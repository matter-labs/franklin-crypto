use crate::bellman::pairing::{
    Engine,
};

use crate::bellman::pairing::ff::{
    Field,
    PrimeField,
    PrimeFieldRepr,
    BitIterator
};

use crate::bellman::{
    SynthesisError,
};

use crate::bellman::plonk::better_better_cs::cs::{
    Variable, 
    ConstraintSystem,
    ArithmeticTerm,
    MainGateTerm,
    Width4MainGateWithDNext,
    MainGate,
    GateInternal,
    Gate,
    LinearCombinationOfTerms,
    PolynomialMultiplicativeTerm,
    PolynomialInConstraint,
    TimeDilation,
    Coefficient,
    PlonkConstraintSystemParams,
    PlonkCsWidth4WithNextStepParams,
    TrivialAssembly
};

use crate::circuit::Assignment;
use super::*;
use super::bigint::*;

use crate::plonk::circuit::allocated_num::{AllocatedNum, Num};
use crate::plonk::circuit::simple_term::{Term};
use crate::plonk::circuit::linear_combination::LinearCombination;

use std::sync::Arc;

// enforces that this value is either `num_bits` long or a little longer 
// up to a single range constraint width from the table
pub fn enforce_using_single_column_table<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS, 
    to_constraint: &AllocatedNum<E>, 
    num_bits: usize
) -> Result<(), SynthesisError> {
    let strategies = get_range_constraint_info(&*cs);
    assert_eq!(CS::Params::STATE_WIDTH, 4);
    assert!(strategies.len() > 0);
    assert!(strategies[0].strategy == RangeConstraintStrategy::SingleTableInvocation);

    let width_per_gate = strategies[0].optimal_multiple;
    let minimal_per_gate = strategies[0].minimal_multiple;
    let linear_terms_used = strategies[0].linear_terms_used;

    assert_eq!(linear_terms_used, 3);
    assert_eq!(width_per_gate, minimal_per_gate);

    if num_bits < width_per_gate {
        return enforce_shorter_range_into_into_single_gate(
            cs,
            to_constraint,
            num_bits
        );
    }

    if num_bits == width_per_gate {
        return enforce_range_into_into_single_gate(
            cs,
            to_constraint,
            num_bits
        );
    }

    // we do two things simultaneously:
    // - arithmetic constraint like 2^k * a + d - d_next = 0
    // - range constraint that a has width W

    let explicit_zero_var = cs.get_explicit_zero()?;
    let dummy_var = CS::get_dummy_variable();

    let mut next_term_range = CS::MainGate::range_of_next_step_linear_terms();
    assert_eq!(next_term_range.len(), 1, "for now works only if only one variable is accessible on the next step");

    let next_step_coeff_idx = next_term_range.next().expect("must give at least one index");

    let mut minus_one = E::Fr::one();
    minus_one.negate();

    let mut shift = E::Fr::one();
    for _ in 0..width_per_gate {
        shift.double();
    }

    let mut current_term_coeff = E::Fr::one();

    let mut num_gates_for_coarse_constraint = num_bits / width_per_gate;
    let remainder_bits = num_bits % width_per_gate;
    if remainder_bits != 0 {
        num_gates_for_coarse_constraint += 1;
    }
    let num_slices = num_gates_for_coarse_constraint;

    let slices = split_some_into_slices(to_constraint.get_value(), width_per_gate, num_slices);

    let mut it = slices.into_iter();

    use crate::circuit::SomeField;

    let mut next_step_variable_from_previous_gate: Option<AllocatedNum<E>> = None;
    let mut next_step_value = None;
    let mut last_allocated_var = None;

    let table = cs.get_table(RANGE_CHECK_SINGLE_APPLICATION_TABLE_NAME)?;

    for full_gate_idx in 0..num_gates_for_coarse_constraint {
        if next_step_value.is_none() {
            next_step_value = Some(E::Fr::zero());
        }

        let mut term = MainGateTerm::<E>::new();
        let value = it.next().unwrap();
        let chunk_allocated = AllocatedNum::alloc(cs, || {
            Ok(*value.get()?)
        })?;
        last_allocated_var = Some(chunk_allocated.clone());
        let scaled = value.mul(&Some(current_term_coeff));
        next_step_value = next_step_value.add(&scaled);

        let next_step_allocated = AllocatedNum::alloc(cs, || {
            Ok(*next_step_value.get()?)
        })?;

        // a * 2^k
        term.add_assign(ArithmeticTerm::from_variable_and_coeff(chunk_allocated.get_variable(), current_term_coeff));
        current_term_coeff.mul_assign(&shift);

        // add padding into B/C polys
        for _ in 1..linear_terms_used {
            term.add_assign_allowing_duplicates(ArithmeticTerm::from_variable_and_coeff(explicit_zero_var, E::Fr::zero()));
        }

        if let Some(from_previous) = next_step_variable_from_previous_gate.take() {
            term.add_assign(ArithmeticTerm::from_variable(from_previous.get_variable()));
        } else {
            term.add_assign(ArithmeticTerm::from_variable(explicit_zero_var));
        }

        // format taking into account the duplicates exist
        let (variables, mut coeffs) = CS::MainGate::format_linear_term_with_duplicates(term, dummy_var)?;
        coeffs[next_step_coeff_idx] = minus_one;
        
        next_step_variable_from_previous_gate = Some(next_step_allocated.clone());

        cs.begin_gates_batch_for_step()?;

        cs.new_gate_in_batch(
            &CS::MainGate::default(), 
            &coeffs, 
            &variables, 
            &[]
        )?;

        cs.apply_single_lookup_gate(&variables[0..linear_terms_used], Arc::clone(&table))?;

        cs.end_gates_batch_for_step()?;
    }

    // add one gate to utilize D_next 
    let final_val = next_step_variable_from_previous_gate.unwrap();

    let (mut vars, coeffs) = CS::MainGate::format_term(MainGateTerm::<E>::new(), dummy_var)?;

    *vars.last_mut().unwrap() = final_val.get_variable();

    cs.new_single_gate_for_trace_step(
        &CS::MainGate::default(), 
        &coeffs, 
        &vars,
        &[]
    )?;

    if remainder_bits != 0 {
        // constraint the last segment
        let to_constraint = last_allocated_var.unwrap();
        enforce_shorter_range_into_into_single_gate(
            cs,
            &to_constraint,
            remainder_bits
        )?;
    }
    
    Ok(())
}


// enforces that this value is either `num_bits` long or a little longer 
// up to a single range constraint width from the table
fn enforce_shorter_range_into_into_single_gate<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS, 
    to_constraint: &AllocatedNum<E>, 
    num_bits: usize
) -> Result<(), SynthesisError> {
    let strategies = get_range_constraint_info(&*cs);
    assert_eq!(CS::Params::STATE_WIDTH, 4);
    assert!(strategies.len() > 0);
    assert!(strategies[0].strategy == RangeConstraintStrategy::SingleTableInvocation);

    let width_per_gate = strategies[0].optimal_multiple;
    let minimal_per_gate = strategies[0].minimal_multiple;
    let linear_terms_used = strategies[0].linear_terms_used;

    assert_eq!(linear_terms_used, 3);
    assert!(num_bits < width_per_gate);

    // we do two things simultaneously:
    // - arithmetic constraint a + 2^k * b + 2^2k * c - d = 0
    // - range constraint that a, b, c have width W

    let explicit_zero_var = cs.get_explicit_zero()?;
    let dummy_var = CS::get_dummy_variable();

    let mut shift = E::Fr::one();
    for _ in 0..(width_per_gate-num_bits) {
        shift.double();
    }

    use super::bigint::make_multiple;

    use crate::circuit::SomeField;

    let mut term = MainGateTerm::<E>::new();
    let value = to_constraint.get_value().mul(&Some(shift));
    let allocated = AllocatedNum::alloc(cs, || {
        Ok(*value.get()?)
    })?;

    term.add_assign(ArithmeticTerm::from_variable(allocated.get_variable()));

    for _ in 1..linear_terms_used {
        term.add_assign_allowing_duplicates(ArithmeticTerm::from_variable_and_coeff(explicit_zero_var, E::Fr::zero()));
    }

    term.sub_assign(ArithmeticTerm::from_variable_and_coeff(to_constraint.get_variable(), shift));

    let (variables, coeffs) = CS::MainGate::format_linear_term_with_duplicates(term, dummy_var)?;

    cs.begin_gates_batch_for_step()?;

    cs.new_gate_in_batch(
        &CS::MainGate::default(), 
        &coeffs, 
        &variables, 
        &[]
    )?;

    let table = cs.get_table(RANGE_CHECK_SINGLE_APPLICATION_TABLE_NAME)?;

    cs.apply_single_lookup_gate(&variables[0..linear_terms_used], table)?;

    cs.end_gates_batch_for_step()?;
    
    Ok(())
}


// enforces that this value is either `num_bits` long or a little longer 
// up to a single range constraint width from the table
fn enforce_range_into_into_single_gate<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS, 
    to_constraint: &AllocatedNum<E>, 
    num_bits: usize
) -> Result<(), SynthesisError> {
    let strategies = get_range_constraint_info(&*cs);
    assert_eq!(CS::Params::STATE_WIDTH, 4);
    assert!(strategies.len() > 0);
    assert!(strategies[0].strategy == RangeConstraintStrategy::SingleTableInvocation);

    let width_per_gate = strategies[0].optimal_multiple;
    let minimal_per_gate = strategies[0].minimal_multiple;
    let linear_terms_used = strategies[0].linear_terms_used;

    assert_eq!(linear_terms_used, 3);
    assert_eq!(num_bits, width_per_gate);

    // we do two things simultaneously:
    // - arithmetic constraint a + 2^k * b + 2^2k * c - d = 0
    // - range constraint that a, b, c have width W

    let explicit_zero_var = cs.get_explicit_zero()?;
    let dummy_var = CS::get_dummy_variable();

    let mut term = MainGateTerm::<E>::new();
    term.add_assign(ArithmeticTerm::from_variable_and_coeff(to_constraint.get_variable(), E::Fr::zero()));

    // add padding into B/C polys
    for _ in 1..linear_terms_used {
        term.add_assign_allowing_duplicates(ArithmeticTerm::from_variable_and_coeff(explicit_zero_var, E::Fr::zero()));
    }

    // format taking into account the duplicates exist
    let (variables, coeffs) = CS::MainGate::format_linear_term_with_duplicates(term, dummy_var)?;
    let table = cs.get_table(RANGE_CHECK_SINGLE_APPLICATION_TABLE_NAME)?;

    cs.begin_gates_batch_for_step()?;

    cs.new_gate_in_batch(
        &CS::MainGate::default(), 
        &coeffs, 
        &variables, 
        &[]
    )?;

    cs.apply_single_lookup_gate(&variables[0..linear_terms_used], Arc::clone(&table))?;

    cs.end_gates_batch_for_step()?;
    
    Ok(())
}


pub fn adaptively_constraint_multiple_with_single_table<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    terms: &[Term<E>],
    widths: &[usize]
) -> Result<(), SynthesisError> {
    let strategies = get_range_constraint_info(&*cs);
    assert_eq!(CS::Params::STATE_WIDTH, 4);
    assert!(strategies.len() > 0);
    assert!(strategies[0].strategy == RangeConstraintStrategy::SingleTableInvocation);

    let width_per_gate = strategies[0].optimal_multiple;
    let minimal_per_gate = strategies[0].minimal_multiple;
    let linear_terms_used = strategies[0].linear_terms_used;

    assert_eq!(linear_terms_used, 3);

    // first let's go over constants
    // and short constraints

    assert_eq!(terms.len(), widths.len());

    for (t, &w) in terms.iter().zip(widths.iter()) {
        if t.is_constant() {
            let value = t.get_constant_value();
            let value = fe_to_biguint(&value);
            assert!(value.bits() as usize <= w);
        } else {
            if w <= minimal_per_gate {
                let collapsed = t.collapse_into_num(cs)?.get_variable();
                if w < minimal_per_gate {
                    enforce_shorter_range_into_into_single_gate(cs, &collapsed, w)?;
                } else {
                    enforce_range_into_into_single_gate(cs, &collapsed, w)?;
                }
            } else {
                let r = t.collapse_into_num(cs)?.get_variable();
                enforce_using_single_column_table(cs, &r, w)?;
            }
        }
    }

    Ok(())
}