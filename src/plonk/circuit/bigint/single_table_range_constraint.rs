use crate::bellman::pairing::Engine;

use crate::bellman::pairing::ff::{BitIterator, Field, PrimeField, PrimeFieldRepr};

use crate::bellman::SynthesisError;

use crate::bellman::plonk::better_better_cs::cs::{
    ArithmeticTerm, Coefficient, ConstraintSystem, Gate, GateInternal, LinearCombinationOfTerms,
    MainGate, MainGateTerm, PlonkConstraintSystemParams, PlonkCsWidth4WithNextStepParams,
    PolynomialInConstraint, PolynomialMultiplicativeTerm, TimeDilation, TrivialAssembly, Variable,
    Width4MainGateWithDNext,
};

use super::bigint::*;
use super::*;
use crate::plonk::circuit::Assignment;

use crate::plonk::circuit::allocated_num::{AllocatedNum, Num};
use crate::plonk::circuit::linear_combination::LinearCombination;
use crate::plonk::circuit::simple_term::Term;

use std::sync::Arc;

use std::sync::atomic::{AtomicUsize, Ordering};

pub static NUM_RANGE_CHECK_INVOCATIONS: AtomicUsize = AtomicUsize::new(0);
pub static NUM_SHORT_RANGE_CHECK_INVOCATIONS: AtomicUsize = AtomicUsize::new(0);
pub static NUM_GATES_SPENT_ON_RANGE_CHECKS: AtomicUsize = AtomicUsize::new(0);

pub fn reset_stats() {
    NUM_RANGE_CHECK_INVOCATIONS.store(0, Ordering::Relaxed);
    NUM_SHORT_RANGE_CHECK_INVOCATIONS.store(0, Ordering::Relaxed);
    NUM_GATES_SPENT_ON_RANGE_CHECKS.store(0, Ordering::Relaxed);
}

fn increment_invocation_count() {
    NUM_RANGE_CHECK_INVOCATIONS.fetch_add(1, Ordering::SeqCst);
}

fn increment_short_checks_count() {
    NUM_SHORT_RANGE_CHECK_INVOCATIONS.fetch_add(1, Ordering::SeqCst);
}

fn increment_total_gates_count(val: usize) {
    NUM_GATES_SPENT_ON_RANGE_CHECKS.fetch_add(val, Ordering::SeqCst);
}

pub fn print_stats() {
    let total_checks = NUM_RANGE_CHECK_INVOCATIONS.load(Ordering::Relaxed);
    let short_checks = NUM_SHORT_RANGE_CHECK_INVOCATIONS.load(Ordering::Relaxed);
    let total_gates = NUM_GATES_SPENT_ON_RANGE_CHECKS.load(Ordering::Relaxed);

    println!("Has made in total of {} range checks, with {} being short (singe gate) and {} gates in total", total_checks, short_checks, total_gates);
}

// enforces that this value is either `num_bits` long or a little longer
// up to a single range constraint width from the table
pub fn enforce_using_single_column_table_for_shifted_variable<
    E: Engine,
    CS: ConstraintSystem<E>,
>(
    cs: &mut CS,
    to_constraint: &AllocatedNum<E>,
    shift: E::Fr,
    num_bits: usize,
) -> Result<Vec<Num<E>>, SynthesisError> {
    // we ensure that var * shift <= N bits
    let strategies = get_range_constraint_info(&*cs);
    assert_eq!(CS::Params::STATE_WIDTH, 4);
    assert!(strategies.len() > 0);
    assert_eq!(
        strategies[0].strategy,
        RangeConstraintStrategy::SingleTableInvocation
    );

    let width_per_gate = strategies[0].optimal_multiple;
    let minimal_per_gate = strategies[0].minimal_multiple;
    let linear_terms_used = strategies[0].linear_terms_used;

    assert_eq!(linear_terms_used, 3);
    assert_eq!(width_per_gate, minimal_per_gate);

    if num_bits <= width_per_gate {
        let chunk = enforce_shorter_range_into_single_gate_for_shifted_variable(
            cs,
            to_constraint,
            shift,
            num_bits,
        )?;

        return Ok(vec![chunk]);
    }

    increment_invocation_count();

    // initial_d = 2^k * num_to_constraint;
    // we split this initial_d into chunks of equal_length W: [a0, a1, ..., an]
    // 2^W d_next = d - a_i
    // we do two things simultaneously:
    // - arithmetic constraint like d - a_i + d + 2^W d_next = 0
    // - range constraint that a has width W
    // NB: on the last row the arithmetic constraint would be simply:
    // d - a_n = 0

    let dummy_var = CS::get_dummy_variable();
    let range_of_linear_terms = CS::MainGate::range_of_linear_terms();
    let mut next_term_range = CS::MainGate::range_of_next_step_linear_terms();
    assert_eq!(
        next_term_range.len(),
        1,
        "for now works only if only one variable is accessible on the next step"
    );
    let next_step_coeff_idx = next_term_range
        .next()
        .expect("must give at least one index");
    let mut minus_one = E::Fr::one();
    minus_one.negate();

    let mut table_width_shift = E::Fr::one();
    for _ in 0..width_per_gate {
        table_width_shift.double();
    }
    let mut table_width_shift_negated = table_width_shift.clone();
    table_width_shift_negated.negate();
    let table_width_shift_inverse = table_width_shift.inverse().unwrap();

    let mut num_gates_for_coarse_constraint = num_bits / width_per_gate;
    let remainder_bits = num_bits % width_per_gate;
    if remainder_bits != 0 {
        num_gates_for_coarse_constraint += 1;
    }
    let num_slices = num_gates_for_coarse_constraint;

    use crate::plonk::circuit::SomeField;

    let value_to_constraint = to_constraint.get_value().mul(&Some(shift));
    let slices = split_some_into_slices(value_to_constraint, width_per_gate, num_slices);
    let mut it = slices.into_iter().peekable();

    let table = cs.get_table(RANGE_CHECK_SINGLE_APPLICATION_TABLE_NAME)?;
    let mut cur_value = to_constraint.clone();
    let mut coeffs = [minus_one, E::Fr::zero(), E::Fr::zero(), shift];

    let mut chunks = vec![];
    while let Some(slice_fr) = it.next() {
        let d_next_coef = if it.peek().is_some() {
            table_width_shift_negated
        } else {
            E::Fr::zero()
        };

        let slice = AllocatedNum::alloc(cs, || slice_fr.grab())?;
        let vars = [
            slice.get_variable(),
            dummy_var,
            dummy_var,
            cur_value.get_variable(),
        ];
        chunks.push(Num::Variable(slice));

        cs.begin_gates_batch_for_step()?;
        cs.apply_single_lookup_gate(&vars[..table.width()], table.clone())?;

        let gate_term = MainGateTerm::new();
        let (_, mut gate_coefs) = CS::MainGate::format_term(gate_term, dummy_var)?;

        for (idx, coef) in range_of_linear_terms.clone().zip(coeffs.iter()) {
            gate_coefs[idx] = *coef;
        }
        gate_coefs[next_step_coeff_idx] = d_next_coef;

        let mg = CS::MainGate::default();
        cs.new_gate_in_batch(&mg, &gate_coefs, &vars, &[])?;
        cs.end_gates_batch_for_step()?;

        cur_value = if it.peek().is_some() {
            AllocatedNum::alloc(cs, || {
                let mut res = cur_value.get_value().grab()?;
                res.mul_assign(&coeffs.last().unwrap());
                let tmp = slice.get_value().grab()?;
                res.sub_assign(&tmp);
                res.mul_assign(&table_width_shift_inverse);
                Ok(res)
            })?
        } else {
            AllocatedNum::zero(cs)
        };
        *coeffs.last_mut().unwrap() = E::Fr::one();
    }

    increment_total_gates_count(num_gates_for_coarse_constraint + (remainder_bits != 0) as usize);

    Ok(chunks)
}

// enforces that this value is either `num_bits` long or a little longer
// up to a single range constraint width from the table
pub fn enforce_using_single_column_table_for_shifted_variable_optimized<
    E: Engine,
    CS: ConstraintSystem<E>,
>(
    cs: &mut CS,
    to_constraint: &AllocatedNum<E>,
    shift: E::Fr,
    num_bits: usize,
) -> Result<Vec<Num<E>>, SynthesisError> {
    // we ensure that var * shift <= N bits
    let strategies = get_range_constraint_info(&*cs);
    assert_eq!(CS::Params::STATE_WIDTH, 4);
    assert!(strategies.len() > 0);
    assert_eq!(
        strategies[0].strategy,
        RangeConstraintStrategy::SingleTableInvocation
    );

    let width_per_gate = strategies[0].optimal_multiple;
    let minimal_per_gate = strategies[0].minimal_multiple;
    let linear_terms_used = strategies[0].linear_terms_used;

    assert_eq!(linear_terms_used, 3);
    assert_eq!(width_per_gate, minimal_per_gate);

    if num_bits <= width_per_gate {
        let short_enforced = enforce_shorter_range_into_single_gate_for_shifted_variable(
            cs,
            to_constraint,
            shift,
            num_bits,
        )?;

        return Ok(vec![short_enforced]);
    }

    // now check if we can further shift the variable to make it multiple or if it's already a multiple

    let remainder_bits = num_bits % width_per_gate;
    if remainder_bits == 0 {
        return enforce_using_single_column_table_for_shifted_variable_optimized_for_multiple_of_table(cs, to_constraint, shift, num_bits);
    } else {
        if num_bits - remainder_bits + width_per_gate <= E::Fr::CAPACITY as usize {
            // we can shift the variable further to the left
            let mut new_shift = shift;
            for _ in 0..(width_per_gate - remainder_bits) {
                new_shift.double();
            }
            let new_num_bits = num_bits - remainder_bits + width_per_gate;
            return enforce_using_single_column_table_for_shifted_variable_optimized_for_multiple_of_table(cs, to_constraint, new_shift, new_num_bits);
        }
    }

    // otherwise proceed with a pessimistic case when we constraint it first as chunks of larger size first,
    // and then constraint that some chunk is even narrower

    increment_invocation_count();

    // we do two things simultaneously:
    // - place initial variable into -d (or shift initial variable)
    // - make it a * 2^k + d - d_next = 0, this zeroes particular bit ranges
    // - range constraint that a has width W

    let explicit_zero_var = cs.get_explicit_zero()?;
    let dummy_var = CS::get_dummy_variable();

    let mut next_term_range = CS::MainGate::range_of_next_step_linear_terms();
    assert_eq!(
        next_term_range.len(),
        1,
        "for now works only if only one variable is accessible on the next step"
    );

    let next_step_coeff_idx = next_term_range
        .next()
        .expect("must give at least one index");

    let mut minus_one = E::Fr::one();
    minus_one.negate();

    let mut accumulation_shift = E::Fr::one();
    for _ in 0..width_per_gate {
        accumulation_shift.double();
    }

    let mut current_term_coeff = E::Fr::one();

    let mut num_gates_for_coarse_constraint = num_bits / width_per_gate;
    let remainder_bits = num_bits % width_per_gate;
    if remainder_bits != 0 {
        num_gates_for_coarse_constraint += 1;
    }
    let num_slices = num_gates_for_coarse_constraint;

    use crate::plonk::circuit::SomeField;

    let value_to_constraint = to_constraint.get_value().mul(&Some(shift));
    let slices = split_some_into_slices(value_to_constraint, width_per_gate, num_slices);

    let mut it = slices.into_iter();

    let mut next_step_variable_from_previous_gate: Option<AllocatedNum<E>> = None;
    let mut next_step_value = value_to_constraint.mul(&Some(minus_one));
    let mut last_allocated_var = None;

    let table = cs.get_table(RANGE_CHECK_SINGLE_APPLICATION_TABLE_NAME)?;

    let mut chunks = vec![];
    for full_gate_idx in 0..num_gates_for_coarse_constraint {
        let is_last = full_gate_idx == num_gates_for_coarse_constraint - 1;
        if next_step_value.is_none() {
            next_step_value = Some(E::Fr::zero());
        }

        let mut term = MainGateTerm::<E>::new();
        let value = it.next().unwrap();
        let chunk_allocated = AllocatedNum::alloc(cs, || Ok(*value.get()?))?;
        chunks.push(Num::Variable(chunk_allocated));
        last_allocated_var = Some(chunk_allocated.clone());
        let scaled = value.mul(&Some(current_term_coeff));
        next_step_value = next_step_value.add(&scaled);

        let next_step_allocated = AllocatedNum::alloc(cs, || Ok(*next_step_value.get()?))?;

        // a * 2^k
        term.add_assign(ArithmeticTerm::from_variable_and_coeff(
            chunk_allocated.get_variable(),
            current_term_coeff,
        ));
        current_term_coeff.mul_assign(&accumulation_shift);

        // add padding into B/C polys
        for _ in 1..linear_terms_used {
            term.add_assign_allowing_duplicates(ArithmeticTerm::from_variable_and_coeff(
                explicit_zero_var,
                E::Fr::zero(),
            ));
        }

        if let Some(from_previous) = next_step_variable_from_previous_gate.take() {
            if is_last {
            } else {
                // not the first gate and no the last
                term.add_assign(ArithmeticTerm::from_variable(from_previous.get_variable()));
            }
        } else {
            // first gate
            term.sub_assign(ArithmeticTerm::from_variable_and_coeff(
                to_constraint.get_variable(),
                shift,
            ));
        }

        // format taking into account the duplicates exist
        let (variables, mut coeffs) =
            CS::MainGate::format_linear_term_with_duplicates(term, dummy_var)?;
        if is_last {
            coeffs[next_step_coeff_idx] = E::Fr::zero();
        } else {
            coeffs[next_step_coeff_idx] = minus_one;
        }

        next_step_variable_from_previous_gate = Some(next_step_allocated.clone());

        cs.begin_gates_batch_for_step()?;

        cs.new_gate_in_batch(&CS::MainGate::default(), &coeffs, &variables, &[])?;

        cs.apply_single_lookup_gate(&variables[0..linear_terms_used], Arc::clone(&table))?;

        cs.end_gates_batch_for_step()?;
    }

    if remainder_bits != 0 {
        // constraint the last segment
        let to_constraint = last_allocated_var.unwrap();
        let short_enforced =
            enforce_shorter_range_into_single_gate(cs, &to_constraint, remainder_bits)?;

        chunks.push(short_enforced);
    }

    increment_total_gates_count(num_gates_for_coarse_constraint + (remainder_bits != 0) as usize);

    Ok(chunks)
}

/// enforces that variable is range checked and bit width is a multiple of the table
pub fn enforce_using_single_column_table_for_shifted_variable_optimized_for_multiple_of_table<
    E: Engine,
    CS: ConstraintSystem<E>,
>(
    cs: &mut CS,
    to_constraint: &AllocatedNum<E>,
    shift: E::Fr,
    num_bits: usize,
) -> Result<Vec<Num<E>>, SynthesisError> {
    // we ensure that var * shift <= N bits
    let strategies = get_range_constraint_info(&*cs);
    assert_eq!(CS::Params::STATE_WIDTH, 4);
    assert!(strategies.len() > 0);
    assert_eq!(
        strategies[0].strategy,
        RangeConstraintStrategy::SingleTableInvocation
    );

    let width_per_gate = strategies[0].optimal_multiple;
    let minimal_per_gate = strategies[0].minimal_multiple;
    let linear_terms_used = strategies[0].linear_terms_used;

    assert_eq!(linear_terms_used, 3);
    assert_eq!(width_per_gate, minimal_per_gate);

    if num_bits <= width_per_gate {
        unreachable!("should be caught by other functions");
        // return enforce_shorter_range_into_single_gate_for_shifted_variable(
        //     cs,
        //     to_constraint,
        //     shift,
        //     num_bits
        // );
    }

    assert!(num_bits % width_per_gate == 0);

    increment_invocation_count();

    // we do two things simultaneously:
    // - place initial variable into -d (or shift initial variable)
    // - make it a * 2^k + d - d_next = 0, this zeroes particular bit ranges
    // - range constraint that a has width W

    let mut chunks = vec![];

    let explicit_zero_var = cs.get_explicit_zero()?;
    let dummy_var = CS::get_dummy_variable();

    let mut next_term_range = CS::MainGate::range_of_next_step_linear_terms();
    assert_eq!(
        next_term_range.len(),
        1,
        "for now works only if only one variable is accessible on the next step"
    );

    let next_step_coeff_idx = next_term_range
        .next()
        .expect("must give at least one index");

    let mut minus_one = E::Fr::one();
    minus_one.negate();

    let mut accumulation_shift = E::Fr::one();
    for _ in 0..width_per_gate {
        accumulation_shift.double();
    }

    let mut current_term_coeff = E::Fr::one();

    let num_gates_for_coarse_constraint = num_bits / width_per_gate;
    let remainder_bits = num_bits % width_per_gate;
    assert_eq!(remainder_bits, 0);

    let num_slices = num_gates_for_coarse_constraint;

    use crate::plonk::circuit::SomeField;

    let value_to_constraint = to_constraint.get_value().mul(&Some(shift));
    let slices = split_some_into_slices(value_to_constraint, width_per_gate, num_slices);

    let mut it = slices.into_iter();

    let mut next_step_variable_from_previous_gate: Option<AllocatedNum<E>> = None;

    let mut next_step_value = value_to_constraint.mul(&Some(minus_one));

    let table = cs.get_table(RANGE_CHECK_SINGLE_APPLICATION_TABLE_NAME)?;

    for full_gate_idx in 0..num_gates_for_coarse_constraint {
        let is_last = full_gate_idx == num_gates_for_coarse_constraint - 1;

        let mut term = MainGateTerm::<E>::new();
        let value = it.next().unwrap();
        let chunk_allocated = AllocatedNum::alloc(cs, || Ok(*value.get()?))?;
        chunks.push(Num::Variable(chunk_allocated));
        let scaled = value.mul(&Some(current_term_coeff));
        next_step_value = next_step_value.add(&scaled);

        let next_step_allocated = AllocatedNum::alloc(cs, || Ok(*next_step_value.get()?))?;

        // a * 2^k
        term.add_assign(ArithmeticTerm::from_variable_and_coeff(
            chunk_allocated.get_variable(),
            current_term_coeff,
        ));
        current_term_coeff.mul_assign(&accumulation_shift);

        // add padding into B/C polys
        for _ in 1..linear_terms_used {
            term.add_assign_allowing_duplicates(ArithmeticTerm::from_variable_and_coeff(
                explicit_zero_var,
                E::Fr::zero(),
            ));
        }

        if let Some(from_previous) = next_step_variable_from_previous_gate.take() {
            // not the first gate
            term.add_assign(ArithmeticTerm::from_variable(from_previous.get_variable()));
        } else {
            // first gate
            term.sub_assign(ArithmeticTerm::from_variable_and_coeff(
                to_constraint.get_variable(),
                shift,
            ));
        }

        // format taking into account the duplicates exist
        let (variables, mut coeffs) =
            CS::MainGate::format_linear_term_with_duplicates(term, dummy_var)?;
        if is_last {
            coeffs[next_step_coeff_idx] = E::Fr::zero();
        } else {
            coeffs[next_step_coeff_idx] = minus_one;
        }

        next_step_variable_from_previous_gate = Some(next_step_allocated.clone());

        cs.begin_gates_batch_for_step()?;

        cs.new_gate_in_batch(&CS::MainGate::default(), &coeffs, &variables, &[])?;

        cs.apply_single_lookup_gate(&variables[0..linear_terms_used], Arc::clone(&table))?;

        cs.end_gates_batch_for_step()?;
    }

    increment_total_gates_count(num_gates_for_coarse_constraint + (remainder_bits != 0) as usize);

    Ok(chunks)
}

// enforces that this value is either `num_bits` long or a little longer
// up to a single range constraint width from the table
pub fn enforce_using_single_column_table<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    to_constraint: &AllocatedNum<E>,
    num_bits: usize,
) -> Result<Vec<Num<E>>, SynthesisError> {
    enforce_using_single_column_table_for_shifted_variable(
        cs,
        to_constraint,
        E::Fr::one(),
        num_bits,
    )
}

// enforces that this value is either `num_bits` long or a little longer
// up to a single range constraint width from the table
pub fn enforce_using_single_column_table_optimized<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    to_constraint: &AllocatedNum<E>,
    num_bits: usize,
) -> Result<Vec<Num<E>>, SynthesisError> {
    enforce_using_single_column_table_for_shifted_variable_optimized(
        cs,
        to_constraint,
        E::Fr::one(),
        num_bits,
    )
}

// enforces that this value * shift is exactly `num_bits` long
fn enforce_shorter_range_into_single_gate_for_shifted_variable<
    E: Engine,
    CS: ConstraintSystem<E>,
>(
    cs: &mut CS,
    to_constraint: &AllocatedNum<E>,
    shift: E::Fr,
    num_bits: usize,
) -> Result<Num<E>, SynthesisError> {
    // var * shift <= num bits
    increment_invocation_count();
    increment_short_checks_count();
    increment_total_gates_count(1);
    let strategies = get_range_constraint_info(&*cs);
    assert_eq!(CS::Params::STATE_WIDTH, 4);
    assert!(strategies.len() > 0);
    assert!(strategies[0].strategy == RangeConstraintStrategy::SingleTableInvocation);

    let width_per_gate = strategies[0].optimal_multiple;
    let linear_terms_used = strategies[0].linear_terms_used;

    assert_eq!(linear_terms_used, 3);
    assert!(num_bits <= width_per_gate);

    let explicit_zero_var = cs.get_explicit_zero()?;
    let dummy_var = CS::get_dummy_variable();

    let mut shift = shift;
    let mut two = E::Fr::one();
    two.double();
    for _ in 0..(width_per_gate - num_bits) {
        shift.mul_assign(&two);
    }

    use super::bigint::make_multiple;

    use crate::plonk::circuit::SomeField;

    let mut term = MainGateTerm::<E>::new();
    let value = to_constraint.get_value().mul(&Some(shift));
    let allocated = AllocatedNum::alloc(cs, || Ok(*value.get()?))?;

    term.add_assign(ArithmeticTerm::from_variable(allocated.get_variable()));

    for _ in 1..linear_terms_used {
        term.add_assign_allowing_duplicates(ArithmeticTerm::from_variable_and_coeff(
            explicit_zero_var,
            E::Fr::zero(),
        ));
    }

    term.sub_assign(ArithmeticTerm::from_variable_and_coeff(
        to_constraint.get_variable(),
        shift,
    ));

    let (variables, coeffs) = CS::MainGate::format_linear_term_with_duplicates(term, dummy_var)?;

    cs.begin_gates_batch_for_step()?;

    cs.new_gate_in_batch(&CS::MainGate::default(), &coeffs, &variables, &[])?;

    let table = cs.get_table(RANGE_CHECK_SINGLE_APPLICATION_TABLE_NAME)?;

    cs.apply_single_lookup_gate(&variables[0..linear_terms_used], table)?;

    cs.end_gates_batch_for_step()?;

    Ok(Num::Variable(*to_constraint))
}

// enforces that this value is exactly `num_bits` long
fn enforce_shorter_range_into_single_gate<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    to_constraint: &AllocatedNum<E>,
    num_bits: usize,
) -> Result<Num<E>, SynthesisError> {
    enforce_shorter_range_into_single_gate_for_shifted_variable(
        cs,
        to_constraint,
        E::Fr::one(),
        num_bits,
    )
}

// enforces that this value * shift is either `num_bits` long or a little longer
// up to a single range constraint width from the table
fn enforce_range_into_single_gate_for_shifted_variable<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    to_constraint: &AllocatedNum<E>,
    shift: E::Fr,
    num_bits: usize,
) -> Result<Num<E>, SynthesisError> {
    let strategies = get_range_constraint_info(&*cs);
    assert_eq!(CS::Params::STATE_WIDTH, 4);
    assert!(strategies.len() > 0);
    assert!(strategies[0].strategy == RangeConstraintStrategy::SingleTableInvocation);

    let width_per_gate = strategies[0].optimal_multiple;
    let linear_terms_used = strategies[0].linear_terms_used;

    assert_eq!(linear_terms_used, 3);
    assert_eq!(num_bits, width_per_gate);

    enforce_shorter_range_into_single_gate_for_shifted_variable(cs, to_constraint, shift, num_bits)
}

// enforces that this value is either `num_bits` long or a little longer
// up to a single range constraint width from the table
fn enforce_range_into_single_gate<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    to_constraint: &AllocatedNum<E>,
    num_bits: usize,
) -> Result<(), SynthesisError> {
    increment_invocation_count();
    increment_short_checks_count();
    increment_total_gates_count(1);
    let strategies = get_range_constraint_info(&*cs);
    assert_eq!(CS::Params::STATE_WIDTH, 4);
    assert!(strategies.len() > 0);
    assert!(strategies[0].strategy == RangeConstraintStrategy::SingleTableInvocation);

    let width_per_gate = strategies[0].optimal_multiple;
    let linear_terms_used = strategies[0].linear_terms_used;

    assert_eq!(linear_terms_used, 3);
    assert_eq!(num_bits, width_per_gate);

    let explicit_zero_var = cs.get_explicit_zero()?;
    let dummy_var = CS::get_dummy_variable();

    let mut term = MainGateTerm::<E>::new();
    term.add_assign(ArithmeticTerm::from_variable_and_coeff(
        to_constraint.get_variable(),
        E::Fr::zero(),
    ));

    // add padding into B/C polys
    for _ in 1..linear_terms_used {
        term.add_assign_allowing_duplicates(ArithmeticTerm::from_variable_and_coeff(
            explicit_zero_var,
            E::Fr::zero(),
        ));
    }

    // format taking into account the duplicates exist
    let (variables, coeffs) = CS::MainGate::format_linear_term_with_duplicates(term, dummy_var)?;
    let table = cs.get_table(RANGE_CHECK_SINGLE_APPLICATION_TABLE_NAME)?;

    cs.begin_gates_batch_for_step()?;

    cs.new_gate_in_batch(&CS::MainGate::default(), &coeffs, &variables, &[])?;

    cs.apply_single_lookup_gate(&variables[0..linear_terms_used], Arc::clone(&table))?;

    cs.end_gates_batch_for_step()?;

    Ok(())
}

pub fn adaptively_constraint_multiple_with_single_table<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    terms: &[Term<E>],
    widths: &[usize],
) -> Result<(), SynthesisError> {
    let strategies = get_range_constraint_info(&*cs);
    assert_eq!(CS::Params::STATE_WIDTH, 4);
    assert!(strategies.len() > 0);
    assert!(strategies[0].strategy == RangeConstraintStrategy::SingleTableInvocation);

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
                    enforce_shorter_range_into_single_gate(cs, &collapsed, w)?;
                } else {
                    enforce_range_into_single_gate(cs, &collapsed, w)?;
                }
            } else {
                let r = t.collapse_into_num(cs)?.get_variable();
                enforce_using_single_column_table(cs, &r, w)?;
            }
        }
    }

    Ok(())
}
