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

use super::allocated_num::AllocatedNum;

pub mod bigint;
pub mod field;
pub mod range_constraint_gate;

use self::range_constraint_gate::TwoBitDecompositionRangecheckCustomGate;

// dummy for now, will address later based on either lookup/range check or trivial
// single bit / two bit decompositions
pub fn constraint_num_bits<E: Engine, CS: ConstraintSystem<E>>(cs: &mut CS, var: Variable, num_bits: usize) -> Result<(), SynthesisError> {
    Ok(())
}

fn split_into_slices<F: PrimeField>(
    el: &F,
    slice_width: usize,
    num_slices: usize
) -> Vec<F> {
    let mut repr = el.into_repr();
    let mut slices = Vec::with_capacity(num_slices);
    let mask = (1u64 << slice_width) - 1u64;
    for _ in 0..num_slices {
        let slice = repr.as_ref()[0] & mask;

        let mut r = F::Repr::default();
        r.as_mut()[0] = slice;

        let slice = F::from_repr(r).unwrap();
        slices.push(slice);

        repr.shr(slice_width as u32);
    }

    slices
}

fn split_into_accululating_slices<F: PrimeField>(
    el: &F,
    slice_width: usize,
    num_slices: usize
) -> Vec<F> {
    let bases = split_into_slices(el, slice_width, num_slices);
    let mut slices = Vec::with_capacity(num_slices);
    let mut accum = F::zero();
    let mut base = F::one();
    for _ in 0..slice_width {
        base.double();
    }
    let mut factor = F::one();
    for s in bases.into_iter() {
        let mut tmp = s;
        tmp.mul_assign(&factor);
        accum.add_assign(&tmp);
        slices.push(accum);

        factor.mul_assign(&base);
    }

    slices
}

fn split_into_bit_constraint_slices<F: PrimeField>(
    el: &F,
    slice_width: usize,
    num_slices: usize
) -> Vec<F> {
    // gate accumulates values a bit differently: each time it shift previous slice by X bits
    // and adds a new chunk into lowest bits, and then constraints the difference
    let bases = split_into_slices(el, slice_width, num_slices);
    let mut slices = Vec::with_capacity(num_slices);
    let mut accum = F::zero();
    let mut base = F::one();
    for _ in 0..slice_width {
        base.double();
    }
    for s in bases.into_iter().rev() {
        accum.mul_assign(&base); // shift existing accumulator
        accum.add_assign(&s); // add into lowest bits

        slices.push(accum);
    }

    slices
}



use std::sync::atomic::{AtomicUsize, Ordering};

pub(crate) static RANGE_GATES_COUNTER: AtomicUsize = AtomicUsize::new(0);

// This is a case for no lookup tables that constraints 8 bits per gate
pub fn create_range_constraint_chain<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS, 
    to_constraint: &AllocatedNum<E>, 
    num_bits: usize
) -> Result<Vec<AllocatedNum<E>>, SynthesisError> {
    assert!(num_bits > 0);
    assert!(num_bits & 1 == 0);
    assert_eq!(CS::Params::STATE_WIDTH, 4, "this only works for a state of width 4 for now");
    if let Some(v) = to_constraint.get_value() {
        let t = self::bigint::fe_to_biguint(&v);
        assert!(t.bits() as usize <= num_bits, "value is {} that is {} bits, while expected {} bits", t.to_str_radix(16), t.bits(), num_bits);
    }
    let num_elements = num_bits / 2;
    let mut slices: Vec<Option<E::Fr>> = if let Some(v) = to_constraint.get_value() {
        split_into_bit_constraint_slices(&v, 2, num_elements).into_iter().map(|el| Some(el)).collect()
    } else {
        vec![None; num_elements]
    };

    let last_val = slices.pop().unwrap();
    if let Some(last_val) = last_val {
        if let Some(v) = to_constraint.get_value() {
            assert_eq!(last_val, v);
        }
    }
    
    let mut result = vec![];
    for v in slices.into_iter() {
        let a = AllocatedNum::alloc(
            cs, 
            || {
                Ok(*v.get()?)
            }
        )?;

        result.push(a);
    }

    result.push(to_constraint.clone());

    let mut num_gates = num_bits / 8;
    if num_gates % 8 != 0 {
        num_gates += 1;
    }

    let mut raw_variables = Vec::with_capacity(result.len() + 1);
    raw_variables.push(cs.get_explicit_zero()?); // we start at D(x) with 0
    for el in result.iter() {
        raw_variables.push(el.get_variable());
    }

    if raw_variables.len() % 4 != 1 {
        let to_add = (5 - (raw_variables.len() % 4)) % 4;

        let mut four = E::Fr::one();
        four.double();
        four.double();

        let four = Some(four);

        use crate::circuit::SomeField;

        let mut previous_value = to_constraint.get_value();

        for _ in 0..to_add {
            let new_value = previous_value.mul(&four);
            let padding = cs.alloc(
                || {
                    Ok(*new_value.get()?)
                }
            )?;

            raw_variables.push(padding);

            previous_value = new_value;
        }
    }

    assert_eq!(raw_variables.len() % 4, 1, "variables len = {}", raw_variables.len());

    let mut rows = raw_variables.chunks_exact(4);

    let gate = TwoBitDecompositionRangecheckCustomGate::default();

    for row in &mut rows {
        let mut row = row.to_vec();
        row.reverse();
        cs.new_single_gate_for_trace_step(
            &gate, 
            &[], 
            &row, 
            &[]
        )?;
    }

    let last = rows.remainder();
    assert!(last.len() == 1);

    let last = last[0];

    let dummy = CS::get_dummy_variable();

    // cause we touch D_Next place an empty gate to the next row

    let (mut variables, coeffs) = CS::MainGate::format_term(MainGateTerm::new(), dummy)?;
    *variables.last_mut().unwrap() = last;

    cs.new_single_gate_for_trace_step(
        &CS::MainGate::default(), 
        &coeffs, 
        &variables, 
        &[]
    )?;

    RANGE_GATES_COUNTER.fetch_add(num_gates+1, Ordering::SeqCst);

    Ok(result)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RangeConstraintInfo {
    pub minimal_multiple: usize,
    pub optimal_multiple: usize,
    pub multiples_per_gate: usize,
}

// pub fn get_range_constraint_info<E: Engine, CS: ConstraintSystem<E>>(cs: &CS) -> RangeConstraintInfo {
//     const MULTIAPPLICATION_TABLE_NAME: &'static str = "Range check table";
//     const SINGLE_APPLICATION_TABLE_NAME: &'static str = "Range check table for a single column";

//     if let Ok(multi) = cs.get_multitable(MULTIAPPLICATION_TABLE_NAME) {
//         let width = crate::log2_floor(multi.size());
//         let multiples = multi.applies_over().len();
//         assert!(multiples <= 3);

//         return RangeConstraintInfo {
//             minimal_multiple: width as usize,
//             optimal_multiple: (width as usize) * multiples,
//             multiples_per_gate: multiples,
//         };
//     }

//     if let Ok(single) = cs.get_table(SINGLE_APPLICATION_TABLE_NAME) {
//         let width = crate::log2_floor(single.size());

//         return RangeConstraintInfo {
//             minimal_multiple: width as usize,
//             optimal_multiple: width as usize,
//             multiples_per_gate: 1,
//         };
//     }

//     if CS::Params::STATE_WIDTH == 4 && CS::Params::HAS_CUSTOM_GATES {
//         return RangeConstraintInfo {
//             minimal_multiple: 2,
//             optimal_multiple: 8,
//             multiples_per_gate: 4,
//         };
//     }

//     return RangeConstraintInfo {
//         minimal_multiple: 1,
//         optimal_multiple: 1,
//         multiples_per_gate: 1,
//     };
// }