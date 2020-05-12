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
    Width4MainGateWithDNextEquation,
    MainGateEquation,
    GateEquationInternal,
    GateEquation,
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
// pub mod range_constraint_gate;

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
    el: &AllocatedNum<E>, 
    num_bits: usize
) -> Result<Vec<AllocatedNum<E>>, SynthesisError> {
    if let Some(v) = el.get_value() {
        let t = self::bigint::fe_to_biguint(&v);
        assert!(t.bits() as usize <= num_bits, "value is {} that is {} bits, while expected {} bits", t.to_str_radix(16), t.bits(), num_bits);
    }
    let num_elements = num_bits / 2;
    let mut slices: Vec<Option<E::Fr>> = if let Some(v) = el.get_value() {
        split_into_bit_constraint_slices(&v, 2, num_elements).into_iter().map(|el| Some(el)).collect()
    } else {
        vec![None; num_elements]
    };

    let _ = slices.pop().unwrap();
    
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

    result.push(el.clone());

    let num_gates = num_bits / 8 + 1;

    // TODO: add using custom gate
    for _ in 0..num_gates {
        cs.allocate_main_gate(MainGateTerm::<E>::new())?;
    }

    RANGE_GATES_COUNTER.fetch_add(num_gates, Ordering::SeqCst);

    Ok(result)
}