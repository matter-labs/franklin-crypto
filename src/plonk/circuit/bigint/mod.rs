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
    PlonkConstraintSystemParams
};

use crate::circuit::Assignment;

use super::allocated_num::AllocatedNum;

// while it's being worked on in another branch we pretend that it exists

pub trait U16RangeConstraintinSystem<E: Engine>: ConstraintSystem<E> {
    fn constraint_u16(&mut self, var: Variable) -> Result<(), SynthesisError>;
}

use crate::bellman::plonk::better_better_cs::cs::{
    TrivialAssembly, 
    PlonkCsWidth4WithNextStepParams,
};

impl<E: Engine, P: PlonkConstraintSystemParams<E>, MG: MainGateEquation> U16RangeConstraintinSystem<E> for TrivialAssembly<E, P, MG> {
    fn constraint_u16(&mut self, var: Variable) -> Result<(), SynthesisError> {
        assert!(P::STATE_WIDTH == 4);
        assert!(P::CAN_ACCESS_NEXT_TRACE_STEP == true);
        // dummy implementation
        let mut term = MainGateTerm::<E>::new();
        let var_term = ArithmeticTerm::from_variable_and_coeff(var, E::Fr::zero());
        term.add_assign(var_term);

        self.allocate_main_gate(term)
    }
}

pub mod bigint;
pub mod field;

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
        assert!(t.bits() <= num_bits);
    }
    let num_elements = num_bits / 2;
    let slices: Vec<Option<E::Fr>> = if let Some(v) = el.get_value() {
        split_into_accululating_slices(&v, 2, num_elements).into_iter().map(|el| Some(el)).collect()
    } else {
        vec![None; num_elements]
    };
    
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

    let num_gates = num_bits / 8;

    // TODO: add using custom gate
    for _ in 0..num_gates {
        cs.allocate_main_gate(MainGateTerm::<E>::new())?;
    }

    RANGE_GATES_COUNTER.fetch_add(num_gates, Ordering::SeqCst);

    Ok(result)
}