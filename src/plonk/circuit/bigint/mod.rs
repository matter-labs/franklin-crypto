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

// This is a case for no lookup tables that constraints 8 bits per gate
pub fn create_range_constraint_chain<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS, 
    el: &AllocatedNum<E>, 
    num_bits: usize
) -> Result<Vec<AllocatedNum<E>>, SynthesisError> {
    let num_elements = num_bits / 4;
    let mut result = vec![];
    for i in 0..num_elements {
        let a = AllocatedNum::alloc(
            cs, 
            || {
                Ok(E::Fr::from_str(&i.to_string()).unwrap())
            }
        )?;

        result.push(a);
    }

    Ok(result)
}