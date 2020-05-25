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
    PolyIdentifier,
    AssembledPolynomialStorage,
};

use crate::bellman::plonk::polynomials::*;

use crate::circuit::{
    Assignment
};

use super::allocated_num::{
    AllocatedNum
};

use super::linear_combination::{
    LinearCombination
};

use crate::rescue::*;

#[derive(Clone, Debug, Hash, Default)]
pub struct Rescue5CustomGate;

impl<E: Engine> GateInternal<E> for Rescue5CustomGate {
    fn name(&self) -> &'static str {
        "Alpha=5 custom gate for Rescue/Poseidon"
    }

    fn degree(&self) -> usize {
        2
    }

    fn can_include_public_inputs(&self) -> bool {
        false
    }

    fn all_queried_polynomials(&self) -> Vec<PolynomialInConstraint> {
        vec![
            PolynomialInConstraint::VariablesPolynomial(0, TimeDilation(0)),
            PolynomialInConstraint::VariablesPolynomial(1, TimeDilation(0)),
            PolynomialInConstraint::VariablesPolynomial(2, TimeDilation(0)),
            PolynomialInConstraint::VariablesPolynomial(3, TimeDilation(0)),
        ]
    }

    fn setup_polynomials(&self) -> Vec<PolyIdentifier> {
        vec![
        ]
    }

    fn variable_polynomials(&self) -> Vec<PolyIdentifier> {
        vec![
            PolyIdentifier::VariablesPolynomial(0),
            PolyIdentifier::VariablesPolynomial(1),
            PolyIdentifier::VariablesPolynomial(2),
            PolyIdentifier::VariablesPolynomial(3),
        ]
    }

    fn benefits_from_linearization(&self) -> bool {
        false
    }

    fn linearizes_over(&self) -> Vec<PolyIdentifier> {
        vec![
        ]
    }

    fn needs_opened_for_linearization(&self) -> Vec<PolynomialInConstraint> {
        vec![
        ]
    }

    fn num_quotient_terms(&self) -> usize {
        3
    }

    fn verify_on_row(&self, row: usize, poly_storage: &AssembledPolynomialStorage<E>, last_row: bool) -> E::Fr {
        let a_value = poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(0), row);
        let b_value = poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(1), row);
        let c_value = poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(2), row);
        let d_value = poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(3), row);
        
        let mut tmp = a_value;
        tmp.square();
        tmp.sub_assign(&b_value);

        if tmp.is_zero() == false {
            return tmp;
        }

        let mut tmp = b_value;
        tmp.square();
        tmp.sub_assign(&c_value);

        if tmp.is_zero() == false {
            return tmp;
        }

        let mut tmp = c_value;
        tmp.mul_assign(&a_value);
        tmp.sub_assign(&d_value);

        tmp
    }

    fn contribute_into_quotient(
        &self, 
        poly_storage: &AssembledPolynomialStorage<E>,
        challenges: &[E::Fr],
        lde_factor: usize,
    ) -> Result<Polynomial<E::Fr, Values>, SynthesisError> {
        unimplemented!()
    }

    fn put_public_inputs_into_selector_id(&self) -> Option<usize> {
        None
    }
}

impl<E: Engine> Gate<E> for Rescue5CustomGate {}

pub fn apply_5th_power<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    el: &AllocatedNum<E>,
    existing_5th: Option<AllocatedNum<E>>,
) -> Result<AllocatedNum<E>, SynthesisError> {

    let squared = AllocatedNum::alloc(
        cs, 
        || {
            let mut val = *el.get_value().get()?;
            val.square();

            Ok(val)
        }
    )?;

    let quad = AllocatedNum::alloc(
        cs, 
        || {
            let mut val = *squared.get_value().get()?;
            val.square();

            Ok(val)
        }
    )?;

    let fifth = if let Some(f) = existing_5th {
        f
    } else {
        AllocatedNum::alloc(
            cs, 
            || {
                let mut val = *quad.get_value().get()?;
                val.mul_assign(el.get_value().get()?);

                Ok(val)
            }
        )?
    };

    let one = E::Fr::one();
    let mut minus_one = one;
    minus_one.negate();

    // we take a value and make 5th power from it
    cs.new_single_gate_for_trace_step(
        &Rescue5CustomGate::default(), 
        &[], 
        &[el.get_variable(), squared.get_variable(), quad.get_variable(), fifth.get_variable()], 
        &[]
    )?;

    Ok(fifth)
}

