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
};


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

#[derive(Clone, Debug, Hash)]
pub struct Rescue5CustomGate(pub [LinearCombinationOfTerms; 3]);

impl GateEquationInternal for Rescue5CustomGate {
    fn degree(&self) -> usize {
        2
    }

    fn num_constraints(&self) -> usize {
        3
    }

    fn get_constraint(&self) -> &LinearCombinationOfTerms {
        unreachable!("must not try to access single constraint of Rescue alpha = 5 gate");
    }

    fn get_constraints(&self) -> &[LinearCombinationOfTerms] {
        &self.0[..]
    }
}

impl GateEquation for Rescue5CustomGate {
    const HAS_NONTRIVIAL_CONSTANTS: bool = false;
    const NUM_CONSTANTS: usize = 6;
    // Rescue5CustomGate is NOT generic, so this is fine
    // and safe since it's sync!
    fn static_description() -> &'static Self {
        static mut VALUE: Option<Rescue5CustomGate> = None;
        static INIT: std::sync::Once = std::sync::Once::new();

        unsafe {
            INIT.call_once(||{
                VALUE = Some(Rescue5CustomGate::default());
            });

            VALUE.as_ref().unwrap()
        }
    }

    fn output_constant_coefficients<E: Engine>() -> Vec<E::Fr> {
        vec![]
    }
}


impl std::default::Default for Rescue5CustomGate {
    fn default() -> Self {
        Self::get_equation()
    }
}

impl Rescue5CustomGate {
    pub fn get_equation() -> Self {
        let mut term_square: Vec<PolynomialMultiplicativeTerm> = Vec::with_capacity(2);
        // constant
        term_square.push(
            PolynomialMultiplicativeTerm(
                Coefficient::PlusOne,
                vec![
                    PolynomialInConstraint::VariablesPolynomial(0, TimeDilation(0)),
                    PolynomialInConstraint::VariablesPolynomial(0, TimeDilation(0))
                ]
            )
        );

        term_square.push(
            PolynomialMultiplicativeTerm(
                Coefficient::MinusOne,
                vec![
                    PolynomialInConstraint::VariablesPolynomial(1, TimeDilation(0))
                ]
            )
        );

        let mut term_quad: Vec<PolynomialMultiplicativeTerm> = Vec::with_capacity(2);
        // constant
        term_quad.push(
            PolynomialMultiplicativeTerm(
                Coefficient::PlusOne,
                vec![
                    PolynomialInConstraint::VariablesPolynomial(1, TimeDilation(0)),
                    PolynomialInConstraint::VariablesPolynomial(1, TimeDilation(0))
                ]
            )
        );

        term_quad.push(
            PolynomialMultiplicativeTerm(
                Coefficient::MinusOne,
                vec![
                    PolynomialInConstraint::VariablesPolynomial(2, TimeDilation(0))
                ]
            )
        );

        let mut term_fifth: Vec<PolynomialMultiplicativeTerm> = Vec::with_capacity(2);
        // constant
        term_fifth.push(
            PolynomialMultiplicativeTerm(
                Coefficient::PlusOne,
                vec![
                    PolynomialInConstraint::VariablesPolynomial(0, TimeDilation(0)),
                    PolynomialInConstraint::VariablesPolynomial(2, TimeDilation(0))
                ]
            )
        );

        term_fifth.push(
            PolynomialMultiplicativeTerm(
                Coefficient::MinusOne,
                vec![
                    PolynomialInConstraint::VariablesPolynomial(3, TimeDilation(0))
                ]
            )
        );

        Self([
            LinearCombinationOfTerms(term_square),
            LinearCombinationOfTerms(term_quad),
            LinearCombinationOfTerms(term_fifth)])
    }
}

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
        Rescue5CustomGate::static_description(), 
        &[], 
        &[el.get_variable(), squared.get_variable(), quad.get_variable(), fifth.get_variable()], 
        &[]
    )?;

    Ok(fifth)
}

