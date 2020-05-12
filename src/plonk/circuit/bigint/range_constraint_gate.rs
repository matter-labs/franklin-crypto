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

#[derive(Clone, Debug, Hash)]
pub struct TwoBitDecompositionRangecheckCustomGate(pub [LinearCombinationOfTerms; 1]);

impl GateEquationInternal for TwoBitDecompositionRangecheckCustomGate {
    fn can_include_public_inputs(&self) -> bool {
        false
    }

    fn put_public_inputs_into_selector_id(&self) -> Option<usize> {
        None
    }

    fn degree(&self) -> usize {
        4
    }

    fn num_constraints(&self) -> usize {
        4
    }

    fn get_constraint(&self) -> &LinearCombinationOfTerms {
        unreachable!("must not try to access single constraint of range check gate");
    }

    fn get_constraints(&self) -> &[LinearCombinationOfTerms] {
        &self.0[..]
    }
}

impl GateEquation for TwoBitDecompositionRangecheckCustomGate {
    const HAS_NONTRIVIAL_CONSTANTS: bool = true;
    const NUM_CONSTANTS: usize = 3;
    // Rescue5CustomGate is NOT generic, so this is fine
    // and safe since it's sync!
    fn static_description() -> &'static Self {
        static mut VALUE: Option<TwoBitDecompositionRangecheckCustomGate> = None;
        static INIT: std::sync::Once = std::sync::Once::new();

        unsafe {
            INIT.call_once(||{
                VALUE = Some(TwoBitDecompositionRangecheckCustomGate::default());
            });

            VALUE.as_ref().unwrap()
        }
    }

    fn output_constant_coefficients<E: Engine>() -> Vec<E::Fr> {
        vec![]
    }
}


impl std::default::Default for TwoBitDecompositionRangecheckCustomGate {
    fn default() -> Self {
        Self::get_equation()
    }
}

impl TwoBitDecompositionRangecheckCustomGate {
    pub fn get_equation() -> Self {
        // For each difference of pairs
        // P(x)*(P(x) - 1)*(P(x) - 2)*(P(x) - 3) -> P * (P-1) * (P^2 - 5P + 6) = P*(P^3 - 5P^2 + 6P - P^2 + 5P - 6) =
        // P * (P^3 - 6P^2 + 11P - 6) = P^4 - 6*P^3 + 11*P^2 - 6P
        let mut term_square: Vec<PolynomialMultiplicativeTerm> = Vec::with_capacity(4);
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

