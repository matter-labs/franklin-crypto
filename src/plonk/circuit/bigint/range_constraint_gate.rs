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

#[derive(Clone, Debug, Hash, Default)]
pub struct TwoBitDecompositionRangecheckCustomGate;

impl<E: Engine> GateInternal<E> for TwoBitDecompositionRangecheckCustomGate {
    fn name(&self) -> &'static str {
        "Two bit decomposition gate for width 4"
    }
    fn can_include_public_inputs(&self) -> bool {
        false
    }

    fn put_public_inputs_into_selector_id(&self) -> Option<usize> {
        None
    }

    fn degree(&self) -> usize {
        4
    }

    fn all_queried_polynomials(&self) -> Vec<PolynomialInConstraint> {
        vec![
            PolynomialInConstraint::VariablesPolynomial(0, TimeDilation(0)),
            PolynomialInConstraint::VariablesPolynomial(1, TimeDilation(0)),
            PolynomialInConstraint::VariablesPolynomial(2, TimeDilation(0)),
            PolynomialInConstraint::VariablesPolynomial(3, TimeDilation(0)),
            PolynomialInConstraint::VariablesPolynomial(3, TimeDilation(1)),
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
        4
    }

    fn verify_on_row(&self, row: usize, poly_storage: &AssembledPolynomialStorage<E>, last_row: bool) -> E::Fr {
        assert!(last_row == false, "can not be applied at the last row");
        let a_value = poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(0), row);
        let b_value = poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(1), row);
        let c_value = poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(2), row);
        let d_value = poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(3), row);
        let d_next_value = poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(3), row+1);

        let one = E::Fr::one();
        let mut two = one;
        two.double();
        let mut three = two;
        three.add_assign(&one);
        let mut four = two;
        four.double();

        for (high, high_and_low) in [
            (d_value, c_value),
            (c_value, b_value),
            (b_value, a_value),
            (a_value, d_next_value),
        ].iter() {
            let mut shifted_high = *high;
            shifted_high.mul_assign(&four);

            let mut low = *high_and_low;
            low.sub_assign(&shifted_high);

            let mut total = low;
            
            let mut tmp = low;
            tmp.sub_assign(&one);
            total.mul_assign(&tmp);

            let mut tmp = low;
            tmp.sub_assign(&two);
            total.mul_assign(&tmp);

            let mut tmp = low;
            tmp.sub_assign(&three);
            total.mul_assign(&tmp);

            if !total.is_zero() {
                return total;
            }
        }

        E::Fr::zero()
    }

    fn contribute_into_quotient(
        &self, 
        poly_storage: &AssembledPolynomialStorage<E>,
        challenges: &[E::Fr],
        lde_factor: usize,
    ) -> Result<Polynomial<E::Fr, Values>, SynthesisError> {
        assert_eq!(challenges.len(), 4);
        unimplemented!()
    }
}

impl<E: Engine> Gate<E> for TwoBitDecompositionRangecheckCustomGate {}
