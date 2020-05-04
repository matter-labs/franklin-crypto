use crate::bellman::pairing::{
    Engine,
    CurveAffine,
    CurveProjective
};

use crate::bellman::pairing::ff::{
    Field,
    PrimeField,
    PrimeFieldRepr,
    BitIterator,
    ScalarEngine
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
    TrivialAssembly,
    PlonkCsWidth4WithNextStepParams,
};

use super::super::allocated_num::{AllocatedNum, Num};
use super::super::linear_combination::LinearCombination;
use super::super::simple_term::Term;
use super::super::boolean::Boolean;

use num_bigint::BigUint;
use num_integer::Integer;

use super::super::bigint::field::*;
use super::super::bigint::bigint::*;

pub struct AffinePoint<'a, E: Engine, G: CurveAffine> where <G as CurveAffine>::Base: PrimeField {
    x: FieldElement<'a, E, G::Base>,
    y: FieldElement<'a, E, G::Base>,
    value: Option<G>,
}

impl<'a, E: Engine, G: CurveAffine> AffinePoint<'a, E, G> where <G as CurveAffine>::Base: PrimeField {
    pub fn alloc<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        value: Option<G>,
        params: &'a RnsParameters<E, G::Base>
    ) -> Result<Self, SynthesisError> {
        let (x, y) = match value {
            Some(v) => {
                assert!(!v.is_zero());
                let (x, y) = v.into_xy_unchecked();

                (Some(x), Some(y))
            },
            None => {
                (None, None)
            }
        };

        let x = FieldElement::new_allocated(
            cs, 
            x, 
            params
        )?;

        let y = FieldElement::new_allocated(
            cs, 
            y, 
            params
        )?;

        let new = Self {
            x,
            y,
            value
        };

        Ok(new)
    }

    pub fn constant(
        value: G,
        params: &'a RnsParameters<E, G::Base>
    ) -> Result<Self, SynthesisError> {
        assert!(!value.is_zero());
        let (x, y) = value.into_xy_unchecked();

        let x = FieldElement::new_constant(
            x,
            params
        )?;

        let y = FieldElement::new_constant(
            y,
            params
        )?;

        let new = Self {
            x,
            y,
            value: Some(value)
        };

        Ok(new)
    }

    pub fn get_value(&self) -> Option<G> {
        self.value
    }

    pub fn add_unequal<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
        other: Self
    ) -> Result<(Self, (Self, Self)), SynthesisError> {
        // since we are in a circuit we don't use projective coodinates cause inversions are
        // "cheap" in terms of constraints 

        // we also do not want to have branching here,
        // so this function implicitly requires that 
        // points are not equal

        // we need to calculate lambda = (y' - y)/(x' - x). We don't care about a particular
        // value of y' - y, so we don't add them explicitly and just use in inversion witness

        let this_value = self.get_value();
        let other_value = other.get_value();

        let this_x = self.x;
        let this_y = self.y;

        let other_x = other.x;
        let other_y = other.y;

        let (this_y_negated, this_y) = this_y.negated(cs)?;
        let (this_x_negated, this_x) = this_x.negated(cs)?;

        let (other_x_minus_this_x, (other_x, this_x_negated)) = other_x.add(cs, this_x_negated)?;

        let (other_x_negated, other_x) = other_x.negated(cs)?;
        let (other_y_negated, other_y) = other_y.negated(cs)?;

        let (lambda, (mut tmp, _)) = FieldElement::div_from_addition_chain(cs, vec![other_y, this_y_negated], other_x_minus_this_x)?;

        let this_y_negated = tmp.pop().unwrap();
        let other_y = tmp.pop().unwrap();

        // lambda^2 + (-x' - x)
        let (new_x, (_, lambda, _)) = lambda.clone().fma_with_addition_chain(cs, lambda, vec![other_x_negated, this_x_negated])?;

        // lambda * (x - new_x) + (- y)

        let (this_x_minus_new_x, (this_x, new_x)) = this_x.sub(cs, new_x)?;
        let (new_y, _) = lambda.fma_with_addition_chain(cs, this_x_minus_new_x, vec![this_y_negated])?;

        let new_value = match (this_value, other_value) {
            (Some(this), Some(other)) => {
                assert!(this != other);
                let mut tmp = this.into_projective();
                tmp.add_assign_mixed(&other);

                Some(tmp.into_affine())
            },
            _ => None
        };
   
        let new = Self {
            x: new_x,
            y: new_y,
            value: new_value
        };

        let this = Self {
            x: this_x,
            y: this_y,
            value: this_value
        };

        let other = Self {
            x: other_x,
            y: other_y,
            value: other_value
        };

        Ok((new, (this, other)))
    }

    pub fn double_and_add<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
        other: Self
    ) -> Result<(Self, (Self, Self)), SynthesisError> {
        // doubles self and adds other

        let this_value = self.get_value();
        let other_value = other.get_value();

        let this_x = self.x;
        let this_y = self.y;

        let other_x = other.x;
        let other_y = other.y;

        let (this_y_negated, this_y) = this_y.negated(cs)?;
        let (this_x_negated, this_x) = this_x.negated(cs)?;

        let (other_x_minus_this_x, (other_x, this_x_negated)) = other_x.add(cs, this_x_negated)?;

        let (other_x_negated, other_x) = other_x.negated(cs)?;
        let (other_y_negated, other_y) = other_y.negated(cs)?;

        let (lambda, (mut tmp, _)) = FieldElement::div_from_addition_chain(cs, vec![other_y, this_y_negated], other_x_minus_this_x)?;

        let this_y_negated = tmp.pop().unwrap();
        let other_y = tmp.pop().unwrap();

        // lambda^2 + (-x' - x)
        let (new_x, (lambda, _)) = lambda.square_with_addition_chain(cs, vec![other_x_negated, this_x_negated])?;

        // lambda * (x - new_x) + (- y)

        let (this_x_minus_new_x, (this_x, new_x)) = this_x.sub(cs, new_x)?;
        let (new_y, _) = lambda.fma_with_addition_chain(cs, this_x_minus_new_x, vec![this_y_negated])?;

        let new_value = match (this_value, other_value) {
            (Some(this), Some(other)) => {
                assert!(this != other);
                let mut tmp = this.into_projective();
                tmp.add_assign_mixed(&other);

                Some(tmp.into_affine())
            },
            _ => None
        };
   
        let new = Self {
            x: new_x,
            y: new_y,
            value: new_value
        };

        let this = Self {
            x: this_x,
            y: this_y,
            value: this_value
        };

        let other = Self {
            x: other_x,
            y: other_y,
            value: other_value
        };

        Ok((new, (this, other)))
    }


}



#[cfg(test)]
mod test {
    use super::*;

    use crate::bellman::pairing::bn256::{Fq, Bn256, Fr, G1Affine};

    #[test]
    fn test_add_on_random_witnesses(){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

        for i in 0..100 {
            let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNextEquation>::new();

            let a_f: G1Affine = rng.gen();
            let b_f: G1Affine = rng.gen();
            let a = AffinePoint::alloc(
                &mut cs, 
                Some(a_f), 
                &params
            ).unwrap();

            let b = AffinePoint::alloc(
                &mut cs, 
                Some(b_f), 
                &params
            ).unwrap();
    
            let (result, (a, b)) = a.add_unequal(&mut cs, b).unwrap();

            assert!(cs.is_satisfied());

            let x_fe = result.x.get_field_value().unwrap();
            let y_fe = result.y.get_field_value().unwrap();

            let (x, y) = result.get_value().unwrap().into_xy_unchecked();

            assert_eq!(x_fe, x, "x coords mismatch");
            assert_eq!(y_fe, y, "y coords mismatch");

            if i == 0 {
                let base = cs.n();
                let _ = a.add_unequal(&mut cs, b).unwrap();
                println!("Single addition taken {} gates", cs.n() - base);
            }
        }
    }
}