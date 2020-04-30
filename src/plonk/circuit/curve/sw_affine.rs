use crate::bellman::pairing::{
    Engine,
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
    PlonkConstraintSystemParams
};

use super::super::allocated_num::{AllocatedNum, Num};
use super::super::linear_combination::LinearCombination;
use super::super::simple_term::Term;
use super::super::boolean::Boolean;

use num_bigint::BigUint;
use num_integer::Integer;

use super::super::bigint::field::*;
use super::super::bigint::bigint::*;

use crate::bellman::pairing::CurveAffine;

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

        // TODO: 
        let x = FieldElement::new_allocated(
            cs, 
            x.unwrap(), 
            params
        )?;

        let y = FieldElement::new_allocated(
            cs, 
            y.unwrap(), 
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
            fe_to_biguint(&x),
            params
        )?;

        let y = FieldElement::new_constant(
            fe_to_biguint(&y),
            params
        )?;

        let new = Self {
            x,
            y,
            value: Some(value)
        };

        Ok(new)
    }

    pub fn add_unequal<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        other: &Self
    ) -> Result<Self, SynthesisError> {
        // since we are in a circuit we don't use projective coodinates cause inversions are
        // "cheap" in terms of constraints 

        // we also do not want to have branching here,
        // so this function explicitly requires that 
        // points are not equal

        let this_x = self.x.reduce_if_necessary(cs)?;
        let this_y = self.y.reduce_if_necessary(cs)?;

        let other_x = other.x.reduce_if_necessary(cs)?;
        let other_y = other.y.reduce_if_necessary(cs)?;
    
        let num = other_y.sub(cs, &this_y)?;
        let den = other_x.sub(cs, &this_x)?;

        let minus_this_x : FieldElement<'a, E, G::Base>= FieldElement::<_, _>::zero(self.x.representation_params).sub(cs, &this_x)?;
        let minus_other_x : FieldElement<'a, E, G::Base>= FieldElement::<_, _>::zero(self.x.representation_params).sub(cs, &other_x)?; 
        let lambda = num.div(cs, &den)?;



    }
}

