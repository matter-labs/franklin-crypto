use crate::alt_babyjubjub::v2::edwards::TwistedEdwardsPoint;
use crate::bellman::plonk::better_better_cs::cs::ConstraintSystem;
use crate::bellman::{Engine, Field, PrimeField, SqrtField, SynthesisError};
use crate::circuit::Assignment;
use crate::plonk::circuit::allocated_num::{AllocatedNum, Num};
use crate::plonk::circuit::{boolean::Boolean, linear_combination::LinearCombination};
pub trait EdwardsCurve<E: Engine>: std::clone::Clone {
    type Fs: PrimeField;

    fn add<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        p: &EdwardsPoint<E>,
        q: &EdwardsPoint<E>,
    ) -> Result<EdwardsPoint<E>, SynthesisError>;
    fn double<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        p: &EdwardsPoint<E>,
    ) -> Result<EdwardsPoint<E>, SynthesisError>;
    fn mul<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        p: &EdwardsPoint<E>,
        s: &[Boolean],
    ) -> Result<EdwardsPoint<E>, SynthesisError>;
    fn subgroup_check<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        p: &EdwardsPoint<E>,
    ) -> Result<(), SynthesisError>;
    fn mul_by_generator<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        s: &[Boolean],
    ) -> Result<EdwardsPoint<E>, SynthesisError>;
    fn alloc_point<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        p: Option<TwistedEdwardsPoint<E>>,
    ) -> Result<EdwardsPoint<E>, SynthesisError>;
}

#[derive(Clone)]
pub struct EdwardsPoint<E: Engine> {
    pub x: Num<E>,
    pub y: Num<E>,
}

impl<E: Engine> EdwardsPoint<E> {
    pub fn zero<CS: ConstraintSystem<E>>(cs: &mut CS) -> Self {
        Self {
            x: Num::Variable(AllocatedNum::zero(cs)),
            y: Num::Variable(AllocatedNum::one(cs)),
        }
    }

    pub fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        flag: &Boolean,
        first: &Self,
        second: &Self,
    ) -> Result<Self, SynthesisError> {
        let x = Num::conditionally_select(cs, flag, &first.x, &second.x)?;
        let y = Num::conditionally_select(cs, flag, &first.y, &second.y)?;

        Ok(EdwardsPoint { x, y })
    }
}
