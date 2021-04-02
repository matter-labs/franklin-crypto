use crate::generic_twisted_edwards::edwards::TwistedEdwardsPoint;
use crate::generic_twisted_edwards::edwards::TwistedEdwardsCurve;
use crate::bellman::plonk::better_better_cs::cs::ConstraintSystem;
use crate::bellman::{Engine, Field, PrimeField, SqrtField, SynthesisError};
use crate::plonk::circuit::Assignment;
use crate::plonk::circuit::allocated_num::{AllocatedNum, Num};
use crate::plonk::circuit::{boolean::Boolean, linear_combination::LinearCombination};
pub trait CircuitTwistedEdwardsCurve<E: Engine>: TwistedEdwardsCurve<E> {
    type Fs: PrimeField;

    fn add<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        p: &CircuitTwistedEdwardsPoint<E>,
        q: &CircuitTwistedEdwardsPoint<E>,
    ) -> Result<CircuitTwistedEdwardsPoint<E>, SynthesisError>;
    fn double<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        p: &CircuitTwistedEdwardsPoint<E>,
    ) -> Result<CircuitTwistedEdwardsPoint<E>, SynthesisError>;
    fn mul<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        p: &CircuitTwistedEdwardsPoint<E>,
        s: &[Boolean],
    ) -> Result<CircuitTwistedEdwardsPoint<E>, SynthesisError>;
    fn subgroup_check<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        p: &CircuitTwistedEdwardsPoint<E>,
    ) -> Result<(), SynthesisError>;
    fn mul_by_generator<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        s: &[Boolean],
    ) -> Result<CircuitTwistedEdwardsPoint<E>, SynthesisError>;
    fn alloc_point<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        p: Option<TwistedEdwardsPoint<E>>,
    ) -> Result<CircuitTwistedEdwardsPoint<E>, SynthesisError>;
}

// TODO: may me add another type param as C: CircuitTwistedEdwardsCurve<E: Engine>
#[derive(Clone)]
pub struct CircuitTwistedEdwardsPoint<E: Engine> {
    pub x: Num<E>,
    pub y: Num<E>,
}

impl<E: Engine> CircuitTwistedEdwardsPoint<E> {
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

        Ok(Self { x, y })
    }
}
