use crate::generic_twisted_edwards::edwards::*;
use crate::bellman::plonk::better_better_cs::cs::ConstraintSystem;
use crate::bellman::{Engine, Field, PrimeField, SqrtField, SynthesisError};
use crate::plonk::circuit::Assignment;
use crate::plonk::circuit::allocated_num::{AllocatedNum, Num};
use crate::plonk::circuit::{boolean::Boolean, linear_combination::LinearCombination};

pub struct CircuitTwistedEdwardsCurveImplementor<E: Engine, C: TwistedEdwardsCurveParams<E>> {
    pub implementor: TwistedEdwardsCurveImplementor<E, C>
}

impl<E: Engine, C: TwistedEdwardsCurveParams<E>> CircuitTwistedEdwardsCurveImplementor<E, C> {
    pub fn add<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        p: &CircuitTwistedEdwardsPoint<E>,
        q: &CircuitTwistedEdwardsPoint<E>,
    ) -> Result<CircuitTwistedEdwardsPoint<E>, SynthesisError> {
        if !self.implementor.curve_params.is_param_a_equals_minus_one() {
            unimplemented!("not yet implemented for a != -1");
        }
        // Compute U = (x1 + y1) * (x2 + y2)
        let t0 = p.x.add(cs, &p.y)?;
        let t1 = q.x.add(cs, &q.y)?;
        let u = t0.mul(cs, &t1)?;

        // Compute A = y2 * x1
        let a = q.y.mul(cs, &p.x)?;

        // Compute B = x2 * y1
        let b = q.x.mul(cs, &p.y)?;

        // Compute C = d*A*B
        let param_d = Num::Constant(self.implementor.curve_params.param_d());
        let t2 = a.mul(cs, &b)?;
        let c = t2.mul(cs, &param_d)?;

        // Compute x3 = (A + B) / (1 + C)
        let t3 = a.add(cs, &b)?;
        let t4 = c.add(cs, &Num::Constant(E::Fr::one()))?;
        let x3 = t3.div(cs, &t4)?;

        // Compute y3 = (U - A - B) / (1 - C)
        let t5 = t3.negate(cs)?;
        let t6 = u.add(cs, &t5)?;
        let t7 = Num::Constant(E::Fr::one()).sub(cs, &c)?;
        let y3 = t6.div(cs, &t7)?;

        Ok(CircuitTwistedEdwardsPoint { x: x3, y: y3 })
    }
    pub fn double<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        p: &CircuitTwistedEdwardsPoint<E>,
    ) -> Result<CircuitTwistedEdwardsPoint<E>, SynthesisError> {
        if !self.implementor.curve_params.is_param_a_equals_minus_one() {
            unimplemented!("not yet implemented for a != -1");
        }
        // Compute T = (x1 + y1) * (x1 + y1)
        let t0 = p.x.add(cs, &p.y)?;

        let t = t0.mul(cs, &t0)?;

        // Compute A = x1 * y1
        let a = p.x.mul(cs, &p.y)?;

        // Compute C = d*A*A
        let param_d = Num::Constant(self.implementor.curve_params.param_d());
        let t1 = a.mul(cs, &a)?;
        let c = t1.mul(cs, &param_d)?;

        // Compute x3 = (2.A) / (1 + C)
        let t2 = a.add(cs, &a)?;
        let t3 = c.add(cs, &Num::Constant(E::Fr::one()))?;
        let x3 = t2.div(cs, &t3)?;

        // Compute y3 = (T - 2.A) / (1 - C)
        let t5 = t.sub(cs, &t2)?;
        let t6 = Num::Constant(E::Fr::one()).sub(cs, &c)?;
        let y3 = t5.div(cs, &t6)?;

        Ok(CircuitTwistedEdwardsPoint { x: x3, y: y3 })
    }
    pub fn mul<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        p: &CircuitTwistedEdwardsPoint<E>,
        s: &[Boolean],
    ) -> Result<CircuitTwistedEdwardsPoint<E>, SynthesisError> {
        if !self.implementor.curve_params.is_param_a_equals_minus_one() {
            unimplemented!("not yet implemented for a != -1");
        }

        // Represents the current "magnitude" of the base
        // that we're operating over. Starts at self,
        // then 2*self, then 4*self, ...
        let mut curbase = None;

        // Represents the result of the multiplication
        let mut result = None;
        let inf = CircuitTwistedEdwardsPoint::zero(cs);
        // for (i, bit) in s.get_variable().into_bits_le(cs, None)?.iter().enumerate() {
        for (_i, bit) in s.iter().enumerate() {
            if curbase.is_none() {
                curbase = Some(p.clone())
            } else {
                let tmp = curbase.unwrap();
                curbase = Some(self.double(cs, &tmp.clone())?);
            }

            // Represents the select base. If the bit for this magnitude
            // is true, this will return `curbase`. Otherwise it will
            // return the neutral element, which will have no effect on
            // the result.
            let tmp = curbase.as_ref().unwrap().clone();
            let thisbase = CircuitTwistedEdwardsPoint::conditionally_select(cs, bit, &tmp, &inf)?;

            if result.is_none() {
                result = Some(thisbase);
            } else {
                result = Some(self.add(cs, &result.unwrap(), &thisbase)?);
            }
        }

        Ok(result.unwrap())
    }
    pub fn subgroup_check<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        p: &CircuitTwistedEdwardsPoint<E>,
    ) -> Result<(), SynthesisError> {
        if !self.implementor.curve_params.is_param_a_equals_minus_one() {
            unimplemented!("not yet implemented for a != -1");
        }

        let mut tmp = p.clone();

        for _ in 0..self.implementor.curve_params.log_2_cofactor() {
            tmp = self.double(cs, &tmp)?;
        }

        // (0, -1) is a small order point, but won't ever appear here
        // because cofactor is 2^3, and we performed three doublings.
        // (0, 1) is the neutral element, so checking if x is nonzero
        // is sufficient to prevent small order points here.
        tmp.x.get_variable().assert_not_zero(cs)?;

        Ok(())
    }
    pub fn mul_by_generator<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        s: &[Boolean],
    ) -> Result<CircuitTwistedEdwardsPoint<E>, SynthesisError> {
        if !self.implementor.curve_params.is_param_a_equals_minus_one() {
            unimplemented!("not yet implemented for a != -1");
        }

        let generator = self.generator();

        self.mul(cs, &generator, s)
    }
    pub fn alloc_point_checked_on_curve<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        p: Option<TwistedEdwardsPoint<E>>,
    ) -> Result<CircuitTwistedEdwardsPoint<E>, SynthesisError> {
        let p = p.map(|p| p.into_xy());

        let x_witness = p.map(|p| p.0);
        let y_witness = p.map(|p| p.1);

        let x = Num::Variable(AllocatedNum::alloc(cs, || Ok(*x_witness.get()?))?);
        let y = Num::Variable(AllocatedNum::alloc(cs, || Ok(*y_witness.get()?))?);

        self.from_xy_assert_on_curve(cs, &x, &y)?;

        Ok(CircuitTwistedEdwardsPoint { x, y })
    }

    pub fn generator(&self) -> CircuitTwistedEdwardsPoint<E>
    {
        let gen = self.implementor.curve_params.generator();
        let (x, y) = gen.into_xy();
        let x = Num::Constant(x);
        let y = Num::Constant(y);

        CircuitTwistedEdwardsPoint { x, y }
    }

    // pub fn generator_as_allocated_variable<CS>(&self, cs: &mut CS) -> Result<CircuitTwistedEdwardsPoint<E>, SynthesisError>
    // where
    //     CS: ConstraintSystem<E>,
    // {
    //     let gen = self.implementor.curve_params.generator();
    //     let (x, y) = gen.into_xy();
    //     let x = Num::Constant(x);
    //     let y = Num::Constant(y);

    //     Ok(CircuitTwistedEdwardsPoint { x, y })
    // }

    pub fn from_xy_assert_on_curve<CS>(
        &self,
        cs: &mut CS,
        x: &Num<E>,
        y: &Num<E>,
    ) -> Result<CircuitTwistedEdwardsPoint<E>, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        if !self.implementor.curve_params.is_param_a_equals_minus_one() {
            unimplemented!("not yet implemented for a != -1");
        }

        // x^2
        let x2 = x.mul(cs, &x)?;

        // y^2
        let y2 = y.mul(cs, &y)?;

        // x^2*y^2
        let x2y2 = x2.mul(cs, &y2)?;

        // y^2 - x^2 == 1 + d*x^2*y^2
        let lhs = y2.sub(cs, &x2)?;
        let param_d = Num::Constant(self.implementor.curve_params.param_d());
        let tmp = param_d.mul(cs, &x2y2)?;
        let rhs = Num::Constant(E::Fr::one()).add(cs, &tmp)?;

        lhs.enforce_equal(cs, &rhs)?;

        Ok(CircuitTwistedEdwardsPoint {
            x: x.clone(),
            y: y.clone(),
        })
    }
}

// TODO: may me add another type param as C: CircuitTwistedEdwardsCurve<E: Engine>
#[derive(Clone, Debug)]
pub struct CircuitTwistedEdwardsPoint<E: Engine> {
    pub x: Num<E>,
    pub y: Num<E>,
}

impl<E: Engine> Copy for CircuitTwistedEdwardsPoint<E> {}

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
