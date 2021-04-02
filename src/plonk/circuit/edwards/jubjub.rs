use super::edwards::{CircuitTwistedEdwardsCurve, CircuitTwistedEdwardsPoint};
use crate::bellman::plonk::better_better_cs::cs::ConstraintSystem;
use crate::generic_twisted_edwards::edwards::TwistedEdwardsPoint;
use crate::bellman::{Engine, Field, PrimeField, SqrtField, SynthesisError};
use crate::plonk::circuit::Assignment;
use crate::plonk::circuit::allocated_num::{AllocatedNum, Num};
use crate::plonk::circuit::boolean::Boolean;

#[derive(Clone)]
pub struct CircuitAltJubjub<E: Engine> {
    edwards_d: E::Fr,
}

impl<E: Engine> CircuitAltJubjub<E> {
    pub fn new() -> Self {
        // d = -(168696/168700)
        let edwards_d = E::Fr::from_str(
            "12181644023421730124874158521699555681764249180949974110617291017600649128846",
        )
        .unwrap();
        Self { edwards_d }
    }
}

impl<E: Engine> EdwardsCurve<E> for CircuitAltJubjub<E> {
    type Fs = crate::alt_babyjubjub::fs::Fs;

    fn alloc_point<CS>(
        &self,
        cs: &mut CS,
        p: Option<TwistedEdwardsPoint<E>>,
    ) -> Result<EdwardsPoint<E>, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let p = p.map(|p| p.into_xy());

        let x_witness = p.as_ref().map(|p| p.0);
        let y_witness = p.as_ref().map(|p| p.1);

        let x = Num::Variable(AllocatedNum::alloc(cs, || Ok(*x_witness.get()?))?);
        let y = Num::Variable(AllocatedNum::alloc(cs, || Ok(*y_witness.get()?))?);

        self.is_on_curve(cs, &x, &y)?;

        Ok(EdwardsPoint { x, y })
    }

    fn add<CS>(
        &self,
        cs: &mut CS,
        p: &EdwardsPoint<E>,
        q: &EdwardsPoint<E>,
    ) -> Result<EdwardsPoint<E>, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        // Compute U = (x1 + y1) * (x2 + y2)
        let t0 = p.x.add(cs, &p.y)?;
        let t1 = q.x.add(cs, &q.y)?;
        let u = t0.mul(cs, &t1)?;

        // Compute A = y2 * x1
        let a = q.y.mul(cs, &p.x)?;

        // Compute B = x2 * y1
        let b = q.x.mul(cs, &p.y)?;

        // Compute C = d*A*B
        let param_d = Num::Constant(self.edwards_d);
        let t2 = a.mul(cs, &b)?;
        let c = t2.mul(cs, &param_d)?;

        // Compute x3 = (A + B) / (1 + C)
        let t3 = a.add(cs, &b)?;
        let t4 = c.add(cs, &Num::Constant(E::Fr::one()))?;
        let x3 = Num::Variable(t3.get_variable().div(cs, &t4.get_variable())?);

        // Compute y3 = (U - A - B) / (1 - C)
        let t5 = t3.negate(cs)?;
        let t6 = u.add(cs, &t5)?;
        let t7 = Num::Constant(E::Fr::one()).sub(cs, &c)?;
        let y3 = Num::Variable(t6.get_variable().div(cs, &t7.get_variable())?);

        Ok(EdwardsPoint { x: x3, y: y3 })
    }

    fn double<CS>(
        &self,
        cs: &mut CS,
        p: &EdwardsPoint<E>,
    ) -> Result<EdwardsPoint<E>, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        // Compute T = (x1 + y1) * (x1 + y1)
        let t0 = p.x.add(cs, &p.y)?;

        let t = t0.mul(cs, &t0)?;

        // Compute A = x1 * y1
        let a = p.x.mul(cs, &p.y)?;

        // Compute C = d*A*A
        let param_d = Num::Constant(self.edwards_d);
        let t1 = a.mul(cs, &a)?;
        let c = t1.mul(cs, &param_d)?;

        // Compute x3 = (2.A) / (1 + C)
        let t2 = a.add(cs, &a)?;
        let t3 = c.add(cs, &Num::Constant(E::Fr::one()))?;
        let x3 = Num::Variable(t2.get_variable().div(cs, &t3.get_variable())?);

        // Compute y3 = (T - 2.A) / (1 - C)
        let t5 = t.sub(cs, &t2)?;
        let t6 = Num::Constant(E::Fr::one()).sub(cs, &c)?;
        let y3 = Num::Variable(t5.get_variable().div(cs, &t6.get_variable())?);

        Ok(EdwardsPoint { x: x3, y: y3 })
    }

    fn mul<CS>(
        &self,
        cs: &mut CS,
        p: &EdwardsPoint<E>,
        s: &[Boolean],
    ) -> Result<EdwardsPoint<E>, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        // Represents the current "magnitude" of the base
        // that we're operating over. Starts at self,
        // then 2*self, then 4*self, ...
        let mut curbase = None;

        // Represents the result of the multiplication
        let mut result = None;
        let inf = EdwardsPoint::zero(cs);
        // for (i, bit) in s.get_variable().into_bits_le(cs, None)?.iter().enumerate() {
        for (i, bit) in s.iter().enumerate() {
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
            let thisbase = EdwardsPoint::conditionally_select(cs, bit, &tmp, &inf)?;

            if result.is_none() {
                result = Some(thisbase);
            } else {
                result = Some(self.add(cs, &result.unwrap(), &thisbase)?);
            }
        }

        Ok(result.unwrap())
    }

    // Assert that whether point has correct order or not
    fn subgroup_check<CS>(
        &self,
        cs: &mut CS,
        p: &EdwardsPoint<E>,
    ) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let tmp = self.double(cs, p)?;
        let tmp = self.double(cs, &tmp)?;
        let tmp = self.double(cs, &tmp)?;

        // (0, -1) is a small order point, but won't ever appear here
        // because cofactor is 2^3, and we performed three doublings.
        // (0, 1) is the neutral element, so checking if x is nonzero
        // is sufficient to prevent small order points here.
        tmp.x.get_variable().assert_not_zero(cs)?;

        Ok(())
    }

    fn mul_by_generator<CS>(
        &self,
        cs: &mut CS,
        s: &[Boolean],
    ) -> Result<EdwardsPoint<E>, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let generator = Self::generator(cs)?;

        self.mul(cs, &generator, s)
    }
}

impl<E: Engine> CircuitAltJubjub<E> {
    pub fn generator<CS>(cs: &mut CS) -> Result<EdwardsPoint<E>, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let x = Num::Variable(AllocatedNum::alloc(cs, || {
            Ok(E::Fr::from_str(
                "21237458262955047976410108958495203094252581401952870797780751629344472264183",
            )
            .unwrap())
        })?);
        let y = Num::Variable(AllocatedNum::alloc(cs, || {
            Ok(E::Fr::from_str(
                "2544379904535866821506503524998632645451772693132171985463128613946158519479",
            )
            .unwrap())
        })?);

        Ok(EdwardsPoint { x, y })
    }

    pub fn is_on_curve<CS>(
        &self,
        cs: &mut CS,
        x: &Num<E>,
        y: &Num<E>,
    ) -> Result<EdwardsPoint<E>, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        // x^2
        let x2 = x.mul(cs, &x)?;

        // y^2
        let y2 = y.mul(cs, &y)?;

        // x^2*y^2
        let x2y2 = x2.mul(cs, &y2)?;

        // y^2 - x^2 == 1 + d*x^2*y^2
        let lhs = y2.sub(cs, &x2)?;
        let param_d = Num::Constant(self.edwards_d);
        let tmp = param_d.mul(cs, &x2y2)?;
        let rhs = Num::Constant(E::Fr::one()).add(cs, &tmp)?;

        lhs.enforce_equal(cs, &rhs)?;

        Ok(EdwardsPoint {
            x: x.clone(),
            y: y.clone(),
        })
    }
}
