use crate::generic_twisted_edwards::edwards::*;
use crate::bellman::plonk::better_better_cs::cs::ConstraintSystem;
use crate::bellman::{Engine, Field, PrimeField, SqrtField, SynthesisError};
use crate::plonk::circuit::Assignment;
use crate::plonk::circuit::allocated_num::{AllocatedNum, Num};
use crate::plonk::circuit::simple_term::Term;
use crate::plonk::circuit::{boolean::Boolean, linear_combination::LinearCombination};

pub struct CircuitTwistedEdwardsCurveImplementor<E: Engine, C: TwistedEdwardsCurveParams<E>> {
    pub implementor: TwistedEdwardsCurveImplementor<E, C>
}

impl<E: Engine, C: TwistedEdwardsCurveParams<E>> CircuitTwistedEdwardsCurveImplementor<E, C> {
    pub fn new_from_params(params: C) -> Self {
        let out_of_circuit_implementor = TwistedEdwardsCurveImplementor::new_from_params(params);

        Self {
            implementor: out_of_circuit_implementor
        }
    }
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
        // save on multiplication
        let mut c = Term::from_num(a).mul(cs, &Term::from_num(b))?;
        c.scale(&self.implementor.curve_params.param_d());

        // Compute x3 = (A + B) / (1 + C)
        let t3 = a.add(cs, &b)?;
        // save on division
        let mut c_plus_one = c.clone();
        c_plus_one.add_constant(&E::Fr::one());
        let t3 = Term::from_num(t3);
        let x3 = t3.div(cs, &c_plus_one)?.into_num();

        // Compute y3 = (U - A - B) / (1 - C)
        let u = Term::from_num(u);
        let mut t5 = t3;
        t5.negate();
        let t6 = u.add(cs, &t5)?;
        let mut t7 = c.clone();
        t7.negate();
        t7.add_constant(&E::Fr::one());

        let y3 = t6.div(cs, &t7)?;
        let y3 = y3.into_num();

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

        let mut two = E::Fr::one();
        two.double();

        // Compute C = d*A*A
        let mut c = Term::from_num(a).mul(cs, &Term::from_num(a))?;
        c.scale(&self.implementor.curve_params.param_d());

        // Compute x3 = (2.A) / (1 + C)
        let mut t3 = Term::from_num(a);
        t3.scale(&two);
        let mut c_plus_one = c.clone();
        c_plus_one.add_constant(&E::Fr::one());
        let x3 = t3.div(cs, &c_plus_one)?.into_num();

        // Compute y3 = (T - 2.A) / (1 - C)
        let t5 = Term::from_num(t).sub(cs, &t3)?;
        let mut t6 = c.clone();
        t6.negate();
        t6.add_constant(&E::Fr::one());
        let y3 = t5.div(cs, &t6)?;
        let y3 = y3.into_num();

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
        let inf = CircuitTwistedEdwardsPoint::zero();
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
    // pub fn subgroup_check<CS: ConstraintSystem<E>>(
    //     &self,
    //     cs: &mut CS,
    //     p: &CircuitTwistedEdwardsPoint<E>,
    // ) -> Result<(), SynthesisError> {
    //     if !self.implementor.curve_params.is_param_a_equals_minus_one() {
    //         unimplemented!("not yet implemented for a != -1");
    //     }

    //     let mut tmp = p.clone();

    //     for _ in 0..self.implementor.curve_params.log_2_cofactor() {
    //         tmp = self.double(cs, &tmp)?;
    //     }

    //     // (0, -1) is a small order point, but won't ever appear here
    //     // because cofactor is 2^3, and we performed three doublings.
    //     // (0, 1) is the neutral element, so checking if x is nonzero
    //     // is sufficient to prevent small order points here.
    //     tmp.x.get_variable().assert_not_zero(cs)?;

    //     Ok(())
    // }
    pub fn is_in_main_subgroup<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        p: &CircuitTwistedEdwardsPoint<E>,
    ) -> Result<Boolean, SynthesisError> {
        if !self.implementor.curve_params.is_param_a_equals_minus_one() {
            unimplemented!("not yet implemented for a != -1");
        }

        use crate::plonk::circuit::utils::words_to_msb_first_bits;

        let mut tmp = p.clone();

        let msb_bits = words_to_msb_first_bits(C::Fs::char().as_ref());
        for b in msb_bits.into_iter().skip(1) {
            tmp = self.double(cs, &tmp)?;
            if b {
                tmp = self.add(cs, &tmp, p)?;
            }
        }

        CircuitTwistedEdwardsPoint::equals(
            cs,
            &CircuitTwistedEdwardsPoint::zero(),
            &tmp
        )
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
    pub fn alloc_point_enforce_on_curve<CS: ConstraintSystem<E>>(
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
    pub fn alloc_point_unchecked<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        p: Option<TwistedEdwardsPoint<E>>,
    ) -> Result<CircuitTwistedEdwardsPoint<E>, SynthesisError> {
        let p = p.map(|p| p.into_xy());

        let x_witness = p.map(|p| p.0);
        let y_witness = p.map(|p| p.1);

        let x = Num::Variable(AllocatedNum::alloc(cs, || Ok(*x_witness.get()?))?);
        let y = Num::Variable(AllocatedNum::alloc(cs, || Ok(*y_witness.get()?))?);

        Ok(CircuitTwistedEdwardsPoint { x, y })
    }
    // TODO: optimize using terms
    pub fn check_is_on_curve<CS: ConstraintSystem<E>>(&self, cs: &mut CS, p: &CircuitTwistedEdwardsPoint<E>) -> Result<Boolean, SynthesisError> {
        if !self.implementor.curve_params.is_param_a_equals_minus_one() {
            unimplemented!("not yet implemented for a != -1");
        }

        let x = p.x;
        let y = p.y;
        
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

        Num::equals(cs, &lhs, &rhs)
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
    pub fn zero() -> Self {
        Self {
            x: Num::zero(),
            y: Num::one(),
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

    pub fn equals<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        first: &Self,
        second: &Self
    ) -> Result<Boolean, SynthesisError> {
        let a = Num::equals(cs, &first.x, &second.x)?;
        let b = Num::equals(cs, &first.y, &second.y)?;

        Boolean::and(cs, &a, &b)
    }
}
