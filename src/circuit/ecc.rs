use bellman::pairing::Engine;

use bellman::pairing::ff::{Field, PrimeField, SqrtField};
use bellman::{ConstraintSystem, SynthesisError};

use super::Assignment;

use super::num::{AllocatedNum, Num};

use jubjub::{edwards, FixedGenerators, JubjubEngine, JubjubParams};

use super::lookup::lookup3_xy;

use super::boolean::{AllocatedBit, Boolean};
use super::expression::*;
#[derive(Clone)]
pub struct EdwardsPoint<E: Engine> {
    x: AllocatedNum<E>,
    y: AllocatedNum<E>,
}

/// Perform a fixed-base scalar multiplication with
/// `by` being in little-endian bit order.
pub fn fixed_base_multiplication<E, CS>(
    mut cs: CS,
    base: FixedGenerators,
    by: &[Boolean],
    params: &E::Params,
) -> Result<EdwardsPoint<E>, SynthesisError>
where
    CS: ConstraintSystem<E>,
    E: JubjubEngine,
{
    // Represents the result of the multiplication
    let mut result = None;

    for (i, (chunk, window)) in by
        .chunks(3)
        .zip(params.circuit_generators(base).iter())
        .enumerate()
    {
        let chunk_a = chunk
            .get(0).cloned()
            .unwrap_or(Boolean::constant(false));
        let chunk_b = chunk
            .get(1).cloned()
            .unwrap_or(Boolean::constant(false));
        let chunk_c = chunk
            .get(2).cloned()
            .unwrap_or(Boolean::constant(false));

        let (x, y) = lookup3_xy(
            cs.namespace(|| format!("window table lookup {}", i)),
            &[chunk_a, chunk_b, chunk_c],
            window,
        )?;

        let p = EdwardsPoint { x, y };

        if result.is_none() {
            result = Some(p);
        } else {
            result = Some(result.unwrap().add(
                cs.namespace(|| format!("addition {}", i)),
                &p,
                params,
            )?);
        }
    }

    Ok(result.get()?.clone())
}

impl<E: JubjubEngine> EdwardsPoint<E> {
    pub fn get_x(&self) -> &AllocatedNum<E> {
        &self.x
    }

    pub fn get_y(&self) -> &AllocatedNum<E> {
        &self.y
    }

    pub fn assert_not_small_order<CS>(
        &self,
        mut cs: CS,
        params: &E::Params,
    ) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let tmp = self.double(cs.namespace(|| "first doubling"), params)?;
        let tmp = tmp.double(cs.namespace(|| "second doubling"), params)?;
        let tmp = tmp.double(cs.namespace(|| "third doubling"), params)?;

        // (0, -1) is a small order point, but won't ever appear here
        // because cofactor is 2^3, and we performed three doublings.
        // (0, 1) is the neutral element, so checking if x is nonzero
        // is sufficient to prevent small order points here.
        tmp.x.assert_nonzero(cs.namespace(|| "check x != 0"))?;

        Ok(())
    }

    pub fn inputize<CS>(&self, mut cs: CS) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        self.x.inputize(cs.namespace(|| "x"))?;
        self.y.inputize(cs.namespace(|| "y"))?;

        Ok(())
    }

    /// This converts the point into a representation.
    pub fn repr<CS>(&self, mut cs: CS) -> Result<Vec<Boolean>, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let mut tmp = vec![];

        let x = self.x.into_bits_le_strict(cs.namespace(|| "unpack x"))?;

        let y = self.y.into_bits_le_strict(cs.namespace(|| "unpack y"))?;

        tmp.extend(y);
        tmp.push(x[0].clone());

        Ok(tmp)
    }

    /// This 'witnesses' a point inside the constraint system.
    /// It guarantees the point is on the curve.
    pub fn witness<Order, CS>(
        mut cs: CS,
        p: Option<edwards::Point<E, Order>>,
        params: &E::Params,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let p = p.map(|p| p.into_xy());

        // Allocate x
        let x = AllocatedNum::alloc(cs.namespace(|| "x"), || Ok(p.get()?.0))?;

        // Allocate y
        let y = AllocatedNum::alloc(cs.namespace(|| "y"), || Ok(p.get()?.1))?;

        Self::interpret(cs.namespace(|| "point interpretation"), &x, &y, params)
    }

    /// Returns `self` if condition is true, and the neutral
    /// element (0, 1) otherwise.
    pub fn conditionally_select<CS>(
        &self,
        mut cs: CS,
        condition: &Boolean,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        // Compute x' = self.x if condition, and 0 otherwise
        let x_prime = AllocatedNum::alloc(cs.namespace(|| "x'"), || {
            if *condition.get_value().get()? {
                Ok(*self.x.get_value().get()?)
            } else {
                Ok(E::Fr::zero())
            }
        })?;

        // condition * x = x'
        // if condition is 0, x' must be 0
        // if condition is 1, x' must be x
        let one = CS::one();
        cs.enforce(
            || "x' computation",
            |lc| lc + self.x.get_variable(),
            |_| condition.lc(one, E::Fr::one()),
            |lc| lc + x_prime.get_variable(),
        );

        // Compute y' = self.y if condition, and 1 otherwise
        let y_prime = AllocatedNum::alloc(cs.namespace(|| "y'"), || {
            if *condition.get_value().get()? {
                Ok(*self.y.get_value().get()?)
            } else {
                Ok(E::Fr::one())
            }
        })?;

        // condition * y = y' - (1 - condition)
        // if condition is 0, y' must be 1
        // if condition is 1, y' must be y
        cs.enforce(
            || "y' computation",
            |lc| lc + self.y.get_variable(),
            |_| condition.lc(one, E::Fr::one()),
            |lc| lc + y_prime.get_variable() - &condition.not().lc(one, E::Fr::one()),
        );

        Ok(EdwardsPoint {
            x: x_prime,
            y: y_prime,
        })
    }

    /// Performs a scalar multiplication of this twisted Edwards
    /// point by a scalar represented as a sequence of booleans
    /// in little-endian bit order.
    pub fn mul<CS>(
        &self,
        mut cs: CS,
        by: &[Boolean],
        params: &E::Params,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        // Represents the current "magnitude" of the base
        // that we're operating over. Starts at self,
        // then 2*self, then 4*self, ...
        let mut curbase = None;

        // Represents the result of the multiplication
        let mut result = None;

        for (i, bit) in by.iter().enumerate() {
            if curbase.is_none() {
                curbase = Some(self.clone());
            } else {
                // Double the previous value
                curbase = Some(
                    curbase
                        .unwrap()
                        .double(cs.namespace(|| format!("doubling {}", i)), params)?,
                );
            }

            // Represents the select base. If the bit for this magnitude
            // is true, this will return `curbase`. Otherwise it will
            // return the neutral element, which will have no effect on
            // the result.
            let thisbase = curbase
                .as_ref()
                .unwrap()
                .conditionally_select(cs.namespace(|| format!("selection {}", i)), bit)?;

            if result.is_none() {
                result = Some(thisbase);
            } else {
                result = Some(result.unwrap().add(
                    cs.namespace(|| format!("addition {}", i)),
                    &thisbase,
                    params,
                )?);
            }
        }

        Ok(result.get()?.clone())
    }

    pub fn interpret<CS>(
        mut cs: CS,
        x: &AllocatedNum<E>,
        y: &AllocatedNum<E>,
        params: &E::Params,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        // -x^2 + y^2 = 1 + dx^2y^2

        let x2 = x.square(cs.namespace(|| "x^2"))?;
        let y2 = y.square(cs.namespace(|| "y^2"))?;
        let x2y2 = x2.mul(cs.namespace(|| "x^2 y^2"), &y2)?;

        let one = CS::one();
        cs.enforce(
            || "on curve check",
            |lc| lc - x2.get_variable() + y2.get_variable(),
            |lc| lc + one,
            |lc| lc + one + (*params.edwards_d(), x2y2.get_variable()),
        );

        Ok(EdwardsPoint {
            x: x.clone(),
            y: y.clone(),
        })
    }
    pub fn recover_from_y_unchecked<CS>(
        mut cs: CS,
        x: &Boolean,
        y: &AllocatedNum<E>,
        params: &E::Params,
    ) -> Result<(Self, Boolean), SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let t1_value = match y.get_value() {
            None => None,
            Some(y) => {
                let mut t1_value = y;
                t1_value.square();
                t1_value.sub_assign(&E::Fr::one());
                Some(t1_value)
            }
        };
        let t1 = AllocatedNum::alloc(cs.namespace(|| "t1"), || Ok(t1_value.grab()?))?;

        let t2_value = match y.get_value() {
            None => None,
            Some(y) => {
                let mut t2_value = y;
                t2_value.square();
                t2_value.mul_assign(&params.edwards_d());
                t2_value.add_assign(&E::Fr::one());
                Some(t2_value)
            }
        };
        let t2 = AllocatedNum::alloc(cs.namespace(|| "t2"), || Ok(t2_value.grab()?))?;

        cs.enforce(
            || " y * y = t1 + 1 ",
            |zero| zero + y.get_variable(),
            |zero| zero + y.get_variable(),
            |zero| zero + t1.get_variable() + (E::Fr::one(), CS::one()),
        );

        cs.enforce(
            || " d*y * y = t2 - 1 ",
            |zero| zero + (*params.edwards_d(), y.get_variable()),
            |zero| zero + y.get_variable(),
            |zero| zero + t2.get_variable() - (E::Fr::one(), CS::one()),
        );

        let t2_inv_value = match t2_value {
            None => None,
            Some(t2_value) => {
                if t2_value.is_zero() {
                    Some(E::Fr::one()) // return any number it doesn't matter
                } else {
                    Some(t2_value.inverse().unwrap())
                }
            }
        };

        let t2_inv = AllocatedNum::alloc(cs.namespace(|| "t2_inv"), || Ok(t2_inv_value.grab()?))?;

        // next three enforces result in a conditional inverse
        let is_t2_inversed = AllocatedBit::alloc(
            cs.namespace(|| "is_t2_inversed"),
            match t2_value {
                None => None,
                Some(t2_value) => Some(!t2_value.is_zero()),
            },
        )?;

        cs.enforce(
            || " t2_inv * t2 = is_t2_inversed ",
            |zero| zero + t2_inv.get_variable(),
            |zero| zero + t2.get_variable(),
            |zero| zero + is_t2_inversed.get_variable(),
        );

        cs.enforce(
            || " t2 * (is_t2_inversed - 1) = 0",
            |zero| zero + t2.get_variable(),
            |zero| zero + is_t2_inversed.get_variable() - (E::Fr::one(), CS::one()),
            |zero| zero,
        );

        // t1 * t2_inv = f
        let f_value = match (t1_value, t2_inv_value) {
            (Some(t1_value), Some(t2_inv_value)) => {
                let mut f_value = t1_value;
                f_value.mul_assign(&t2_inv_value);
                Some(f_value)
            }
            (_, _) => None,
        };
        let f = AllocatedNum::alloc(cs.namespace(|| "f"), || Ok(f_value.grab()?))?;

        cs.enforce(
            || " t1 * t2_inv = f",
            |zero| zero + t1.get_variable(),
            |zero| zero + t2_inv.get_variable(),
            |zero| zero + f.get_variable(),
        );

        // now we need to conditionally check if f is a quadratic residue
        let mut one_half = E::Fr::from_str("2").unwrap();
        one_half = one_half.inverse().unwrap();

        let mut power = E::Fr::zero();
        power.sub_assign(&E::Fr::one());
        power.mul_assign(&one_half); // now power=(p-1)/2 wher p is a characteristic of field

        let f_legendre_symbol = f.pow(
            cs.namespace(|| "f to the power of (p-1) divide by 2"),
            &power,
        )?; //Euler's criteria

        let is_f_quadratic_residue_value = match f_legendre_symbol.get_value() {
            None => None,
            Some(f_legendre_symbol) => {
                if f_legendre_symbol == E::Fr::one() {
                    Some(true)
                } else {
                    Some(false)
                }
            }
        };

        let is_f_quadratic_residue = AllocatedBit::alloc(
            cs.namespace(|| "is_f_quadratic_residue"),
            is_f_quadratic_residue_value,
        )?;

        let f_square_root_value = match (is_f_quadratic_residue_value, f_value) {
            (Some(is_f_quadratic_residue_value), Some(f_value)) => {
                if is_f_quadratic_residue_value {
                    Some(f_value.sqrt().unwrap())
                } else {
                    Some(E::Fr::zero()) // so zero or root
                }
            }
            (_, _) => None,
        };

        let f_square_root = AllocatedNum::alloc(cs.namespace(|| "f_square_root"), || {
            f_square_root_value.grab()
        })?;
        let e_value = match is_f_quadratic_residue_value {
            None => None,
            Some(is_f_quadratic_residue_value) => {
                if is_f_quadratic_residue_value {
                    Some(E::Fr::zero())
                } else {
                    f_value
                }
            }
        };
        let e = AllocatedNum::alloc(cs.namespace(|| "e"), || e_value.grab())?;

        cs.enforce(
            || " f_square_root * f_square_root = f - e",
            |zero| zero + f_square_root.get_variable(),
            |zero| zero + f_square_root.get_variable(),
            |zero| zero + f.get_variable() - e.get_variable(),
        );
        cs.enforce(
            || " e * is_f_quadratic_residue = 0",
            |zero| zero + e.get_variable(),
            |zero| zero + is_f_quadratic_residue.get_variable(),
            |zero| zero,
        ); // so if is_f_quadratic_residue is true => e==0 = > f_square_root * f_square_root = f
           // if is_f_quadratic_residue is false, then it's trash, but we already know that the point is not on the curve

        let f_square_root_bits =
            f_square_root.into_bits_le(cs.namespace(|| "f_square_root bits"))?;

        // f_square_root_bits[0] == x
        let should_x_negate = Boolean::xor(
            cs.namespace(|| "f_square_root_bits[0] == x"),
            &f_square_root_bits[0],
            &x,
        )?;

        let x_negated_value = match f_square_root_value {
            None => None,
            Some(f_square_root_value) => {
                let mut val = E::Fr::zero();
                val.sub_assign(&f_square_root_value);
                Some(val)
            }
        };
        let x_negated =
            AllocatedNum::alloc(cs.namespace(|| "x_negated"), || x_negated_value.grab())?;

        cs.enforce(
            || "x_negated + f_square_root = 0",
            |zero| zero + x_negated.get_variable() + f_square_root.get_variable(),
            |zero| zero + (E::Fr::one(), CS::one()),
            |zero| zero,
        );

        let x_coord = AllocatedNum::conditionally_select(
            cs.namespace(|| "determine pairity"),
            &x_negated,
            &f_square_root,
            &should_x_negate,
        )?;

        let is_succesfully_recovered = Boolean::and(
            cs.namespace(|| "is_sucesfully_recovered"),
            &Boolean::from(is_f_quadratic_residue),
            &Boolean::from(is_t2_inversed),
        )?;

        Ok((
            EdwardsPoint {
                x: x_coord,
                y: y.clone(),
            },
            is_succesfully_recovered,
        ))
    }

    pub fn from_x_y_unchecked<CS>(
        mut cs: CS,
        x: &AllocatedNum<E>,
        y: &AllocatedNum<E>,
        params: &E::Params,
    ) -> Result<(Self, Boolean), SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let x2 = x.square(cs.namespace(|| "x^2"))?;
        let y2 = y.square(cs.namespace(|| "y^2"))?;
        let x2y2 = x2.mul(cs.namespace(|| "x^2 y^2"), &y2)?;

        let one = CS::one();
        let num = Num::zero();
        let num = num.add_number_with_coeff(&x2y2, *params.edwards_d());

        let equals = Boolean::from(Expression::equals(
            cs.namespace(|| "is_on_curve"),
            Expression::from(&y2) - Expression::from(&x2),
            Expression::constant::<CS>(E::Fr::one()) + Expression::from(&num),
        )?);

        Ok((
            EdwardsPoint {
                x: x.clone(),
                y: y.clone(),
            },
            equals,
        ))
    }

    pub fn double<CS>(&self, mut cs: CS, params: &E::Params) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        // Compute T = (x1 + y1) * (x1 + y1)
        let t = AllocatedNum::alloc(cs.namespace(|| "T"), || {
            let mut t0 = *self.x.get_value().get()?;
            t0.add_assign(self.y.get_value().get()?);

            let mut t1 = *self.x.get_value().get()?;
            t1.add_assign(self.y.get_value().get()?);

            t0.mul_assign(&t1);

            Ok(t0)
        })?;

        cs.enforce(
            || "T computation",
            |lc| lc + self.x.get_variable() + self.y.get_variable(),
            |lc| lc + self.x.get_variable() + self.y.get_variable(),
            |lc| lc + t.get_variable(),
        );

        // Compute A = x1 * y1
        let a = self.x.mul(cs.namespace(|| "A computation"), &self.y)?;

        // Compute C = d*A*A
        let c = AllocatedNum::alloc(cs.namespace(|| "C"), || {
            let mut t0 = *a.get_value().get()?;
            t0.square();
            t0.mul_assign(params.edwards_d());

            Ok(t0)
        })?;

        cs.enforce(
            || "C computation",
            |lc| lc + (*params.edwards_d(), a.get_variable()),
            |lc| lc + a.get_variable(),
            |lc| lc + c.get_variable(),
        );

        // Compute x3 = (2.A) / (1 + C)
        let x3 = AllocatedNum::alloc(cs.namespace(|| "x3"), || {
            let mut t0 = *a.get_value().get()?;
            t0.double();

            let mut t1 = E::Fr::one();
            t1.add_assign(c.get_value().get()?);

            match t1.inverse() {
                Some(t1) => {
                    t0.mul_assign(&t1);

                    Ok(t0)
                }
                None => Err(SynthesisError::DivisionByZero),
            }
        })?;

        let one = CS::one();
        cs.enforce(
            || "x3 computation",
            |lc| lc + one + c.get_variable(),
            |lc| lc + x3.get_variable(),
            |lc| lc + a.get_variable() + a.get_variable(),
        );

        // Compute y3 = (U - 2.A) / (1 - C)
        let y3 = AllocatedNum::alloc(cs.namespace(|| "y3"), || {
            let mut t0 = *a.get_value().get()?;
            t0.double();
            t0.negate();
            t0.add_assign(t.get_value().get()?);

            let mut t1 = E::Fr::one();
            t1.sub_assign(c.get_value().get()?);

            match t1.inverse() {
                Some(t1) => {
                    t0.mul_assign(&t1);

                    Ok(t0)
                }
                None => Err(SynthesisError::DivisionByZero),
            }
        })?;

        cs.enforce(
            || "y3 computation",
            |lc| lc + one - c.get_variable(),
            |lc| lc + y3.get_variable(),
            |lc| lc + t.get_variable() - a.get_variable() - a.get_variable(),
        );

        Ok(EdwardsPoint { x: x3, y: y3 })
    }

    /// Perform addition between any two points
    pub fn add<CS>(
        &self,
        mut cs: CS,
        other: &Self,
        params: &E::Params,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        // Compute U = (x1 + y1) * (x2 + y2)
        let u = AllocatedNum::alloc(cs.namespace(|| "U"), || {
            let mut t0 = *self.x.get_value().get()?;
            t0.add_assign(self.y.get_value().get()?);

            let mut t1 = *other.x.get_value().get()?;
            t1.add_assign(other.y.get_value().get()?);

            t0.mul_assign(&t1);

            Ok(t0)
        })?;

        cs.enforce(
            || "U computation",
            |lc| lc + self.x.get_variable() + self.y.get_variable(),
            |lc| lc + other.x.get_variable() + other.y.get_variable(),
            |lc| lc + u.get_variable(),
        );

        // Compute A = y2 * x1
        let a = other.y.mul(cs.namespace(|| "A computation"), &self.x)?;

        // Compute B = x2 * y1
        let b = other.x.mul(cs.namespace(|| "B computation"), &self.y)?;

        // Compute C = d*A*B
        let c = AllocatedNum::alloc(cs.namespace(|| "C"), || {
            let mut t0 = *a.get_value().get()?;
            t0.mul_assign(b.get_value().get()?);
            t0.mul_assign(params.edwards_d());

            Ok(t0)
        })?;

        cs.enforce(
            || "C computation",
            |lc| lc + (*params.edwards_d(), a.get_variable()),
            |lc| lc + b.get_variable(),
            |lc| lc + c.get_variable(),
        );

        // Compute x3 = (A + B) / (1 + C)
        let x3 = AllocatedNum::alloc(cs.namespace(|| "x3"), || {
            let mut t0 = *a.get_value().get()?;
            t0.add_assign(b.get_value().get()?);

            let mut t1 = E::Fr::one();
            t1.add_assign(c.get_value().get()?);

            match t1.inverse() {
                Some(t1) => {
                    t0.mul_assign(&t1);

                    Ok(t0)
                }
                None => Err(SynthesisError::DivisionByZero),
            }
        })?;

        let one = CS::one();
        cs.enforce(
            || "x3 computation",
            |lc| lc + one + c.get_variable(),
            |lc| lc + x3.get_variable(),
            |lc| lc + a.get_variable() + b.get_variable(),
        );

        // Compute y3 = (U - A - B) / (1 - C)
        let y3 = AllocatedNum::alloc(cs.namespace(|| "y3"), || {
            let mut t0 = *u.get_value().get()?;
            t0.sub_assign(a.get_value().get()?);
            t0.sub_assign(b.get_value().get()?);

            let mut t1 = E::Fr::one();
            t1.sub_assign(c.get_value().get()?);

            match t1.inverse() {
                Some(t1) => {
                    t0.mul_assign(&t1);

                    Ok(t0)
                }
                None => Err(SynthesisError::DivisionByZero),
            }
        })?;

        cs.enforce(
            || "y3 computation",
            |lc| lc + one - c.get_variable(),
            |lc| lc + y3.get_variable(),
            |lc| lc + u.get_variable() - a.get_variable() - b.get_variable(),
        );

        Ok(EdwardsPoint { x: x3, y: y3 })
    }

    pub fn is_not_small_order<CS>(
        &self,
        mut cs: CS,
        params: &E::Params,
    ) -> Result<Boolean, SynthesisError>
    where
        CS: ConstraintSystem<E>
    {
        let tmp = self.double(cs.namespace(|| "first doubling"), params)?;
        let tmp = tmp.double(cs.namespace(|| "second doubling"), params)?;
        let tmp = tmp.double(cs.namespace(|| "third doubling"), params)?;
    
        // (0, -1) is a small order point, but won't ever appear here
        // because cofactor is 2^3, and we performed three doublings.
        // (0, 1) is the neutral element, so checking if x is nonzero
        // is sufficient to prevent small order points here.
        let is_zero = Expression::equals(
            cs.namespace(|| "x==0"),
            Expression::from(tmp.get_x()),
            Expression::u64::<CS>(0),
        )?;
    
        Ok(Boolean::from(is_zero).not())
    }
}

pub struct MontgomeryPoint<E: Engine> {
    x: Num<E>,
    y: Num<E>,
}

impl<E: JubjubEngine> MontgomeryPoint<E> {
    /// Converts an element in the prime order subgroup into
    /// a point in the birationally equivalent twisted
    /// Edwards curve.
    pub fn into_edwards<CS>(
        &self,
        mut cs: CS,
        params: &E::Params,
    ) -> Result<EdwardsPoint<E>, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        // Compute u = (scale*x) / y
        let u = AllocatedNum::alloc(cs.namespace(|| "u"), || {
            let mut t0 = *self.x.get_value().get()?;
            t0.mul_assign(params.scale());

            match self.y.get_value().get()?.inverse() {
                Some(invy) => {
                    t0.mul_assign(&invy);

                    Ok(t0)
                }
                None => Err(SynthesisError::DivisionByZero),
            }
        })?;

        cs.enforce(
            || "u computation",
            |lc| lc + &self.y.lc(E::Fr::one()),
            |lc| lc + u.get_variable(),
            |lc| lc + &self.x.lc(*params.scale()),
        );

        // Compute v = (x - 1) / (x + 1)
        let v = AllocatedNum::alloc(cs.namespace(|| "v"), || {
            let mut t0 = *self.x.get_value().get()?;
            let mut t1 = t0;
            t0.sub_assign(&E::Fr::one());
            t1.add_assign(&E::Fr::one());

            match t1.inverse() {
                Some(t1) => {
                    t0.mul_assign(&t1);

                    Ok(t0)
                }
                None => Err(SynthesisError::DivisionByZero),
            }
        })?;

        let one = CS::one();
        cs.enforce(
            || "v computation",
            |lc| lc + &self.x.lc(E::Fr::one()) + one,
            |lc| lc + v.get_variable(),
            |lc| lc + &self.x.lc(E::Fr::one()) - one,
        );

        Ok(EdwardsPoint { x: u, y: v })
    }

    /// Interprets an (x, y) pair as a point
    /// in Montgomery, does not check that it's
    /// on the curve. Useful for constants and
    /// window table lookups.
    pub fn interpret_unchecked(x: Num<E>, y: Num<E>) -> Self {
        MontgomeryPoint { x, y }
    }

    /// Performs an affine point addition, not defined for
    /// coincident points.
    pub fn add<CS>(
        &self,
        mut cs: CS,
        other: &Self,
        params: &E::Params,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        // Compute lambda = (y' - y) / (x' - x)
        let lambda = AllocatedNum::alloc(cs.namespace(|| "lambda"), || {
            let mut n = *other.y.get_value().get()?;
            n.sub_assign(self.y.get_value().get()?);

            let mut d = *other.x.get_value().get()?;
            d.sub_assign(self.x.get_value().get()?);

            match d.inverse() {
                Some(d) => {
                    n.mul_assign(&d);
                    Ok(n)
                }
                None => Err(SynthesisError::DivisionByZero),
            }
        })?;

        cs.enforce(
            || "evaluate lambda",
            |lc| lc + &other.x.lc(E::Fr::one()) - &self.x.lc(E::Fr::one()),
            |lc| lc + lambda.get_variable(),
            |lc| lc + &other.y.lc(E::Fr::one()) - &self.y.lc(E::Fr::one()),
        );

        // Compute x'' = lambda^2 - A - x - x'
        let xprime = AllocatedNum::alloc(cs.namespace(|| "xprime"), || {
            let mut t0 = *lambda.get_value().get()?;
            t0.square();
            t0.sub_assign(params.montgomery_a());
            t0.sub_assign(self.x.get_value().get()?);
            t0.sub_assign(other.x.get_value().get()?);

            Ok(t0)
        })?;

        // (lambda) * (lambda) = (A + x + x' + x'')
        let one = CS::one();
        cs.enforce(
            || "evaluate xprime",
            |lc| lc + lambda.get_variable(),
            |lc| lc + lambda.get_variable(),
            |lc| {
                lc + (*params.montgomery_a(), one)
                    + &self.x.lc(E::Fr::one())
                    + &other.x.lc(E::Fr::one())
                    + xprime.get_variable()
            },
        );

        // Compute y' = -(y + lambda(x' - x))
        let yprime = AllocatedNum::alloc(cs.namespace(|| "yprime"), || {
            let mut t0 = *xprime.get_value().get()?;
            t0.sub_assign(self.x.get_value().get()?);
            t0.mul_assign(lambda.get_value().get()?);
            t0.add_assign(self.y.get_value().get()?);
            t0.negate();

            Ok(t0)
        })?;

        // y' + y = lambda(x - x')
        cs.enforce(
            || "evaluate yprime",
            |lc| lc + &self.x.lc(E::Fr::one()) - xprime.get_variable(),
            |lc| lc + lambda.get_variable(),
            |lc| lc + yprime.get_variable() + &self.y.lc(E::Fr::one()),
        );

        Ok(MontgomeryPoint {
            x: xprime.into(),
            y: yprime.into(),
        })
    }
}

#[cfg(test)]
mod test {
    use super::super::boolean::{AllocatedBit, Boolean};
    use super::{fixed_base_multiplication, AllocatedNum, EdwardsPoint, MontgomeryPoint};
    use bellman::pairing::bls12_381::{Bls12, Fr};
    use bellman::pairing::ff::{BitIterator, Field, PrimeField};
    use bellman::ConstraintSystem;
    use circuit::test::*;
    use jubjub::fs::Fs;
    use jubjub::{edwards, montgomery, FixedGenerators, JubjubBls12, JubjubParams};
    use rand::{Rand, Rng, SeedableRng, XorShiftRng};

    #[test]
    fn test_into_edwards() {
        let params = &JubjubBls12::new();
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for _ in 0..100 {
            let mut cs = TestConstraintSystem::<Bls12>::new();

            let p = montgomery::Point::<Bls12, _>::rand(rng, params);
            let (u, v) = edwards::Point::from_montgomery(&p, params).into_xy();
            let (x, y) = p.into_xy().unwrap();

            let numx = AllocatedNum::alloc(cs.namespace(|| "mont x"), || Ok(x)).unwrap();
            let numy = AllocatedNum::alloc(cs.namespace(|| "mont y"), || Ok(y)).unwrap();

            let p = MontgomeryPoint::interpret_unchecked(numx.into(), numy.into());

            let q = p.into_edwards(&mut cs, params).unwrap();

            assert!(cs.is_satisfied());
            assert!(q.x.get_value().unwrap() == u);
            assert!(q.y.get_value().unwrap() == v);

            cs.set("u/num", rng.gen());
            assert_eq!(cs.which_is_unsatisfied().unwrap(), "u computation");
            cs.set("u/num", u);
            assert!(cs.is_satisfied());

            cs.set("v/num", rng.gen());
            assert_eq!(cs.which_is_unsatisfied().unwrap(), "v computation");
            cs.set("v/num", v);
            assert!(cs.is_satisfied());
        }
    }

    #[test]
    fn test_interpret() {
        let params = &JubjubBls12::new();
        let rng = &mut XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for _ in 0..100 {
            let p = edwards::Point::<Bls12, _>::rand(rng, &params);

            let mut cs = TestConstraintSystem::<Bls12>::new();
            let q = EdwardsPoint::witness(&mut cs, Some(p.clone()), &params).unwrap();

            let p = p.into_xy();

            assert!(cs.is_satisfied());
            assert_eq!(q.x.get_value().unwrap(), p.0);
            assert_eq!(q.y.get_value().unwrap(), p.1);
        }

        for _ in 0..100 {
            let p = edwards::Point::<Bls12, _>::rand(rng, &params);
            let (x, y) = p.into_xy();

            let mut cs = TestConstraintSystem::<Bls12>::new();
            let numx = AllocatedNum::alloc(cs.namespace(|| "x"), || Ok(x)).unwrap();
            let numy = AllocatedNum::alloc(cs.namespace(|| "y"), || Ok(y)).unwrap();

            let p = EdwardsPoint::interpret(&mut cs, &numx, &numy, &params).unwrap();

            assert!(cs.is_satisfied());
            assert_eq!(p.x.get_value().unwrap(), x);
            assert_eq!(p.y.get_value().unwrap(), y);
        }

        // Random (x, y) are unlikely to be on the curve.
        for _ in 0..100 {
            let x = rng.gen();
            let y = rng.gen();

            let mut cs = TestConstraintSystem::<Bls12>::new();
            let numx = AllocatedNum::alloc(cs.namespace(|| "x"), || Ok(x)).unwrap();
            let numy = AllocatedNum::alloc(cs.namespace(|| "y"), || Ok(y)).unwrap();

            EdwardsPoint::interpret(&mut cs, &numx, &numy, &params).unwrap();

            assert_eq!(cs.which_is_unsatisfied().unwrap(), "on curve check");
        }
    }

    #[test]
    fn test_edwards_fixed_base_multiplication() {
        let params = &JubjubBls12::new();
        let rng = &mut XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for _ in 0..100 {
            let mut cs = TestConstraintSystem::<Bls12>::new();

            let p = params.generator(FixedGenerators::NoteCommitmentRandomness);
            let s = Fs::rand(rng);
            let q = p.mul(s, params);
            let (x1, y1) = q.into_xy();

            let mut s_bits = BitIterator::new(s.into_repr()).collect::<Vec<_>>();
            s_bits.reverse();
            s_bits.truncate(Fs::NUM_BITS as usize);

            let s_bits = s_bits
                .into_iter()
                .enumerate()
                .map(|(i, b)| {
                    AllocatedBit::alloc(cs.namespace(|| format!("scalar bit {}", i)), Some(b))
                        .unwrap()
                })
                .map(|v| Boolean::from(v))
                .collect::<Vec<_>>();

            let q = fixed_base_multiplication(
                cs.namespace(|| "multiplication"),
                FixedGenerators::NoteCommitmentRandomness,
                &s_bits,
                params,
            )
            .unwrap();

            assert_eq!(q.x.get_value().unwrap(), x1);
            assert_eq!(q.y.get_value().unwrap(), y1);
        }
    }

    #[test]
    fn test_edwards_multiplication() {
        let params = &JubjubBls12::new();
        let rng = &mut XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for _ in 0..100 {
            let mut cs = TestConstraintSystem::<Bls12>::new();

            let p = edwards::Point::<Bls12, _>::rand(rng, params);
            let s = Fs::rand(rng);
            let q = p.mul(s, params);

            let (x0, y0) = p.into_xy();
            let (x1, y1) = q.into_xy();

            let num_x0 = AllocatedNum::alloc(cs.namespace(|| "x0"), || Ok(x0)).unwrap();
            let num_y0 = AllocatedNum::alloc(cs.namespace(|| "y0"), || Ok(y0)).unwrap();

            let p = EdwardsPoint {
                x: num_x0,
                y: num_y0,
            };

            let mut s_bits = BitIterator::new(s.into_repr()).collect::<Vec<_>>();
            s_bits.reverse();
            s_bits.truncate(Fs::NUM_BITS as usize);

            let s_bits = s_bits
                .into_iter()
                .enumerate()
                .map(|(i, b)| {
                    AllocatedBit::alloc(cs.namespace(|| format!("scalar bit {}", i)), Some(b))
                        .unwrap()
                })
                .map(|v| Boolean::from(v))
                .collect::<Vec<_>>();

            let q = p
                .mul(cs.namespace(|| "scalar mul"), &s_bits, params)
                .unwrap();

            assert!(cs.is_satisfied());

            assert_eq!(q.x.get_value().unwrap(), x1);

            assert_eq!(q.y.get_value().unwrap(), y1);
        }
    }

    #[test]
    fn test_conditionally_select() {
        let params = &JubjubBls12::new();
        let rng = &mut XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for _ in 0..1000 {
            let mut cs = TestConstraintSystem::<Bls12>::new();

            let p = edwards::Point::<Bls12, _>::rand(rng, params);

            let (x0, y0) = p.into_xy();

            let num_x0 = AllocatedNum::alloc(cs.namespace(|| "x0"), || Ok(x0)).unwrap();
            let num_y0 = AllocatedNum::alloc(cs.namespace(|| "y0"), || Ok(y0)).unwrap();

            let p = EdwardsPoint {
                x: num_x0,
                y: num_y0,
            };

            let mut should_we_select = rng.gen();

            // Conditionally allocate
            let mut b = if rng.gen() {
                Boolean::from(
                    AllocatedBit::alloc(cs.namespace(|| "condition"), Some(should_we_select))
                        .unwrap(),
                )
            } else {
                Boolean::constant(should_we_select)
            };

            // Conditionally negate
            if rng.gen() {
                b = b.not();
                should_we_select = !should_we_select;
            }

            let q = p
                .conditionally_select(cs.namespace(|| "select"), &b)
                .unwrap();

            assert!(cs.is_satisfied());

            if should_we_select {
                assert_eq!(q.x.get_value().unwrap(), x0);
                assert_eq!(q.y.get_value().unwrap(), y0);

                cs.set("select/y'/num", Fr::one());
                assert_eq!(cs.which_is_unsatisfied().unwrap(), "select/y' computation");
                cs.set("select/x'/num", Fr::zero());
                assert_eq!(cs.which_is_unsatisfied().unwrap(), "select/x' computation");
            } else {
                assert_eq!(q.x.get_value().unwrap(), Fr::zero());
                assert_eq!(q.y.get_value().unwrap(), Fr::one());

                cs.set("select/y'/num", x0);
                assert_eq!(cs.which_is_unsatisfied().unwrap(), "select/y' computation");
                cs.set("select/x'/num", y0);
                assert_eq!(cs.which_is_unsatisfied().unwrap(), "select/x' computation");
            }
        }
    }

    #[test]
    fn test_edwards_addition() {
        let params = &JubjubBls12::new();
        let rng = &mut XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for _ in 0..100 {
            let p1 = edwards::Point::<Bls12, _>::rand(rng, params);
            let p2 = edwards::Point::<Bls12, _>::rand(rng, params);

            let p3 = p1.add(&p2, params);

            let (x0, y0) = p1.into_xy();
            let (x1, y1) = p2.into_xy();
            let (x2, y2) = p3.into_xy();

            let mut cs = TestConstraintSystem::<Bls12>::new();

            let num_x0 = AllocatedNum::alloc(cs.namespace(|| "x0"), || Ok(x0)).unwrap();
            let num_y0 = AllocatedNum::alloc(cs.namespace(|| "y0"), || Ok(y0)).unwrap();

            let num_x1 = AllocatedNum::alloc(cs.namespace(|| "x1"), || Ok(x1)).unwrap();
            let num_y1 = AllocatedNum::alloc(cs.namespace(|| "y1"), || Ok(y1)).unwrap();

            let p1 = EdwardsPoint {
                x: num_x0,
                y: num_y0,
            };

            let p2 = EdwardsPoint {
                x: num_x1,
                y: num_y1,
            };

            let p3 = p1.add(cs.namespace(|| "addition"), &p2, params).unwrap();

            assert!(cs.is_satisfied());

            assert!(p3.x.get_value().unwrap() == x2);
            assert!(p3.y.get_value().unwrap() == y2);

            let u = cs.get("addition/U/num");
            cs.set("addition/U/num", rng.gen());
            assert_eq!(cs.which_is_unsatisfied(), Some("addition/U computation"));
            cs.set("addition/U/num", u);
            assert!(cs.is_satisfied());

            let x3 = cs.get("addition/x3/num");
            cs.set("addition/x3/num", rng.gen());
            assert_eq!(cs.which_is_unsatisfied(), Some("addition/x3 computation"));
            cs.set("addition/x3/num", x3);
            assert!(cs.is_satisfied());

            let y3 = cs.get("addition/y3/num");
            cs.set("addition/y3/num", rng.gen());
            assert_eq!(cs.which_is_unsatisfied(), Some("addition/y3 computation"));
            cs.set("addition/y3/num", y3);
            assert!(cs.is_satisfied());
        }
    }

    #[test]
    fn test_edwards_doubling() {
        let params = &JubjubBls12::new();
        let rng = &mut XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for _ in 0..100 {
            let p1 = edwards::Point::<Bls12, _>::rand(rng, params);
            let p2 = p1.double(params);

            let (x0, y0) = p1.into_xy();
            let (x1, y1) = p2.into_xy();

            let mut cs = TestConstraintSystem::<Bls12>::new();

            let num_x0 = AllocatedNum::alloc(cs.namespace(|| "x0"), || Ok(x0)).unwrap();
            let num_y0 = AllocatedNum::alloc(cs.namespace(|| "y0"), || Ok(y0)).unwrap();

            let p1 = EdwardsPoint {
                x: num_x0,
                y: num_y0,
            };

            let p2 = p1.double(cs.namespace(|| "doubling"), params).unwrap();

            assert!(cs.is_satisfied());

            assert!(p2.x.get_value().unwrap() == x1);
            assert!(p2.y.get_value().unwrap() == y1);
        }
    }

    #[test]
    fn test_montgomery_addition() {
        let params = &JubjubBls12::new();
        let rng = &mut XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for _ in 0..100 {
            let p1 = loop {
                let x: Fr = rng.gen();
                let s: bool = rng.gen();

                if let Some(p) = montgomery::Point::<Bls12, _>::get_for_x(x, s, params) {
                    break p;
                }
            };

            let p2 = loop {
                let x: Fr = rng.gen();
                let s: bool = rng.gen();

                if let Some(p) = montgomery::Point::<Bls12, _>::get_for_x(x, s, params) {
                    break p;
                }
            };

            let p3 = p1.add(&p2, params);

            let (x0, y0) = p1.into_xy().unwrap();
            let (x1, y1) = p2.into_xy().unwrap();
            let (x2, y2) = p3.into_xy().unwrap();

            let mut cs = TestConstraintSystem::<Bls12>::new();

            let num_x0 = AllocatedNum::alloc(cs.namespace(|| "x0"), || Ok(x0)).unwrap();
            let num_y0 = AllocatedNum::alloc(cs.namespace(|| "y0"), || Ok(y0)).unwrap();

            let num_x1 = AllocatedNum::alloc(cs.namespace(|| "x1"), || Ok(x1)).unwrap();
            let num_y1 = AllocatedNum::alloc(cs.namespace(|| "y1"), || Ok(y1)).unwrap();

            let p1 = MontgomeryPoint {
                x: num_x0.into(),
                y: num_y0.into(),
            };

            let p2 = MontgomeryPoint {
                x: num_x1.into(),
                y: num_y1.into(),
            };

            let p3 = p1.add(cs.namespace(|| "addition"), &p2, params).unwrap();

            assert!(cs.is_satisfied());

            assert!(p3.x.get_value().unwrap() == x2);
            assert!(p3.y.get_value().unwrap() == y2);

            cs.set("addition/yprime/num", rng.gen());
            assert_eq!(cs.which_is_unsatisfied(), Some("addition/evaluate yprime"));
            cs.set("addition/yprime/num", y2);
            assert!(cs.is_satisfied());

            cs.set("addition/xprime/num", rng.gen());
            assert_eq!(cs.which_is_unsatisfied(), Some("addition/evaluate xprime"));
            cs.set("addition/xprime/num", x2);
            assert!(cs.is_satisfied());

            cs.set("addition/lambda/num", rng.gen());
            assert_eq!(cs.which_is_unsatisfied(), Some("addition/evaluate lambda"));
        }
    }
}

#[cfg(test)]
mod baby_test {
    use alt_babyjubjub::fs::Fs;
    use alt_babyjubjub::{edwards, montgomery, AltJubjubBn256, FixedGenerators, JubjubParams};
    use bellman::pairing::bn256::{Bn256, Fr};
    use bellman::pairing::ff::{BitIterator, Field, PrimeField};
    use bellman::ConstraintSystem;
    use circuit::test::*;
    use rand::{Rand, Rng, SeedableRng, XorShiftRng};

    use super::super::boolean::{AllocatedBit, Boolean};
    use super::{fixed_base_multiplication, AllocatedNum, EdwardsPoint, MontgomeryPoint};

    #[test]
    fn test_into_edwards() {
        let params = &AltJubjubBn256::new();
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for _ in 0..100 {
            let mut cs = TestConstraintSystem::<Bn256>::new();

            let p = montgomery::Point::<Bn256, _>::rand(rng, params);
            let (u, v) = edwards::Point::from_montgomery(&p, params).into_xy();
            let (x, y) = p.into_xy().unwrap();

            let numx = AllocatedNum::alloc(cs.namespace(|| "mont x"), || Ok(x)).unwrap();
            let numy = AllocatedNum::alloc(cs.namespace(|| "mont y"), || Ok(y)).unwrap();

            let p = MontgomeryPoint::interpret_unchecked(numx.into(), numy.into());

            let q = p.into_edwards(&mut cs, params).unwrap();

            assert!(cs.is_satisfied());
            assert!(q.x.get_value().unwrap() == u);
            assert!(q.y.get_value().unwrap() == v);

            cs.set("u/num", rng.gen());
            assert_eq!(cs.which_is_unsatisfied().unwrap(), "u computation");
            cs.set("u/num", u);
            assert!(cs.is_satisfied());

            cs.set("v/num", rng.gen());
            assert_eq!(cs.which_is_unsatisfied().unwrap(), "v computation");
            cs.set("v/num", v);
            assert!(cs.is_satisfied());
        }
    }

    #[test]
    fn test_interpret() {
        let params = &AltJubjubBn256::new();
        let rng = &mut XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for _ in 0..100 {
            let p = edwards::Point::<Bn256, _>::rand(rng, &params);

            let mut cs = TestConstraintSystem::<Bn256>::new();
            let q = EdwardsPoint::witness(&mut cs, Some(p.clone()), &params).unwrap();

            let p = p.into_xy();

            assert!(cs.is_satisfied());
            assert_eq!(q.x.get_value().unwrap(), p.0);
            assert_eq!(q.y.get_value().unwrap(), p.1);
        }

        for _ in 0..100 {
            let p = edwards::Point::<Bn256, _>::rand(rng, &params);
            let (x, y) = p.into_xy();

            let mut cs = TestConstraintSystem::<Bn256>::new();
            let numx = AllocatedNum::alloc(cs.namespace(|| "x"), || Ok(x)).unwrap();
            let numy = AllocatedNum::alloc(cs.namespace(|| "y"), || Ok(y)).unwrap();

            let p = EdwardsPoint::interpret(&mut cs, &numx, &numy, &params).unwrap();

            assert!(cs.is_satisfied());
            assert_eq!(p.x.get_value().unwrap(), x);
            assert_eq!(p.y.get_value().unwrap(), y);
        }

        // Random (x, y) are unlikely to be on the curve.
        for _ in 0..100 {
            let x = rng.gen();
            let y = rng.gen();

            let mut cs = TestConstraintSystem::<Bn256>::new();
            let numx = AllocatedNum::alloc(cs.namespace(|| "x"), || Ok(x)).unwrap();
            let numy = AllocatedNum::alloc(cs.namespace(|| "y"), || Ok(y)).unwrap();

            EdwardsPoint::interpret(&mut cs, &numx, &numy, &params).unwrap();

            assert_eq!(cs.which_is_unsatisfied().unwrap(), "on curve check");
        }
    }

    #[test]
    fn test_recover_from_y() {
        let params = &AltJubjubBn256::new();
        let rng = &mut XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for i in 0..100 {
            let mut cs = TestConstraintSystem::<Bn256>::new();

            let y_cord: Fr = rng.gen();
            let point = edwards::Point::<Bn256, _>::get_for_y(y_cord, true, params);
            if point == None {
                let q_y =
                    AllocatedNum::alloc(cs.namespace(|| format!("corrupted_y : {}", i)), || {
                        Ok(y_cord)
                    })
                    .unwrap();
                let (point, sucess) = EdwardsPoint::recover_from_y_unchecked(
                    cs.namespace(|| format!("recover :{}", i)),
                    &Boolean::constant(true),
                    &q_y,
                    &params,
                )
                .unwrap();
                assert!(cs.is_satisfied());
                assert_eq!(sucess.get_value().unwrap(), false, "iteration: i: {}", i);
            }
        }

        for i in 0..100 {
            let p = edwards::Point::<Bn256, _>::rand(rng, &params);

            let mut cs = TestConstraintSystem::<Bn256>::new();
            let q = EdwardsPoint::witness(&mut cs, Some(p.clone()), &params).unwrap();

            let q_x = q.get_x();
            let q_x_bits = q_x
                .into_bits_le(cs.namespace(|| format!("q_x : {}", i)))
                .unwrap();

            let p = p.into_xy();

            assert!(cs.is_satisfied());
            assert_eq!(q.x.get_value().unwrap(), p.0);
            assert_eq!(q.y.get_value().unwrap(), p.1);

            let (point, sucess) = EdwardsPoint::recover_from_y_unchecked(
                cs.namespace(|| format!("recover :{}", i)),
                &q_x_bits[0],
                q.get_y(),
                &params,
            )
            .unwrap();
            assert!(cs.is_satisfied());
            assert_eq!(point.y.get_value().unwrap(), p.1);
            assert_eq!(point.x.get_value().unwrap(), p.0);
            assert_eq!(sucess.get_value().unwrap(), true);
        }
    }

    #[test]
    fn test_edwards_fixed_base_multiplication() {
        let params = &AltJubjubBn256::new();
        let rng = &mut XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for _ in 0..100 {
            let mut cs = TestConstraintSystem::<Bn256>::new();

            let p = params.generator(FixedGenerators::NoteCommitmentRandomness);
            let s = Fs::rand(rng);
            let q = p.mul(s, params);
            let (x1, y1) = q.into_xy();

            let mut s_bits = BitIterator::new(s.into_repr()).collect::<Vec<_>>();
            s_bits.reverse();
            s_bits.truncate(Fs::NUM_BITS as usize);

            let s_bits = s_bits
                .into_iter()
                .enumerate()
                .map(|(i, b)| {
                    AllocatedBit::alloc(cs.namespace(|| format!("scalar bit {}", i)), Some(b))
                        .unwrap()
                })
                .map(|v| Boolean::from(v))
                .collect::<Vec<_>>();

            let q = fixed_base_multiplication(
                cs.namespace(|| "multiplication"),
                FixedGenerators::NoteCommitmentRandomness,
                &s_bits,
                params,
            )
            .unwrap();

            assert_eq!(q.x.get_value().unwrap(), x1);
            assert_eq!(q.y.get_value().unwrap(), y1);
        }
    }

    #[test]
    fn test_edwards_multiplication() {
        let params = &AltJubjubBn256::new();
        let rng = &mut XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for _ in 0..100 {
            let mut cs = TestConstraintSystem::<Bn256>::new();

            let p = edwards::Point::<Bn256, _>::rand(rng, params);
            let s = Fs::rand(rng);
            let q = p.mul(s, params);

            let (x0, y0) = p.into_xy();
            let (x1, y1) = q.into_xy();

            let num_x0 = AllocatedNum::alloc(cs.namespace(|| "x0"), || Ok(x0)).unwrap();
            let num_y0 = AllocatedNum::alloc(cs.namespace(|| "y0"), || Ok(y0)).unwrap();

            let p = EdwardsPoint {
                x: num_x0,
                y: num_y0,
            };

            let mut s_bits = BitIterator::new(s.into_repr()).collect::<Vec<_>>();
            s_bits.reverse();
            s_bits.truncate(Fs::NUM_BITS as usize);

            let s_bits = s_bits
                .into_iter()
                .enumerate()
                .map(|(i, b)| {
                    AllocatedBit::alloc(cs.namespace(|| format!("scalar bit {}", i)), Some(b))
                        .unwrap()
                })
                .map(|v| Boolean::from(v))
                .collect::<Vec<_>>();

            let q = p
                .mul(cs.namespace(|| "scalar mul"), &s_bits, params)
                .unwrap();

            assert!(cs.is_satisfied());

            assert_eq!(q.x.get_value().unwrap(), x1);

            assert_eq!(q.y.get_value().unwrap(), y1);
        }
    }

    #[test]
    fn test_conditionally_select() {
        let params = &AltJubjubBn256::new();
        let rng = &mut XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for _ in 0..1000 {
            let mut cs = TestConstraintSystem::<Bn256>::new();

            let p = edwards::Point::<Bn256, _>::rand(rng, params);

            let (x0, y0) = p.into_xy();

            let num_x0 = AllocatedNum::alloc(cs.namespace(|| "x0"), || Ok(x0)).unwrap();
            let num_y0 = AllocatedNum::alloc(cs.namespace(|| "y0"), || Ok(y0)).unwrap();

            let p = EdwardsPoint {
                x: num_x0,
                y: num_y0,
            };

            let mut should_we_select = rng.gen();

            // Conditionally allocate
            let mut b = if rng.gen() {
                Boolean::from(
                    AllocatedBit::alloc(cs.namespace(|| "condition"), Some(should_we_select))
                        .unwrap(),
                )
            } else {
                Boolean::constant(should_we_select)
            };

            // Conditionally negate
            if rng.gen() {
                b = b.not();
                should_we_select = !should_we_select;
            }

            let q = p
                .conditionally_select(cs.namespace(|| "select"), &b)
                .unwrap();

            assert!(cs.is_satisfied());

            if should_we_select {
                assert_eq!(q.x.get_value().unwrap(), x0);
                assert_eq!(q.y.get_value().unwrap(), y0);

                cs.set("select/y'/num", Fr::one());
                assert_eq!(cs.which_is_unsatisfied().unwrap(), "select/y' computation");
                cs.set("select/x'/num", Fr::zero());
                assert_eq!(cs.which_is_unsatisfied().unwrap(), "select/x' computation");
            } else {
                assert_eq!(q.x.get_value().unwrap(), Fr::zero());
                assert_eq!(q.y.get_value().unwrap(), Fr::one());

                cs.set("select/y'/num", x0);
                assert_eq!(cs.which_is_unsatisfied().unwrap(), "select/y' computation");
                cs.set("select/x'/num", y0);
                assert_eq!(cs.which_is_unsatisfied().unwrap(), "select/x' computation");
            }
        }
    }

    #[test]
    fn test_edwards_addition() {
        let params = &AltJubjubBn256::new();
        let rng = &mut XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for _ in 0..100 {
            let p1 = edwards::Point::<Bn256, _>::rand(rng, params);
            let p2 = edwards::Point::<Bn256, _>::rand(rng, params);

            let p3 = p1.add(&p2, params);

            let (x0, y0) = p1.into_xy();
            let (x1, y1) = p2.into_xy();
            let (x2, y2) = p3.into_xy();

            let mut cs = TestConstraintSystem::<Bn256>::new();

            let num_x0 = AllocatedNum::alloc(cs.namespace(|| "x0"), || Ok(x0)).unwrap();
            let num_y0 = AllocatedNum::alloc(cs.namespace(|| "y0"), || Ok(y0)).unwrap();

            let num_x1 = AllocatedNum::alloc(cs.namespace(|| "x1"), || Ok(x1)).unwrap();
            let num_y1 = AllocatedNum::alloc(cs.namespace(|| "y1"), || Ok(y1)).unwrap();

            let p1 = EdwardsPoint {
                x: num_x0,
                y: num_y0,
            };

            let p2 = EdwardsPoint {
                x: num_x1,
                y: num_y1,
            };

            let p3 = p1.add(cs.namespace(|| "addition"), &p2, params).unwrap();

            assert!(cs.is_satisfied());

            assert!(p3.x.get_value().unwrap() == x2);
            assert!(p3.y.get_value().unwrap() == y2);

            let u = cs.get("addition/U/num");
            cs.set("addition/U/num", rng.gen());
            assert_eq!(cs.which_is_unsatisfied(), Some("addition/U computation"));
            cs.set("addition/U/num", u);
            assert!(cs.is_satisfied());

            let x3 = cs.get("addition/x3/num");
            cs.set("addition/x3/num", rng.gen());
            assert_eq!(cs.which_is_unsatisfied(), Some("addition/x3 computation"));
            cs.set("addition/x3/num", x3);
            assert!(cs.is_satisfied());

            let y3 = cs.get("addition/y3/num");
            cs.set("addition/y3/num", rng.gen());
            assert_eq!(cs.which_is_unsatisfied(), Some("addition/y3 computation"));
            cs.set("addition/y3/num", y3);
            assert!(cs.is_satisfied());
        }
    }

    #[test]
    fn test_edwards_doubling() {
        let params = &AltJubjubBn256::new();
        let rng = &mut XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for _ in 0..100 {
            let p1 = edwards::Point::<Bn256, _>::rand(rng, params);
            let p2 = p1.double(params);

            let (x0, y0) = p1.into_xy();
            let (x1, y1) = p2.into_xy();

            let mut cs = TestConstraintSystem::<Bn256>::new();

            let num_x0 = AllocatedNum::alloc(cs.namespace(|| "x0"), || Ok(x0)).unwrap();
            let num_y0 = AllocatedNum::alloc(cs.namespace(|| "y0"), || Ok(y0)).unwrap();

            let p1 = EdwardsPoint {
                x: num_x0,
                y: num_y0,
            };

            let p2 = p1.double(cs.namespace(|| "doubling"), params).unwrap();

            assert!(cs.is_satisfied());

            assert!(p2.x.get_value().unwrap() == x1);
            assert!(p2.y.get_value().unwrap() == y1);
        }
    }

    #[test]
    fn test_montgomery_addition() {
        let params = &AltJubjubBn256::new();
        let rng = &mut XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for _ in 0..100 {
            let p1 = loop {
                let x: Fr = rng.gen();
                let s: bool = rng.gen();

                if let Some(p) = montgomery::Point::<Bn256, _>::get_for_x(x, s, params) {
                    break p;
                }
            };

            let p2 = loop {
                let x: Fr = rng.gen();
                let s: bool = rng.gen();

                if let Some(p) = montgomery::Point::<Bn256, _>::get_for_x(x, s, params) {
                    break p;
                }
            };

            let p3 = p1.add(&p2, params);

            let (x0, y0) = p1.into_xy().unwrap();
            let (x1, y1) = p2.into_xy().unwrap();
            let (x2, y2) = p3.into_xy().unwrap();

            let mut cs = TestConstraintSystem::<Bn256>::new();

            let num_x0 = AllocatedNum::alloc(cs.namespace(|| "x0"), || Ok(x0)).unwrap();
            let num_y0 = AllocatedNum::alloc(cs.namespace(|| "y0"), || Ok(y0)).unwrap();

            let num_x1 = AllocatedNum::alloc(cs.namespace(|| "x1"), || Ok(x1)).unwrap();
            let num_y1 = AllocatedNum::alloc(cs.namespace(|| "y1"), || Ok(y1)).unwrap();

            let p1 = MontgomeryPoint {
                x: num_x0.into(),
                y: num_y0.into(),
            };

            let p2 = MontgomeryPoint {
                x: num_x1.into(),
                y: num_y1.into(),
            };

            let p3 = p1.add(cs.namespace(|| "addition"), &p2, params).unwrap();

            assert!(cs.is_satisfied());

            assert!(p3.x.get_value().unwrap() == x2);
            assert!(p3.y.get_value().unwrap() == y2);

            cs.set("addition/yprime/num", rng.gen());
            assert_eq!(cs.which_is_unsatisfied(), Some("addition/evaluate yprime"));
            cs.set("addition/yprime/num", y2);
            assert!(cs.is_satisfied());

            cs.set("addition/xprime/num", rng.gen());
            assert_eq!(cs.which_is_unsatisfied(), Some("addition/evaluate xprime"));
            cs.set("addition/xprime/num", x2);
            assert!(cs.is_satisfied());

            cs.set("addition/lambda/num", rng.gen());
            assert_eq!(cs.which_is_unsatisfied(), Some("addition/evaluate lambda"));
        }
    }
}
