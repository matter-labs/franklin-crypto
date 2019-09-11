use super::boolean::AllocatedBit;
use super::boolean::Boolean;
use super::num::AllocatedNum;
use super::num::Num;
use bellman::pairing::ff::PrimeFieldRepr;
use bellman::pairing::ff::{BitIterator, Field, PrimeField};
use bellman::pairing::Engine;
use bellman::{ConstraintSystem, LinearCombination, Namespace, SynthesisError};
use circuit::boolean;
use circuit::Assignment;
use std::ops::{Add, Sub};

#[derive(Clone)]
pub struct Expression<E: Engine> {
    value: Option<E::Fr>,
    lc: LinearCombination<E>,
}

impl<E: Engine> Expression<E> {
    pub fn new(value: Option<E::Fr>, lc: LinearCombination<E>) -> Expression<E> {
        Expression {
            value: value,
            lc: lc,
        }
    }
    pub fn constant<CS: ConstraintSystem<E>>(value: E::Fr) -> Expression<E> {
        Expression {
            value: Some(value),
            lc: LinearCombination::<E>::zero() + (value, CS::one()),
        }
    }

    pub fn u64<CS: ConstraintSystem<E>>(number: u64) -> Expression<E> {
        let value = E::Fr::from_str(&number.to_string()).unwrap();
        Expression {
            value: Some(value),
            lc: LinearCombination::<E>::zero() + (value, CS::one()),
        }
    }
    pub fn boolean<CS: ConstraintSystem<E>>(boolean_var: Boolean) -> Expression<E> {
        Expression {
            value: boolean_var.get_value_field::<E>(),
            lc: boolean_var.lc(CS::one(), E::Fr::one()),
        }
    }
    pub fn le_bits<CS: ConstraintSystem<E>>(le_bits: &[Boolean]) -> Expression<E> {
        let mut data_from_lc = Num::<E>::zero();
        let mut coeff = E::Fr::one();
        for bit in le_bits {
            data_from_lc = data_from_lc.add_bool_with_coeff(CS::one(), &bit, coeff);
            coeff.double();
        }
        Self::from(&data_from_lc)
    }
}

impl<E: Engine> Expression<E> {
    pub fn get_value(&self) -> Option<E::Fr> {
        self.value
    }

    pub fn lc(&self) -> LinearCombination<E> {
        LinearCombination::zero() + (E::Fr::one(), &self.lc)
    }


    // returns a==b
    pub fn equals<CS, EX1, EX2>(
        mut cs: CS,
        a: EX1,
        b: EX2,
    ) -> Result<boolean::AllocatedBit, SynthesisError>
    where
        E: Engine,
        CS: ConstraintSystem<E>,
        EX1: Into<Expression<E>>,
        EX2: Into<Expression<E>>,
    {
        // Allocate and constrain `r`: result boolean bit.
        // It equals `true` if `a` equals `b`, `false` otherwise
        let a: Expression<E> = a.into();
        let b: Expression<E> = b.into();
        let r_value = match (a.get_value(), b.get_value()) {
            (Some(a), Some(b)) => Some(a == b),
            _ => None,
        };

        let r = boolean::AllocatedBit::alloc(cs.namespace(|| "r"), r_value)?;

        // Let `delta = a - b`

        let delta_value = match (a.get_value(), b.get_value()) {
            (Some(a), Some(b)) => {
                // return (a - b)
                let mut a = a;
                a.sub_assign(&b);
                Some(a)
            }
            _ => None,
        };

        let x_value = match (delta_value, r_value) {
            (Some(delta), Some(r)) => {
                if delta.is_zero() {
                    Some(E::Fr::one())
                } else {
                    let mut mult: E::Fr;
                    if r {
                        mult = E::Fr::one();
                    } else {
                        mult = E::Fr::zero();
                    }
                    mult.sub_assign(&E::Fr::one());
                    let mut temp = delta.inverse().unwrap();
                    temp.mul_assign(&mult);
                    Some(temp)
                }
            }
            _ => None,
        };

        let x = AllocatedNum::alloc(cs.namespace(|| "x"), || x_value.grab())?;

        // Constrain allocation:
        // 0 = (a - b) * r
        // thus if (a-b) != 0 then r == 0
        cs.enforce(
            || "0 = (a - b) * r",
            |zero| zero + &a.lc() - &b.lc(),
            |zero| zero + r.get_variable(),
            |zero| zero,
        );

        // Constrain:
        // (a-b) * x == r - 1
        // and thus `r` is 1 if `(a - b)` is zero (a != b )
        cs.enforce(
            || "(a - b) * x == r - 1",
            |zero| zero + &a.lc() - &b.lc(),
            |zero| zero + x.get_variable(),
            |zero| zero + r.get_variable() - CS::one(),
        );

        Ok(r)
    }

    /// Takes two expressions (a, b) and returns corresponding allocated numbers 
    /// (b_allocated, a_allocated) if the condition is true, and (a_allocated, b_allocated)
    /// otherwise.
    pub fn conditionally_reverse<CS, EX1, EX2>(
        mut cs: CS,
        a: EX1,
        b: EX2,
        condition: &Boolean,
    ) -> Result<(AllocatedNum<E>, AllocatedNum<E>), SynthesisError>
    where
        CS: ConstraintSystem<E>,
        EX1: Into<Expression<E>>,
        EX2: Into<Expression<E>>,
    {
        let a: Expression<E> = a.into();
        let b: Expression<E> = b.into();

        let c = AllocatedNum::alloc(cs.namespace(|| "conditional reversal result 1"), || {
            if *condition.get_value().get()? {
                Ok(*b.get_value().get()?)
            } else {
                Ok(*a.get_value().get()?)
            }
        })?;

        cs.enforce(
            || "first conditional reversal",
            |zero| zero + &a.lc() - &b.lc(),
            |_| condition.lc(CS::one(), E::Fr::one()),
            |zero| zero + &a.lc() - c.get_variable(),
        );

        let d = AllocatedNum::alloc(cs.namespace(|| "conditional reversal result 2"), || {
            if *condition.get_value().get()? {
                Ok(*a.get_value().get()?)
            } else {
                Ok(*b.get_value().get()?)
            }
        })?;

        cs.enforce(
            || "second conditional reversal",
            |zero| zero + &b.lc() - &a.lc(),
            |_| condition.lc(CS::one(), E::Fr::one()),
            |zero| zero + &b.lc() - d.get_variable(),
        );

        Ok((c, d))
    }

    /// Takes two expressions (a, b) and returns allocated result for 
    /// a if the condition is true, and b
    /// otherwise.
    /// Most often to be used with b = 0
    pub fn conditionally_select<CS, EX1, EX2>(
        mut cs: CS,
        a: EX1,
        b: EX2,
        condition: &Boolean,
    ) -> Result<AllocatedNum<E>, SynthesisError>
    where
        CS: ConstraintSystem<E>,
        EX1: Into<Expression<E>>,
        EX2: Into<Expression<E>>,
    {
        let a: Expression<E> = a.into();
        let b: Expression<E> = b.into();

        let a = a.into_number(cs.namespace(|| "pack A"))?;
        let b = b.into_number(cs.namespace(|| "pack B"))?;

        let c = AllocatedNum::alloc(cs.namespace(|| "conditional select result"), || {
            if *condition.get_value().get()? {
                Ok(*a.get_value().get()?)
            } else {
                Ok(*b.get_value().get()?)
            }
        })?;

        // a * condition + b*(1-condition) = c ->
        // a * condition - b*condition = c - b

        cs.enforce(
            || "conditional select constraint",
            |zero| zero + a.get_variable() - b.get_variable(),
            |_| condition.lc(CS::one(), E::Fr::one()),
            |zero| zero + c.get_variable() - b.get_variable(),
        );

        Ok(c)
    }

    /// Returns `a == b ? x : y`
    pub fn select_ifeq<CS, EX1, EX2, EX3, EX4>(
        mut cs: CS,
        a: EX1,
        b: EX2,
        x: EX3,
        y: EX4,
    ) -> Result<AllocatedNum<E>, SynthesisError>
    where
        E: Engine,
        CS: ConstraintSystem<E>,
        EX1: Into<Expression<E>>,
        EX2: Into<Expression<E>>,
        EX3: Into<Expression<E>>,
        EX4: Into<Expression<E>>,
    {
        let eq = Self::equals(cs.namespace(|| "eq"), a, b)?;
        Self::conditionally_select(cs.namespace(|| "select"), x, y, &Boolean::from(eq))
    }

    /// Deconstructs this allocated number into its
    /// boolean representation in little-endian bit
    /// order, requiring that the representation
    /// strictly exists "in the field" (i.e., a
    /// congruency is not allowed.)
    pub fn into_bits_le_strict<CS>(&self, mut cs: CS) -> Result<Vec<Boolean>, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        pub fn kary_and<E, CS>(
            mut cs: CS,
            v: &[AllocatedBit],
        ) -> Result<AllocatedBit, SynthesisError>
        where
            E: Engine,
            CS: ConstraintSystem<E>,
        {
            assert!(v.len() > 0);

            // Let's keep this simple for now and just AND them all
            // manually
            let mut cur = None;

            for (i, v) in v.iter().enumerate() {
                if cur.is_none() {
                    cur = Some(v.clone());
                } else {
                    cur = Some(AllocatedBit::and(
                        cs.namespace(|| format!("and {}", i)),
                        cur.as_ref().unwrap(),
                        v,
                    )?);
                }
            }

            Ok(cur.expect("v.len() > 0"))
        }

        // We want to ensure that the bit representation of a is
        // less than or equal to r - 1.
        let mut a = self.get_value().map(|e| BitIterator::new(e.into_repr()));
        let mut b = E::Fr::char();
        b.sub_noborrow(&1.into());

        let mut result = vec![];

        // Runs of ones in r
        let mut last_run = None;
        let mut current_run = vec![];

        let mut found_one = false;
        let mut i = 0;
        for b in BitIterator::new(b) {
            let a_bit = a.as_mut().map(|e| e.next().unwrap());

            // Skip over unset bits at the beginning
            found_one |= b;
            if !found_one {
                // a_bit should also be false
                a_bit.map(|e| assert!(!e));
                continue;
            }

            if b {
                // This is part of a run of ones. Let's just
                // allocate the boolean with the expected value.
                let a_bit = AllocatedBit::alloc(cs.namespace(|| format!("bit {}", i)), a_bit)?;
                // ... and add it to the current run of ones.
                current_run.push(a_bit.clone());
                result.push(a_bit);
            } else {
                if current_run.len() > 0 {
                    // This is the start of a run of zeros, but we need
                    // to k-ary AND against `last_run` first.

                    if last_run.is_some() {
                        current_run.push(last_run.clone().unwrap());
                    }
                    last_run = Some(kary_and(
                        cs.namespace(|| format!("run ending at {}", i)),
                        &current_run,
                    )?);
                    current_run.truncate(0);
                }

                // If `last_run` is true, `a` must be false, or it would
                // not be in the field.
                //
                // If `last_run` is false, `a` can be true or false.

                let a_bit = AllocatedBit::alloc_conditionally(
                    cs.namespace(|| format!("bit {}", i)),
                    a_bit,
                    &last_run.as_ref().expect("char always starts with a one"),
                )?;
                result.push(a_bit);
            }

            i += 1;
        }

        // char is prime, so we'll always end on
        // a run of zeros.
        assert_eq!(current_run.len(), 0);

        // Now, we have `result` in big-endian order.
        // However, now we have to unpack self!

        let mut packed_lc = LinearCombination::zero();
        let mut coeff = E::Fr::one();

        for bit in result.iter().rev() {
            packed_lc = packed_lc + (coeff, bit.get_variable());

            coeff.double();
        }

        // ensure packed bits equal to given lc
        // packed_lc * 1 == self.lc
        cs.enforce(
            || "unpacking constraint",
            |_| packed_lc,
            |zero| zero + CS::one(),
            |zero| zero + &self.lc,
        );

        // Convert into booleans, and reverse for little-endian bit order
        Ok(result.into_iter().map(|b| Boolean::from(b)).rev().collect())
    }

    /// Convert the expression into its little-endian representation.
    /// Note that this does not strongly enforce that the commitment is
    /// "in the field."
    pub fn into_bits_le<CS>(&self, mut cs: CS) -> Result<Vec<Boolean>, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let bits = boolean::field_into_allocated_bits_le(&mut cs, self.value)?;

        let mut packed_lc = LinearCombination::zero();
        let mut coeff = E::Fr::one();

        for bit in bits.iter() {
            packed_lc = packed_lc + (coeff, bit.get_variable());

            coeff.double();
        }

        // ensure packed bits equal to given lc
        // packed_lc * 1 == self.lc
        cs.enforce(|| "unpacking constraint", |_| packed_lc, |zero| zero + CS::one(), |zero| zero + &self.lc);

        Ok(bits.into_iter().map(|b| Boolean::from(b)).collect())
    }

    pub fn into_number<CS>(&self, mut cs: CS) -> Result<AllocatedNum<E>, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let value = AllocatedNum::alloc(
            cs.namespace(|| "allocate number"), 
            || {
                self.value.grab()
            }
        )?;

        // ensure packed bits equal to given lc
        // packed_lc * 1 == self.lc
        cs.enforce(
            || "packing constraint", 
            |zero| zero + value.get_variable(), 
            |zero| zero + CS::one(), 
            |zero| zero + &self.lc
        );

        Ok(value)
    }

    /// Return fixed amount of bits of the expression.
    /// Should be used when there is a priori knowledge of bit length of the number
    pub fn into_bits_le_fixed<CS>(
        &self,
        mut cs: CS,
        bit_length: usize,
    ) -> Result<Vec<Boolean>, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let bits = boolean::field_into_allocated_bits_le_fixed(&mut cs, self.value, bit_length)?;

        let mut packed_lc = LinearCombination::zero();
        let mut coeff = E::Fr::one();

        for bit in bits.iter() {
            packed_lc = packed_lc + (coeff, bit.get_variable());

            coeff.double();
        }

        // ensure packed bits equal to given lc
        // packed_lc * 1 == self.lc
        cs.enforce(|| "unpacking constraint", |_| packed_lc, |zero| zero + CS::one(), |zero| zero + &self.lc);

        Ok(bits.into_iter().map(|b| Boolean::from(b)).collect())
    }
    /// Limits number of bits. The easiest example when required
    /// is to add or subtract two "small" (with bit length smaller
    /// than one of the field) numbers and check for overflow
    pub fn limit_number_of_bits<CS>(
        &self,
        mut cs: CS,
        number_of_bits: usize,
    ) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        // do the bit decomposition and check that higher bits are all zeros

        let mut bits = self.into_bits_le(cs.namespace(|| "unpack to limit number of bits"))?;

        bits.drain(0..number_of_bits);

        // repack

        let mut top_bits_lc = Num::<E>::zero();
        let mut coeff = E::Fr::one();
        for bit in bits.into_iter() {
            top_bits_lc = top_bits_lc.add_bool_with_coeff(CS::one(), &bit, coeff);
            coeff.double();
        }

        // enforce packing and zeroness
        cs.enforce(
            || "repack top bits",
            |zero| zero,
            |zero| zero + CS::one(),
            |_| top_bits_lc.lc(E::Fr::one()),
        );

        Ok(())
    }
}

impl<E: Engine> From<&AllocatedNum<E>> for Expression<E> {
    fn from(num: &AllocatedNum<E>) -> Expression<E> {
        Expression {
            value: num.get_value(),
            lc: LinearCombination::<E>::zero() + num.get_variable(),
        }
    }
}

impl<E: Engine> From<&Num<E>> for Expression<E> {
    fn from(num: &Num<E>) -> Expression<E> {
        Expression {
            value: num.get_value(),
            lc: num.lc(E::Fr::one()),
        }
    }
}

impl<E: Engine> From<&AllocatedBit> for Expression<E> {
    fn from(bit: &AllocatedBit) -> Expression<E> {
        Expression {
            value: bit.get_value_field::<E>(),
            lc: LinearCombination::<E>::zero() + bit.get_variable(),
        }
    }
}

impl<E: Engine, EX: Into<Expression<E>>> Add<EX> for Expression<E> {
    type Output = Expression<E>;

    fn add(self, other: EX) -> Expression<E> {
        let other: Expression<E> = other.into();
        let newval = match (self.value, other.value) {
            (Some(mut curval), Some(val)) => {
                let tmp = val;
                curval.add_assign(&tmp);

                Some(curval)
            }
            _ => None,
        };

        Expression {
            value: newval,
            lc: self.lc + &other.lc,
        }
    }
}

impl<E: Engine, EX: Into<Expression<E>>> Sub<EX> for Expression<E> {
    type Output = Expression<E>;

    fn sub(self, other: EX) -> Expression<E> {
        let other: Expression<E> = other.into();
        let newval = match (self.value, other.value) {
            (Some(mut curval), Some(val)) => {
                let tmp = val;
                curval.sub_assign(&tmp);

                Some(curval)
            }
            _ => None,
        };

        Expression {
            value: newval,
            lc: self.lc - &other.lc,
        }
    }
}

#[cfg(test)]
mod test {
    use super::Expression;
    use super::{AllocatedBit, AllocatedNum, Boolean, Num};
    use bellman::pairing::bls12_381::{Bls12, Fr};
    use bellman::pairing::ff::{BitIterator, Field, PrimeField};
    use bellman::ConstraintSystem;
    use circuit::test::*;
    use rand::{Rand, Rng, SeedableRng, XorShiftRng};
    #[test]
    fn test_lc_equals() {
        let mut cs = TestConstraintSystem::<Bls12>::new();
        let bit = AllocatedBit::alloc(cs.namespace(|| "true"), Some(true)).unwrap();
        let one = AllocatedNum::alloc(cs.namespace(|| "one"), || Ok(Fr::one())).unwrap();
        let b_true_const = Boolean::constant(true);
        let one_const = Expression::constant::<TestConstraintSystem<Bls12>>(Fr::one());

        let a =
            AllocatedNum::alloc(cs.namespace(|| "a"), || Ok(Fr::from_str("10").unwrap())).unwrap();
        let b =
            AllocatedNum::alloc(cs.namespace(|| "b"), || Ok(Fr::from_str("12").unwrap())).unwrap();
        let c =
            AllocatedNum::alloc(cs.namespace(|| "c"), || Ok(Fr::from_str("10").unwrap())).unwrap();

        let d = Num::zero();
        let d = d.add_number_with_coeff(&one, Fr::from_str("10").unwrap());

        let not_eq = Expression::equals(cs.namespace(|| "not_eq"), &a, &b).unwrap();
        let not_eq2 = Expression::equals(cs.namespace(|| "eq a bit_true"), &bit, &a).unwrap();

        let eq = Expression::equals(cs.namespace(|| "eq"), &a, &c).unwrap();
        let eq2 = Expression::equals(cs.namespace(|| "eq a d"), &a, &d).unwrap();
        let eq3 = Expression::equals(cs.namespace(|| "eq one bit_true"), &bit, &one).unwrap();
        let eq4 = Expression::equals(
            cs.namespace(|| "eq one_const b_true_const"),
            Expression::boolean::<TestConstraintSystem<Bls12>>(b_true_const),
            Expression::constant::<TestConstraintSystem<Bls12>>(Fr::one()),
        )
        .unwrap();
        let err = cs.which_is_unsatisfied();
        if err.is_some() {
            panic!("ERROR satisfying in {}", err.unwrap());
        }
        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 6 * 3 + 1);

        assert_eq!(not_eq.get_value().unwrap(), false);
        assert_eq!(not_eq2.get_value().unwrap(), false);
        assert_eq!(eq.get_value().unwrap(), true);
        assert_eq!(eq2.get_value().unwrap(), true);
        assert_eq!(eq3.get_value().unwrap(), true);
        assert_eq!(eq4.get_value().unwrap(), true);
    }

    #[test]
    fn test_expr_conditional_reversal() {
        let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        {
            let mut cs = TestConstraintSystem::<Bls12>::new();

            let a = AllocatedNum::alloc(cs.namespace(|| "a"), || Ok(rng.gen())).unwrap();
            let b = AllocatedNum::alloc(cs.namespace(|| "b"), || Ok(rng.gen())).unwrap();
            let condition = Boolean::constant(false);
            let (c, d) = Expression::conditionally_reverse(cs.namespace(||"reverse1"), &a, &b, &condition).unwrap();


            assert_eq!(a.get_value().unwrap(), c.get_value().unwrap());
            assert_eq!(b.get_value().unwrap(), d.get_value().unwrap());

            let a = Expression::u64::<TestConstraintSystem::<Bls12>>(19);
            let b = Expression::u64::<TestConstraintSystem::<Bls12>>(15);
            let condition = Boolean::constant(false);
            let (c, d) = Expression::conditionally_reverse(cs.namespace(||"reverse2"), a.clone(), b.clone(), &condition).unwrap();

            assert_eq!(a.get_value().unwrap(), c.get_value().unwrap());
            assert_eq!(b.get_value().unwrap(), d.get_value().unwrap());

            assert!(cs.is_satisfied());

        }

        {
            let mut cs = TestConstraintSystem::<Bls12>::new();

            let a = AllocatedNum::alloc(cs.namespace(|| "a"), || Ok(rng.gen())).unwrap();
            let b = AllocatedNum::alloc(cs.namespace(|| "b"), || Ok(rng.gen())).unwrap();
            let condition = Boolean::constant(true);
            let (c, d) = Expression::conditionally_reverse(&mut cs, &a, &b, &condition).unwrap();

            assert!(cs.is_satisfied());

            assert_eq!(a.get_value().unwrap(), d.get_value().unwrap());
            assert_eq!(b.get_value().unwrap(), c.get_value().unwrap());
        }
    }

    #[test]
    fn test_expr_conditional_select() {
        let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        {
            let mut cs = TestConstraintSystem::<Bls12>::new();

            let a = AllocatedNum::alloc(cs.namespace(|| "a"), || Ok(rng.gen())).unwrap();
            let b = AllocatedNum::alloc(cs.namespace(|| "b"), || Ok(rng.gen())).unwrap();

            let condition_true = Boolean::constant(true);
            let c = Expression::conditionally_select(cs.namespace(|| "c"), &a, &b, &condition_true).unwrap();

            let condition_false = Boolean::constant(false);
            let d = Expression::conditionally_select(cs.namespace(|| "d"), &a, &b, &condition_false).unwrap();

            assert!(cs.is_satisfied());
            assert!(cs.num_constraints() == 2);

            assert_eq!(a.get_value().unwrap(), c.get_value().unwrap());
            assert_eq!(b.get_value().unwrap(), d.get_value().unwrap());
        }
    }

    #[test]
    fn select_if_equals() {
        let mut cs = TestConstraintSystem::<Bls12>::new();

        let a = AllocatedNum::alloc(cs.namespace(|| "a"), || Ok(Fr::from_str("0").unwrap())).unwrap();
        let b = AllocatedNum::alloc(cs.namespace(|| "b"), || Ok(Fr::from_str("1").unwrap())).unwrap();
        let c = AllocatedNum::alloc(cs.namespace(|| "c"), || Ok(Fr::from_str("0").unwrap())).unwrap();

        let x = AllocatedNum::alloc(cs.namespace(|| "x"), || Ok(Fr::from_str("100").unwrap())).unwrap();
        let y = AllocatedNum::alloc(cs.namespace(|| "y"), || Ok(Fr::from_str("200").unwrap())).unwrap();

        let n_eq =     Expression::select_ifeq(cs.namespace(|| "ifeq"),  &a, &c, &x, &y).unwrap();
        let n_not_eq = Expression::select_ifeq(cs.namespace(|| "ifneq"), &a, &b, &x, &y).unwrap();

        assert!(cs.is_satisfied());
        assert_eq!(n_eq.get_value().unwrap(), Fr::from_str("100").unwrap());
        assert_eq!(n_not_eq.get_value().unwrap(), Fr::from_str("200").unwrap());
    }

    #[test]
    fn test_into_bits_strict() {
        let mut negone = Fr::one();
        negone.negate();

        let mut cs = TestConstraintSystem::<Bls12>::new();

        let n = AllocatedNum::alloc(&mut cs, || Ok(negone)).unwrap();
        let n = Expression::from(&n);
        n.into_bits_le_strict(&mut cs).unwrap();

        assert!(cs.is_satisfied());

        // make the bit representation the characteristic
        cs.set("bit 254/boolean", Fr::one());

        // this makes the conditional boolean constraint fail
        assert_eq!(cs.which_is_unsatisfied().unwrap(), "bit 254/boolean constraint");
    }

    #[test]
    fn test_into_bits() {
        let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for i in 0..200 {
            let r = Fr::rand(&mut rng);
            let mut cs = TestConstraintSystem::<Bls12>::new();

            let n = AllocatedNum::alloc(&mut cs, || Ok(r)).unwrap();
            let n = Expression::from(&n);

            let bits = if i % 2 == 0 {
                n.into_bits_le(&mut cs).unwrap()
            } else {
                n.into_bits_le_strict(&mut cs).unwrap()
            };

            assert!(cs.is_satisfied());

            for (b, a) in BitIterator::new(r.into_repr()).skip(1).zip(bits.iter().rev()) {
                if let &Boolean::Is(ref a) = a {
                    assert_eq!(b, a.get_value().unwrap());
                } else {
                    unreachable!()
                }
            }

            cs.set("num", Fr::rand(&mut rng));
            assert!(!cs.is_satisfied());
            cs.set("num", r);
            assert!(cs.is_satisfied());

            for i in 0..Fr::NUM_BITS {
                let name = format!("bit {}/boolean", i);
                let cur = cs.get(&name);
                let mut tmp = Fr::one();
                tmp.sub_assign(&cur);
                cs.set(&name, tmp);
                assert!(!cs.is_satisfied());
                cs.set(&name, cur);
                assert!(cs.is_satisfied());
            }
        }
    }
    #[test]
    fn test_into_bits_fixed(){
        let mut cs = TestConstraintSystem::<Bls12>::new();
        let a = Expression::u64::<TestConstraintSystem::<Bls12>>(0b1011);
        let bits = a.into_bits_le_fixed(&mut cs, 4).unwrap();
        assert!(cs.is_satisfied());
        assert_eq!(bits[0].get_value().unwrap(), true);
        assert_eq!(bits[1].get_value().unwrap(), true);
        assert_eq!(bits[2].get_value().unwrap(), false);
        assert_eq!(bits[3].get_value().unwrap(), true);

    }
}
