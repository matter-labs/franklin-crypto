use bellman::pairing::Engine;
use super::num::Num;
use super::num::AllocatedNum;
use super::boolean::Boolean;
use super::boolean::AllocatedBit;
use bellman::pairing::ff::{Field, PrimeField, BitIterator};
use bellman::{LinearCombination, ConstraintSystem, SynthesisError, Namespace};
use bellman::pairing::ff::PrimeFieldRepr;
use circuit::boolean;
use circuit::Assignment;

pub trait Linearizable<E: Engine, CS: ConstraintSystem<E>> {
    fn lc(&self) -> LinearCombination<E>;
    fn get_value(&self) -> Option<E::Fr>;
}

impl<E: Engine, CS: ConstraintSystem<E>> Linearizable<E, CS> for Num<E> {
    fn lc(&self) -> LinearCombination<E> {
        self.lc(E::Fr::one())
    }
    fn get_value(&self) -> Option<E::Fr> {
        self.get_value()
    }
}

impl<E: Engine, CS: ConstraintSystem<E>> Linearizable<E, CS> for Boolean {
    fn lc(&self) -> LinearCombination<E> {
        self.lc(CS::one(), E::Fr::one())
    }
    fn get_value(&self) -> Option<E::Fr> {
        match self.get_value() {
            None => None,
            Some(value) => {
                if value {
                    Some(E::Fr::one())
                } else {
                    Some(E::Fr::zero())
                }
            }
        }
    }
}

pub fn equals<'a, CS, E, L>(
    mut cs: CS,
    a: &L,
    b: &L,
) -> Result<boolean::AllocatedBit, SynthesisError>
    where E: Engine,
          CS: ConstraintSystem<E>+'a,
          L: Linearizable<E, CS>
{
    // Allocate and constrain `r`: result boolean bit.
    // It equals `true` if `a` equals `b`, `false` otherwise
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

    // `x = (r-1)/delta = (r-1)/a-b`
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
        _ => None
    };
    let x = AllocatedNum::alloc(cs.namespace(|| "x"), || x_value.grab())?;
    // Constrain allocation:
    // (a - b) * r = 0
    // and this r is 0 if (a-b)!=0 (i.e a!=b)
    cs.enforce(
        || " (a - b) * r = 0",
        |lc| lc + &a.lc() - &b.lc(),
        |lc| lc + r.get_variable(),
        |lc| lc,
    );
    // Constrain:
    // (a-b)*x = (r - 1)
    // and thus `r` is 1 if `(a - b)` is zero (a == b )
    cs.enforce(
        || "(a - b) * x == r - 1",
        |lc| lc + &a.lc() - &b.lc(),
        |lc| lc + x.get_variable(),
        |lc| lc + r.get_variable() - CS::one(),
    );
    Ok(r)
}

pub fn conditionally_reverse<CS, E, L>(
    mut cs: CS,
    a: &L,
    b: &L,
    condition: &Boolean,
) -> Result<(AllocatedNum<E>, AllocatedNum<E>), SynthesisError>
    where E: Engine, CS: ConstraintSystem<E>, L: Linearizable<E, CS>
{
    let c = AllocatedNum::alloc(
        cs.namespace(|| "conditional reversal result 1"),
        || {
            if *condition.get_value().get()? {
                Ok(*b.get_value().get()?)
            } else {
                Ok(*a.get_value().get()?)
            }
        },
    )?;
    cs.enforce(
        || "first conditional reversal",
        |lc| lc + &a.lc() - &b.lc(),
        |_| condition.lc(CS::one(), E::Fr::one()),
        |lc| lc + &a.lc() - c.get_variable(),
    );
    let d = AllocatedNum::alloc(
        cs.namespace(|| "conditional reversal result 2"),
        || {
            if *condition.get_value().get()? {
                Ok(*a.get_value().get()?)
            } else {
                Ok(*b.get_value().get()?)
            }
        },
    )?;
    cs.enforce(
        || "second conditional reversal",
        |lc| lc + &b.lc() - &a.lc(),
        |_| condition.lc(CS::one(), E::Fr::one()),
        |lc| lc + &b.lc() - d.get_variable(),
    );
    Ok((c, d))
}

/// Takes two allocated numbers (a, b) and returns
/// a if the condition is true, and b
/// otherwise.
/// Most often to be used with b = 0
pub fn conditionally_select<CS, E, L>(
    mut cs: CS,
    a: &L,
    b: &L,
    condition: &Boolean,
) -> Result<AllocatedNum<E>, SynthesisError>
    where CS: ConstraintSystem<E>, E: Engine, L: Linearizable<E, CS>
{
    let c = AllocatedNum::alloc(
        cs.namespace(|| "conditional select result"),
        || {
            if *condition.get_value().get()? {
                Ok(*a.get_value().get()?)
            } else {
                Ok(*b.get_value().get()?)
            }
        },
    )?;

    // a * condition + b*(1-condition) = c ->
    // a * condition - b*condition = c - b

    cs.enforce(
        || "conditional select constraint",
        |lc| lc + &a.lc() - &b.lc(),
        |_| condition.lc(CS::one(), E::Fr::one()),
        |lc| lc + c.get_variable() - &b.lc(),
    );

    Ok(c)
}

/// Returns `a == b ? x : y`
pub fn select_ifeq< CS, E, L>(
    mut cs: CS,
    a: &L,
    b: &L,
    x: &L,
    y: &L,
) -> Result<AllocatedNum<E>, SynthesisError>
    where E: Engine,
          CS: ConstraintSystem<E>,
          L: Linearizable<E, CS>,
{
    let eq = equals(cs.namespace(|| "eq"), a, b)?;
    conditionally_select(cs.namespace(|| "select"), x, y, &Boolean::from(eq))
}

/// Note: this function is copied as is from AllocatedNum::into_bits_le_strict()
/// Deconstructs this allocated number into its
/// boolean representation in little-endian bit
/// order, requiring that the representation
/// strictly exists "in the field" (i.e., a
/// congruency is not allowed.)
pub fn into_bits_le_strict<CS, E, L>(
    linear: &L,
    mut cs: CS,
) -> Result<Vec<Boolean>, SynthesisError>
    where CS: ConstraintSystem<E>,
          E: Engine,
          L: Linearizable<E, CS>
{
    pub fn kary_and<E, CS>(
        mut cs: CS,
        v: &[AllocatedBit],
    ) -> Result<AllocatedBit, SynthesisError>
        where E: Engine,
              CS: ConstraintSystem<E>
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
    let mut a = linear.get_value().map(|e| BitIterator::new(e.into_repr()));
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
            let a_bit = AllocatedBit::alloc(
                cs.namespace(|| format!("bit {}", i)),
                a_bit,
            )?;
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

    let mut supposed_diff_lc = LinearCombination::zero();
    let mut coeff = E::Fr::one();

    for bit in result.iter().rev() {
        supposed_diff_lc = supposed_diff_lc + (coeff, bit.get_variable());

        coeff.double();
    }

    supposed_diff_lc = supposed_diff_lc - &linear.lc();

    // Enforce that difference is equal to zero thus correctly packed
    cs.enforce(
        || "unpacking constraint",
        |lc| lc,
        |lc| lc,
        |_| supposed_diff_lc,
    );

    // Convert into booleans, and reverse for little-endian bit order
    Ok(result.into_iter().map(|b| Boolean::from(b)).rev().collect())
}

/// Convert the allocated number into its little-endian representation.
/// Note that this does not strongly enforce that the commitment is
/// "in the field."
pub fn into_bits_le<CS, E, L>(
    mut cs: CS,
    linear: &L,
) -> Result<Vec<Boolean>, SynthesisError>
    where CS: ConstraintSystem<E>, E: Engine, L: Linearizable<E, CS>
{
    let bits = boolean::field_into_allocated_bits_le(
        &mut cs,
        linear.get_value(),
    )?;

    let mut lc = LinearCombination::zero();
    let mut coeff = E::Fr::one();

    for bit in bits.iter() {
        lc = lc + (coeff, bit.get_variable());

        coeff.double();
    }

    lc = lc - &linear.lc();

    cs.enforce(
        || "unpacking constraint",
        |lc| lc,
        |lc| lc,
        |_| lc,
    );

    Ok(bits.into_iter().map(|b| Boolean::from(b)).collect())
}

/// Return fixed amount of bits of the allocated number.
/// Should be used when there is a priori knowledge of bit length of the number
pub fn into_bits_le_fixed<CS, E, L>(
    linear: &L,
    mut cs: CS,
    bit_length: usize,
) -> Result<Vec<Boolean>, SynthesisError>
    where
        CS: ConstraintSystem<E>,
        E: Engine,
        L: Linearizable<E, CS>
{
    let bits = boolean::field_into_allocated_bits_le_fixed(&mut cs, linear.get_value(), bit_length)?;

    let mut packed_lc = LinearCombination::zero();
    let mut coeff = E::Fr::one();

    for bit in bits.iter() {
        packed_lc = packed_lc + (coeff, bit.get_variable());

        coeff.double();
    }
    // ensure linear combination obtained from bits equals to the linear combination we deconstruct
    cs.enforce(|| "unpacking constraint", |lc| lc, |_| linear.lc(), |_| packed_lc);

    Ok(bits.into_iter().map(|b| Boolean::from(b)).collect())
}

// /// Limits number of bits. The easiest example when required
// /// is to add or subtract two "small" (with bit length smaller
// /// than one of the field) numbers and check for overflow
// pub fn limit_number_of_bits<'_, CS, E, L>(
//     linear: &L,
//     mut cs: CS,
//     number_of_bits: usize,
// ) -> Result<(), SynthesisError>
//     where CS: ConstraintSystem<E>+'a,
//           E: Engine,
//           L: Linearizable<E, CS>,
//         L: Linearizable<E, Namespace<'_, E, <CS as ConstraintSystem<E>>::Root>>

// {
//     // do the bit decomposition and check that higher bits are all zeros

//     let mut bits = into_bits_le(
//         cs.namespace(|| "unpack to limit number of bits"),
//         linear
//     )?;

//     bits.drain(0..number_of_bits);

//     // repack

//     let mut top_bits_lc = Num::<E>::zero();
//     let mut coeff = E::Fr::one();
//     for bit in bits.into_iter() {
//         top_bits_lc = top_bits_lc.add_bool_with_coeff(CS::one(), &bit, coeff);
//         coeff.double();
//     }

//     // enforce packing and zeroness
//     cs.enforce(
//         || "repack top bits",
//         |lc| lc,
//         |lc| lc + CS::one(),
//         |_| top_bits_lc.lc(E::Fr::one()),
//     );

//     Ok(())
// }