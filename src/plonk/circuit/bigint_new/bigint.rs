use crate::bellman::pairing::Engine;
use crate::bellman::pairing::ff::{Field, PrimeField, PrimeFieldRepr, BitIterator};
use crate::bellman::SynthesisError;
use crate::bellman::plonk::better_better_cs::cs::ConstraintSystem;
use num_bigint::BigUint;
use super::super::allocated_num::{AllocatedNum, Num};
use super::super::linear_combination::LinearCombination;
use super::super::simple_term::Term;


pub fn repr_to_biguint<F: PrimeField>(repr: &F::Repr) -> BigUint {
    let mut b = BigUint::from(0u64);
    for &limb in repr.as_ref().iter().rev() {
        b <<= 64;
        b += BigUint::from(limb)
    }
    b
}

#[track_caller]
pub fn mod_inverse(el: &BigUint, modulus: &BigUint) -> BigUint {
    use crate::num_bigint::BigInt;
    use crate::num_integer::{Integer, ExtendedGcd};
    use crate::num_traits::{ToPrimitive, Zero, One};

    if el.is_zero() {
        panic!("division by zero");
    }

    let el_signed = BigInt::from(el.clone());
    let modulus_signed = BigInt::from(modulus.clone());

    let ExtendedGcd{ gcd, x: _, y, .. } = modulus_signed.extended_gcd(&el_signed); 
    assert!(gcd.is_one());
    let y = if y < BigInt::zero() {
        let mut y = y;
        y += modulus_signed;

        y.to_biguint().expect("must be > 0")
    } else {
        y.to_biguint().expect("must be > 0")
    };

    debug_assert!(el.clone() * &y % modulus == BigUint::from(1u64));

    debug_assert!(&y < modulus);

    y
}

pub fn biguint_to_fe<F: PrimeField>(value: BigUint) -> F {
    F::from_str(&value.to_str_radix(10)).unwrap()
}

pub fn biguint_to_repr<F: PrimeField>(mut value: BigUint) -> F::Repr {
    use num_traits::ToPrimitive;

    let mut repr = F::Repr::default();
    let mask = BigUint::from(1u64) << 64;
    for l in repr.as_mut().iter_mut() {
        let limb: BigUint = value.clone() % &mask;
        *l = limb.to_u64().unwrap();
        value >>= 64;
    }

    repr
}

pub fn some_biguint_to_fe<F: PrimeField>(value: &Option<BigUint>) -> Option<F> {
    match value {
        Some(value) => {
            let n = F::from_str(&value.to_str_radix(10)).unwrap();

            Some(n)
        },
        None => None
    }
}

pub fn fe_to_biguint<F: PrimeField>(el: &F) -> BigUint {
    let repr = el.into_repr();

    repr_to_biguint::<F>(&repr)
}

pub fn some_fe_to_biguint<F: PrimeField>(el: &Option<F>) -> Option<BigUint> {
    match el {
        Some(el) => {
            let repr = el.into_repr();

            let ret = repr_to_biguint::<F>(&repr);

            Some(ret)
        },
        None => None
    }
}

pub fn get_bit_slice(v: BigUint, start: usize, end: usize) -> BigUint {
    let mut tmp = v;
    tmp >>= start;

    let mask = BigUint::from(1u64) << (end - start);

    tmp % mask
}

pub fn split_into_fixed_width_limbs(mut fe: BigUint, bits_per_limb: usize) -> Vec<BigUint> {
    let mut num_limbs = (fe.bits() as usize) / bits_per_limb;
    if (fe.bits() as usize) % bits_per_limb != 0 {
        num_limbs += 1;
    }

    let mut limbs = Vec::with_capacity(num_limbs);

    let modulus = BigUint::from(1u64) << bits_per_limb;

    for _ in 0..num_limbs {
        let limb = fe.clone() % &modulus;
        limbs.push(limb);
        fe >>= bits_per_limb;
    }

    limbs.reverse();

    limbs
}

#[track_caller]
pub fn split_some_into_fixed_number_of_limbs(
    fe: Option<BigUint>, bits_per_limb: usize, num_limbs: usize
) -> Vec<Option<BigUint>> 
{
    if let Some(fe) = fe {
        let mut fe = fe;
        // assert!(fe.bits() as usize <= bits_per_limb * num_limbs);
        let mut limbs = Vec::with_capacity(num_limbs);

        let modulus = BigUint::from(1u64) << bits_per_limb;

        for _ in 0..num_limbs {
            let limb = fe.clone() % &modulus;
            limbs.push(Some(limb));
            fe >>= bits_per_limb;
        }

        limbs
    } else {
        vec![None; num_limbs]
    }
}

#[track_caller]
pub fn split_into_fixed_number_of_limbs(mut fe: BigUint, bits_per_limb: usize, num_limbs: usize) -> Vec<BigUint> {
    let mut limbs = Vec::with_capacity(num_limbs);

    let modulus = BigUint::from(1u64) << bits_per_limb;

    for _ in 0..num_limbs {
        let limb = fe.clone() % &modulus;
        limbs.push(limb);
        fe >>= bits_per_limb;
    }

    limbs
}

#[track_caller]
pub fn split_some_into_limbs_of_variable_width(fe: Option<BigUint>, bits_per_limb: &[usize]) -> Vec<Option<BigUint>> {
    if let Some(fe) = fe {
        let mut fe = fe;
        let full_width = bits_per_limb.iter().sum();
        assert!(
            fe.bits() as usize <= full_width,
            "can fit {} bits maximum, but got {}",
            full_width,
            fe.bits()
        );
        let mut limbs = Vec::with_capacity(bits_per_limb.len());

        for &width in bits_per_limb.iter() {
            let modulus = BigUint::from(1u64) << width;
            let limb = fe.clone() % &modulus;
            limbs.push(Some(limb));
            fe >>= width;
        }

        limbs
    } else {
        vec![None; bits_per_limb.len()]
    }
}
