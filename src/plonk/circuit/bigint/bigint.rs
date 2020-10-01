use crate::bellman::pairing::{
    Engine,
};

use crate::bellman::pairing::ff::{
    Field,
    PrimeField,
    PrimeFieldRepr,
    BitIterator
};

use crate::bellman::{
    SynthesisError,
};

use crate::bellman::plonk::better_better_cs::cs::{
    Variable, 
    ConstraintSystem,
    ArithmeticTerm,
    MainGateTerm,
    Width4MainGateWithDNext,
    MainGate,
    GateInternal,
    Gate,
    LinearCombinationOfTerms,
    PolynomialMultiplicativeTerm,
    PolynomialInConstraint,
    TimeDilation,
    Coefficient,
    PlonkConstraintSystemParams
};

use num_bigint::BigUint;

use super::super::allocated_num::{AllocatedNum, Num};
use super::super::linear_combination::LinearCombination;
use super::super::simple_term::Term;

use super::constraint_num_bits;

// in principle this is valid for both cases:
// when we represent some (field) element as a set of limbs
// that are power of two, or if it's a single element as in RNS

#[derive(Clone, Debug)]
pub struct LimbedRepresentationParameters<E: Engine> {
    pub limb_size_bits: usize,
    pub limb_max_value: BigUint,
    pub limb_max_intermediate_value: BigUint,
    pub limb_intermediate_value_capacity: usize,
    pub shift_left_by_limb_constant: E::Fr,
    pub shift_right_by_limb_constant: E::Fr,
    pub mul_two_constant: E::Fr,
    pub div_two_constant: E::Fr
}

impl<E: Engine> LimbedRepresentationParameters<E> {
    pub fn new(limb_size: usize, intermediate_value_capacity: usize) -> Self {
        // assert!(limb_size <= (E::Fr::CAPACITY as usize) / 2);
        // assert!(intermediate_value_capacity <= E::Fr::CAPACITY as usize);

        let limb_max_value = (BigUint::from(1u64) << limb_size) - BigUint::from(1u64);

        let tmp = BigUint::from(1u64) << limb_size;

        let shift_left_by_limb_constant = E::Fr::from_str(&tmp.to_string()).unwrap();

        let shift_right_by_limb_constant = shift_left_by_limb_constant.inverse().unwrap();

        let mut two = E::Fr::one();
        two.double();

        let div_two_constant = two.inverse().unwrap();

        Self {
            limb_size_bits: limb_size,
            limb_max_value,
            limb_max_intermediate_value: (BigUint::from(1u64) << intermediate_value_capacity) - BigUint::from(1u64),
            limb_intermediate_value_capacity: intermediate_value_capacity,
            shift_left_by_limb_constant,
            shift_right_by_limb_constant,
            mul_two_constant: two,
            div_two_constant,
        }
    }
}

// Simple term and bit counter/max value counter that we can update
#[derive(Clone, Debug)]
pub struct Limb<E: Engine> {
    pub term: Term<E>,
    pub max_value: BigUint,
}

pub(crate) fn get_num_bits<F: PrimeField>(el: &F) -> usize {
    let repr = el.into_repr();
    let mut num_bits = repr.as_ref().len() * 64;
    for &limb in repr.as_ref().iter().rev() {
        if limb == 0 {
            num_bits -= 64;
        } else {
            num_bits -= limb.leading_zeros() as usize;
            break;
        }
    }

    num_bits
}

impl<E: Engine> Limb<E> {
    pub fn new(
        term: Term<E>,
        max_value: BigUint,
    ) -> Self {
        Self {
            term,
            max_value,
        }
    }

    pub fn new_constant(
        value: BigUint
    ) -> Self {
        let v = biguint_to_fe(value.clone());

        let term = Term::<E>::from_constant(v);

        Self {
            term,
            max_value: value
        }
    }

    pub fn max_bits(&mut self) -> usize {
        (self.max_value.bits() as usize) + 1
    }

    pub fn inc_max(&mut self, by: &BigUint) {
        self.max_value += by;
    }

    pub fn scale_max(&mut self, by: &BigUint) {
        self.max_value *= by;
    }

    pub fn max_value(&self) -> BigUint {
        self.max_value.clone()
    }

    pub fn get_value(&self) -> Option<BigUint> {
        some_fe_to_biguint(&self.term.get_value())
    }

    pub fn scale(&mut self, by: &E::Fr) {
        self.term.scale(by);
    }

    pub fn negate(&mut self) {
        self.term.negate();
    }

    pub fn add_constant(&mut self, c: &E::Fr) {
        self.term.add_constant(&c);
    }

    pub fn get_field_value(&self) -> Option<E::Fr> {
        let v = self.term.get_value();

        v
    }

    pub fn is_constant(&self) -> bool {
        self.term.is_constant()
    }

    pub fn collapse_into_constant(&self) -> E::Fr {
        self.term.get_constant_value()
    }

    pub fn collapse_into_num<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS
    ) -> Result<Num<E>, SynthesisError> {
        self.term.collapse_into_num(cs)
    }

    pub fn is_zero(&self) -> bool {
        if self.is_constant() {
            self.term.get_constant_value().is_zero()
        } else {
            false
        }
    }
}

pub fn repr_to_biguint<F: PrimeField>(repr: &F::Repr) -> BigUint {
    let mut b = BigUint::from(0u64);
    for &limb in repr.as_ref().iter().rev() {
        b <<= 64;
        b += BigUint::from(limb)
    }

    b
}

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


pub fn split_some_into_fixed_number_of_limbs(fe: Option<BigUint>, bits_per_limb: usize, num_limbs: usize) -> Vec<Option<BigUint>> {
    if let Some(fe) = fe {
        let mut fe = fe;
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

pub fn slice_into_limbs_of_max_size(value: Option<BigUint>, max_width: usize, limb_width: usize) -> (Vec<Option<BigUint>>, Vec<usize>) {
    let mut limb_sizes = vec![];
    let mut tmp = max_width;
    loop {
        if tmp > limb_width {
            tmp -= limb_width;
            limb_sizes.push(limb_width);
        } else {
            limb_sizes.push(tmp);
            break;
        }
    }

    let mask = BigUint::from(1u64) << limb_width;

    let limb_values = if let Some(value) = value {
        let mut values = Vec::with_capacity(limb_sizes.len());
        let mut tmp = value.clone();
        for _ in 0..limb_sizes.len() {
            let value = tmp.clone() % &mask;
            values.push(Some(value));
            tmp >>= limb_width;
        }

        values
    } else {
        vec![None; limb_sizes.len()]
    };

    (limb_values, limb_sizes)
}

pub(crate) fn make_multiple(mut value: usize, multiple_of: usize) -> usize {
    let remainder = value % multiple_of;
    if remainder != 0 {
        value += multiple_of - remainder;
    }

    value
}