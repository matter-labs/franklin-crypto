use bellman::pairing::bn256::Bn256;
use bellman::pairing::ff::BitIterator;
use bellman::{Engine, Field, PrimeField, PrimeFieldRepr, ScalarEngine, SqrtField};
use rand::{Rand, Rng};
use std::marker::PhantomData;

pub trait TwistedEdwardsCurve<E: Engine> {
    type Fs: PrimeField;

    fn add(&self, p: &TwistedEdwardsPoint<E>, q: &TwistedEdwardsPoint<E>)
        -> TwistedEdwardsPoint<E>;

    fn double(&self, p: &TwistedEdwardsPoint<E>) -> TwistedEdwardsPoint<E>;

    fn mul<S: Into<<Self::Fs as PrimeField>::Repr>>(
        &self,
        p: &TwistedEdwardsPoint<E>,
        scalar: S,
    ) -> TwistedEdwardsPoint<E>;

    fn ct_mul(
        &self,
        p: &TwistedEdwardsPoint<E>,
        scalar: Self::Fs,
    ) -> TwistedEdwardsPoint<E>;

    fn negate(&self, p: &TwistedEdwardsPoint<E>) -> TwistedEdwardsPoint<E>;

    fn mul_by_generator<S: Into<<Self::Fs as PrimeField>::Repr>>(
        &self, 
        scalar: S
    ) -> TwistedEdwardsPoint<E>;
}

#[derive(Clone, Debug)]
pub struct TwisterEdwardsCurveParams<E: Engine> {
    pub is_param_a_equals_minus_one: bool,
    pub param_d: E::Fr,
    pub param_a: E::Fr,
    pub generator: TwistedEdwardsPoint<E>,
}

impl<E: Engine> TwisterEdwardsCurveParams<E> {
    pub fn new(d: E::Fr, a: E::Fr, generator: TwistedEdwardsPoint<E>) -> Self {
        let mut minus_one = E::Fr::one();
        minus_one.negate();
        
        let is_param_a_equals_minus_one = a == minus_one; 

        Self { 
            param_d: d,
            param_a: a,
            is_param_a_equals_minus_one,
            generator
        }
    }
}

pub(crate) trait ConditionalSelect<T> {
    fn conditional_select(flag: u8, first: T, second: T) -> T;
}

impl ConditionalSelect<u64> for u64 {
    fn conditional_select(flag: u8, first: u64, second: u64) -> u64 {
        let bit = flag as u64;

        bit*first + (1-bit)*second // TODO: check correctness
    }
}

#[derive(Clone, Debug)]
pub struct TwistedEdwardsPoint<E: Engine> {
    pub x: E::Fr,
    pub y: E::Fr,
    pub z: E::Fr,
    pub t: E::Fr,
}

impl<E: Engine> TwistedEdwardsPoint<E> {
    pub fn into_xy(&self) -> (E::Fr, E::Fr) {
        let zinv = self.z.inverse().unwrap();

        let mut x = self.x;
        x.mul_assign(&zinv);

        let mut y = self.y;
        y.mul_assign(&zinv);

        (x, y)
    }
    // The identity element is represented by (x:y:t:z) -> (0:1:0:1)
    pub fn identity() -> TwistedEdwardsPoint<E> {
        let zero = E::Fr::zero();
        let one = E::Fr::one();

        TwistedEdwardsPoint {
            x: zero,
            y: one,
            t: zero,
            z: one,
        }
    }

    pub fn conditional_select(
        flag: u8,
        first: &Self,
        second: &Self,
    ) -> Self {
        fn conditional_select_fe<E: Engine>(flag: u8, first: &E::Fr, second: &E::Fr) -> E::Fr {
            let first_repr = first.into_raw_repr();
            let second_repr = second.into_raw_repr();
            let mut result_repr = <E::Fr as PrimeField>::Repr::default();
            
            result_repr.as_mut()[0] =  u64::conditional_select(flag, first_repr.as_ref()[0], second_repr.as_ref()[0]);
            result_repr.as_mut()[1] =  u64::conditional_select(flag, first_repr.as_ref()[1], second_repr.as_ref()[1]);
            result_repr.as_mut()[2] =  u64::conditional_select(flag, first_repr.as_ref()[2], second_repr.as_ref()[2]);
            result_repr.as_mut()[3] =  u64::conditional_select(flag, first_repr.as_ref()[3], second_repr.as_ref()[3]);

            // first and second are valid field elements so we can unwrap
            let result = E::Fr::from_raw_repr(result_repr).unwrap();

            result
        }

        let mut result = Self::identity();
        result.x = conditional_select_fe::<E>(flag, &first.x, &second.x);
        result.y = conditional_select_fe::<E>(flag, &first.y, &second.y);
        result.t = conditional_select_fe::<E>(flag, &first.t, &second.t);
        result.z = conditional_select_fe::<E>(flag, &first.z, &second.z);

        result
    }
}
