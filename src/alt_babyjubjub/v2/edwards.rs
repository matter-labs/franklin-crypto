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

    fn negate(&self, p: &TwistedEdwardsPoint<E>) -> TwistedEdwardsPoint<E>;
}

#[derive(Clone)]
pub struct TwisterEdwardsCurveParams<E: Engine> {
    pub param_d: E::Fr,
}

impl<E: Engine> TwisterEdwardsCurveParams<E> {
    pub fn new(d: E::Fr) -> Self {
        Self { param_d: d }
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

    pub fn zero() -> TwistedEdwardsPoint<E> {
        let zero = E::Fr::zero();
        let one = E::Fr::one();

        TwistedEdwardsPoint {
            x: zero,
            y: one,
            t: zero,
            z: one,
        }
    }
}
