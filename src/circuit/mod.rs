// #[cfg(test)]
pub mod test;

pub mod boolean;
pub mod multieq;
pub mod uint32;
pub mod blake2s;
pub mod num;
pub mod lookup;
pub mod baby_ecc;
pub mod ecc;
pub mod pedersen_hash;
pub mod baby_pedersen_hash;
pub mod multipack;
pub mod sha256;
pub mod baby_eddsa;
pub mod float_point;
pub mod polynomial_lookup;
pub mod as_waksman;
// pub mod linear_combination;
pub mod expression;
// pub mod shark_mimc;
pub mod rescue;

pub mod sapling;
pub mod sprout;

use bellman::{
    SynthesisError
};

// TODO: This should probably be removed and we
// should use existing helper methods on `Option`
// for mapping with an error.
/// This basically is just an extension to `Option`
/// which allows for a convenient mapping to an
/// error on `None`.
pub trait Assignment<T> {
    fn get(&self) -> Result<&T, SynthesisError>;
    fn grab(self) -> Result<T, SynthesisError>;
}

impl<T: Clone> Assignment<T> for Option<T> {
    fn get(&self) -> Result<&T, SynthesisError> {
        match *self {
            Some(ref v) => Ok(v),
            None => Err(SynthesisError::AssignmentMissing)
        }
    }

    fn grab(self) -> Result<T, SynthesisError> {
        match self {
            Some(v) => Ok(v),
            None => Err(SynthesisError::AssignmentMissing)
        }
    }
}

use crate::bellman::pairing::ff::{Field, PrimeField};

pub trait SomeField<F: Field> {
    fn add(&self, other: &Self) -> Self;
    fn sub(&self, other: &Self) -> Self;
    fn mul(&self, other: &Self) -> Self;
    fn fma(&self, to_mul: &Self, to_add: &Self) -> Self;
    fn negate(&self) -> Self;
}

impl<F: Field> SomeField<F> for Option<F> {
    fn add(&self, other: &Self) -> Self {
        match (self, other) {
            (Some(s), Some(o)) => {
                let mut tmp = *s;
                tmp.add_assign(&o);

                Some(tmp)
            },
            _ => None
        }
    }
    fn sub(&self, other: &Self) -> Self {
        match (self, other) {
            (Some(s), Some(o)) => {
                let mut tmp = *s;
                tmp.sub_assign(&o);

                Some(tmp)
            },
            _ => None
        }
    }
    fn mul(&self, other: &Self) -> Self {
        match (self, other) {
            (Some(s), Some(o)) => {
                let mut tmp = *s;
                tmp.mul_assign(&o);

                Some(tmp)
            },
            _ => None
        }
    }
    fn fma(&self, to_mul: &Self, to_add: &Self) -> Self {
        match (self, to_mul, to_add) {
            (Some(s), Some(m), Some(a)) => {
                let mut tmp = *s;
                tmp.mul_assign(&m);
                tmp.add_assign(&a);

                Some(tmp)
            },
            _ => None
        }
    }
    fn negate(&self) -> Self {
        match self {
            Some(s) => {
                let mut tmp = *s;
                tmp.negate();

                Some(tmp)
            },
            _ => None
        }
    }
}