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

pub mod sapling;
pub mod sprout;

pub mod permutation;
pub mod hashmap;

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
