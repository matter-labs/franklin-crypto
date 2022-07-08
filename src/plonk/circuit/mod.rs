pub mod allocated_num;
pub mod blake2s;
pub mod boolean;
pub mod custom_rescue_gate;
pub mod linear_combination;
pub mod multieq;
pub mod rescue;
pub mod sha256;
pub mod uint32;
//pub mod poseidon;
pub mod bigint;
pub mod booleanwrapper;
pub mod byte;
pub mod counter;
pub mod curve;
pub mod custom_5th_degree_gate_optimized;
pub mod edwards;
pub mod permutation_network;
pub mod simple_term;
pub mod tables;
pub mod utils;
pub mod verifier_circuit;

pub mod assignment;
pub mod hashes_with_tables;

use crate::bellman::pairing::Engine;
use crate::bellman::plonk::better_better_cs::cs::PlonkConstraintSystemParams;

pub use crate::bellman::plonk::better_better_cs::cs::PlonkCsWidth4WithNextStepAndCustomGatesParams as Width4WithCustomGates;

use crate::bellman::SynthesisError;

pub use self::assignment::*;
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
            }
            _ => None,
        }
    }
    fn sub(&self, other: &Self) -> Self {
        match (self, other) {
            (Some(s), Some(o)) => {
                let mut tmp = *s;
                tmp.sub_assign(&o);

                Some(tmp)
            }
            _ => None,
        }
    }
    fn mul(&self, other: &Self) -> Self {
        match (self, other) {
            (Some(s), Some(o)) => {
                let mut tmp = *s;
                tmp.mul_assign(&o);

                Some(tmp)
            }
            _ => None,
        }
    }
    fn fma(&self, to_mul: &Self, to_add: &Self) -> Self {
        match (self, to_mul, to_add) {
            (Some(s), Some(m), Some(a)) => {
                let mut tmp = *s;
                tmp.mul_assign(&m);
                tmp.add_assign(&a);

                Some(tmp)
            }
            _ => None,
        }
    }
    fn negate(&self) -> Self {
        match self {
            Some(s) => {
                let mut tmp = *s;
                tmp.negate();

                Some(tmp)
            }
            _ => None,
        }
    }
}
