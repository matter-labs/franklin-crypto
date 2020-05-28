pub mod allocated_num;
pub mod custom_rescue_gate;
pub mod rescue;
pub mod linear_combination;
pub mod boolean;
pub mod uint32;
pub mod multieq;
pub mod sha256;
pub mod blake2s;
//pub mod poseidon;
pub mod bigint;
pub mod simple_term;
pub mod curve;
pub mod verifier_circuit;


use crate::bellman::pairing::Engine;
use crate::bellman::plonk::better_better_cs::cs::PlonkConstraintSystemParams;

#[derive(Clone, Copy)]
pub struct Width4WithCustomGates;

impl<E: Engine> PlonkConstraintSystemParams<E> for Width4WithCustomGates {
    const STATE_WIDTH: usize =  4;
    const WITNESS_WIDTH: usize = 0;
    const HAS_WITNESS_POLYNOMIALS: bool = false;
    const HAS_CUSTOM_GATES: bool = true;
    const CAN_ACCESS_NEXT_TRACE_STEP: bool = true;
}