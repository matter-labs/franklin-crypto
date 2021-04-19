use super::edwards::CircuitTwistedEdwardsCurveImplementor;
use crate::generic_twisted_edwards::bn256::*;
use crate::bellman::pairing::bn256::Bn256;

pub struct CircuitAltBabyJubjubBn256;
impl CircuitAltBabyJubjubBn256 {
    pub fn get_implementor() -> CircuitTwistedEdwardsCurveImplementor<Bn256, AltBabyJubjubParams> {
        let implementor = AltBabyJubjubBn256::get_implementor();
        CircuitTwistedEdwardsCurveImplementor {implementor }
    }
}