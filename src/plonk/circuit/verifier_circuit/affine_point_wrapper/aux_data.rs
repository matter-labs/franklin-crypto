use crate::bellman::pairing::{
    Engine,
    CurveAffine,
    CurveProjective,
};

use crate::bellman::pairing::ff::{
    PrimeField,
};

use crate::bellman::pairing::bn256::{Bn256};


pub trait AuxData<E: Engine>: Clone + std::fmt::Debug
{
    fn new() -> Self;
    fn get_b(&self) -> <E::G1Affine as CurveAffine>::Base;
    fn get_group_order(&self) -> &[u64];
    // get point G not located in the main subgroup
    // possible for BLS12-381 and not possible for BN
    fn get_h(&self) -> Option<E::G1Affine>;
    fn requires_subgroup_check(&self) -> bool;
}

#[derive(Clone, Debug)]
pub struct BN256AuxData {
    b: <Bn256 as Engine>::Fq,
    group_order: [u64; 4],
}

impl AuxData<Bn256> for BN256AuxData {

    fn new() -> Self {
        // curve equation: y^2 = x^3 + 3, a = 0, b = 3
        // r = 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001
        
        let b = <Bn256 as Engine>::Fq::from_str("3").expect("should convert");
        let r : [u64; 4] = [0x43e1f593f0000001, 0x2833e84879b97091, 0xb85045b68181585d, 0x30644e72e131a029];

        BN256AuxData {
            b: b,
            group_order: r,
        }
    }

    fn get_b(&self) -> <Bn256 as Engine>::Fq {
        self.b.clone()
    }

    fn get_group_order(&self) -> &[u64] {
        &self.group_order[..]
    }

    fn get_h(&self) -> Option<<Bn256 as Engine>::G1Affine> {
        None
    }

    fn requires_subgroup_check(&self) -> bool {
        false
    }
}

// TODO: implement AuxData for BLS12-381