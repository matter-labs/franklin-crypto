use bellman::{Engine};

use super::super::common::params::InnerHashParameters;
use super::super::traits::{HashParams, HashFamily, Sbox, CustomGate};
use std::convert::TryInto;
use plonk::circuit::rescue_copy::{serialize_vec_of_arrays, deserialize_vec_of_arrays, serialize_array_of_arrays, deserialize_array_of_arrays};
use plonk::circuit::rescue_copy::common::utils::compute_gcd_vec;
use plonk::circuit::rescue_copy::common::utils::compute_gcd_biguint;
use num_bigint::BigUint;
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct RescueParams<E: Engine, const RATE: usize, const WIDTH: usize> {
    pub(crate) allows_specialization: bool,
    pub(crate) full_rounds: usize,
    #[serde(serialize_with = "serialize_vec_of_arrays")]
    #[serde(deserialize_with = "deserialize_vec_of_arrays")]
    pub(crate) round_constants: Vec<[E::Fr; WIDTH]>,
    #[serde(serialize_with = "serialize_array_of_arrays")]
    #[serde(deserialize_with = "deserialize_array_of_arrays")]
    pub(crate) mds_matrix: [[E::Fr; WIDTH]; WIDTH],
    pub(crate) alpha: Sbox,
    pub(crate) alpha_inv: Sbox,
    pub(crate) custom_gate: CustomGate,
}

impl<E: Engine, const RATE: usize, const WIDTH: usize> PartialEq for RescueParams<E, RATE, WIDTH>{
    fn eq(&self, other: &Self) -> bool {
        self.hash_family() == other.hash_family()
    }
}

impl<E: Engine, const RATE: usize, const WIDTH: usize> Default
    for RescueParams<E, RATE, WIDTH>
{
    fn default() -> Self {
        let (params, alpha, alpha_inv) = compute_params::<E, RATE, WIDTH>();
        Self {
            allows_specialization: false,
            full_rounds: params.full_rounds,
            round_constants: params
                .round_constants()
                .try_into()
                .expect("round constants"),
            mds_matrix: *params.mds_matrix(),
            alpha: Sbox::Alpha(alpha),
            alpha_inv: Sbox::AlphaInverse(alpha_inv, alpha),
            custom_gate: CustomGate::None,
        }
    }
}

impl<E: Engine, const RATE: usize, const WIDTH: usize> HashParams<E, RATE, WIDTH>
    for RescueParams<E, RATE, WIDTH>
{
    #[inline]
    fn allows_specialization(&self) -> bool {
        self.allows_specialization
    }

    fn hash_family(&self) -> HashFamily {
        HashFamily::Rescue
    }

    fn constants_of_round(&self, round: usize) -> &[E::Fr; WIDTH] {
        &self.round_constants[round]
    }

    fn mds_matrix(&self) -> &[[E::Fr; WIDTH]; WIDTH] {
        &self.mds_matrix
    }

    fn number_of_full_rounds(&self) -> usize {
        self.full_rounds
    }

    fn number_of_partial_rounds(&self) -> usize {
        unimplemented!("Rescue doesn't have partial rounds.")
    }

    fn alpha(&self) -> &Sbox {
        &self.alpha
    }

    fn alpha_inv(&self) -> &Sbox {
        &self.alpha_inv
    }

    fn optimized_mds_matrixes(&self) -> (&[[E::Fr; WIDTH]; WIDTH], &[[[E::Fr; WIDTH];WIDTH]]) {
        unimplemented!("Rescue doesn't use optimized matrixes")
    }

    fn optimized_round_constants(&self) -> &[[E::Fr; WIDTH]] {
        unimplemented!("Rescue doesn't use optimized round constants")
    }

    fn custom_gate(&self) -> CustomGate {
        self.custom_gate
    }
    
    fn use_custom_gate(&mut self, custom_gate: CustomGate) {
        self.custom_gate = custom_gate;    
    }

    fn specialized_affine_transformation_for_round(&self, state: &mut [E::Fr; WIDTH], round_constants: &[E::Fr; WIDTH]) {
        debug_assert_eq!(WIDTH, 3);
        debug_assert!(self.allows_specialization);
        use bellman::Field;

        let mut res0 = state[0];
        res0.double();
        res0.add_assign(&state[1]);
        res0.add_assign(&state[2]);
        res0.add_assign(&round_constants[0]);

        let mut res1 = state[1];
        res1.double();
        res1.add_assign(&state[0]);
        res1.add_assign(&state[2]);
        res1.add_assign(&round_constants[1]);

        let mut res2 = state[2];
        res2.double();
        res2.add_assign(&state[0]);
        res2.add_assign(&state[1]);
        res2.add_assign(&round_constants[2]);

        state[0] = res0;
        state[1] = res1;
        state[2] = res2;
    }
}

impl<E: Engine> RescueParams<E, 2, 3> {
    pub fn specialized_for_num_rounds(num_rounds: usize, claimed_security_bits: usize) -> Self {
        let (params, alpha, _alpha_inv, addition_chain) = mds_optimized_params_alpha_5::<E>(num_rounds, claimed_security_bits);
        
        Self {
            allows_specialization: true,
            full_rounds: params.full_rounds,
            round_constants: params
                .round_constants()
                .try_into()
                .expect("round constants"),
            mds_matrix: *params.mds_matrix(),
            alpha: Sbox::Alpha(alpha),
            alpha_inv: Sbox::AddChain(addition_chain, alpha),
            custom_gate: CustomGate::None,
        }
    }
}

pub(crate) fn compute_params<E: Engine, const RATE: usize, const WIDTH: usize>() -> (InnerHashParameters<E, RATE, WIDTH>, u64, Vec<u64>) {
    // let full_rounds = 22;
    let full_rounds = 8;
    let security_level = 126;

    let mut params = InnerHashParameters::new(        
        security_level,
        full_rounds,
        0,
    );

    let rounds_tag = b"Rescue_f";
    let _mds_tag = b"ResM0003";
    let total_number_of_rounds = 2*full_rounds + 1;
    
    params.compute_round_constants(total_number_of_rounds, rounds_tag);
    params.compute_mds_matrix_for_rescue();

    let alpha = 5u64;
    let alpha_inv = super::super::common::utils::compute_gcd_vec::<E>(alpha).expect("inverse of alpha");

    (params, alpha, alpha_inv)
}

pub(crate) fn mds_optimized_params_alpha_5<E: Engine>(
    full_rounds: usize,
    claimed_security_bits: usize,
) -> (InnerHashParameters<E, 2, 3>, u64, Vec<u64>, Vec<super::super::traits::Step>) {
    let mut params = InnerHashParameters::new(        
        claimed_security_bits,
        full_rounds,
        0,
    );

    let rounds_tag = b"Rescue_f";
    let total_number_of_rounds = 2*full_rounds + 1;
    params.compute_round_constants_with_prefixed_blake2s(total_number_of_rounds, rounds_tag);
    params.set_circular_optimized_mds();

    let alpha = 5;
    let alpha_inv = compute_gcd_vec::<E>(alpha).expect("inverse of alpha");
    let alpha_inv_as_biguint= compute_gcd_biguint::<E>(alpha).expect("inverse of alpha");
    let addition_chain: Vec<_> = addchain::build_addition_chain(alpha_inv_as_biguint).into_iter().map(|el| super::super::traits::Step::from(el)).collect();

    (params, alpha, alpha_inv, addition_chain)
}


// #[cfg(test)]
// mod tests {

//     use super::*;
//     use bellman::pairing::bn256::{Bn256, Fr};
//     use bellman::{PrimeField, ScalarEngine};
//     use num_bigint::{BigInt, Sign};
//     #[test]
//     fn test_addition_chains() {
//         let mut rng = rand::thread_rng();

//         let alpha = 5;
//         let alpha_inv_as_biguint = compute_gcd_biguint::<Bn256>(alpha).expect("inverse of alpha");
//         let addition_chain: Vec<_> = addchain::build_addition_chain(alpha_inv_as_biguint).into_iter().map(|el| super::super::super::traits::Step::from(el)).collect();
//         use rand::Rand;

//         dbg!(addition_chain.len());
//         assert!(addition_chain.len() <= 512);

//         use bellman::Field;

//         // let mut scratch = smallvec::SmallVec::<[Fr; 512]>::new();
//         // for _ in 0..1000 {
//         //     let x = Fr::rand(&mut rng);
//         //     let forward = x.pow(&[alpha]);
//         //     let backward = add_chain_pow_smallvec(forward, &addition_chain, &mut scratch);
//         //     assert_eq!(x, backward);
//         // }

//         // for _ in 0..1000 {
//         //     let x = Fr::rand(&mut rng);
//         //     let backward = add_chain_pow_smallvec(x, &addition_chain, &mut scratch);
//         //     let forward = backward.pow(&[alpha]);
//         //     assert_eq!(x, forward);
//         // }

//         let x = Fr::rand(&mut rng);
//         let y = Fr::rand(&mut rng);
//         let z = Fr::rand(&mut rng);
//         let mut state = [x, y, z];
//         use super::super::super::common::sbox::sbox_alpha_inv_via_add_chain;
//         sbox_alpha_inv_via_add_chain::<Bn256>(&addition_chain, &mut state);
//     }
// }
