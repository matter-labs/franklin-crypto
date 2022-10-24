use bellman::{Engine, Field, PrimeField};

use super::super::common::matrix::{compute_optimized_matrixes, mmul_assign, try_inverse};
use super::super::common::params::InnerHashParameters;
use super::super::traits::{CustomGate, HashFamily, HashParams, Sbox};
use plonk::circuit::rescue_copy::{BigArraySerde, serialize_array_of_arrays, serialize_vec_of_arrays, deserialize_array_of_arrays, 
    deserialize_vec_of_arrays, serialize_vec_of_arrays_of_arrays, deserialize_vec_of_arrays_of_arrays};
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct PoseidonParams<E: Engine, const RATE: usize, const WIDTH: usize> {
    #[serde(with = "BigArraySerde")]
    pub(crate) state: [E::Fr; WIDTH],
    #[serde(serialize_with = "serialize_array_of_arrays")]
    #[serde(deserialize_with = "deserialize_array_of_arrays")]
    pub(crate) mds_matrix: [[E::Fr; WIDTH]; WIDTH],
    #[serde(serialize_with = "serialize_vec_of_arrays")]
    #[serde(deserialize_with = "deserialize_vec_of_arrays")]
    pub(crate) optimized_round_constants: Vec<[E::Fr; WIDTH]>,
    #[serde(serialize_with = "serialize_array_of_arrays")]
    #[serde(deserialize_with = "deserialize_array_of_arrays")]
    pub(crate) optimized_mds_matrixes_0: [[E::Fr; WIDTH]; WIDTH],
    #[serde(serialize_with = "serialize_vec_of_arrays_of_arrays")]
    #[serde(deserialize_with = "deserialize_vec_of_arrays_of_arrays")]
    pub(crate) optimized_mds_matrixes_1: Vec<[[E::Fr; WIDTH]; WIDTH]>,
    pub(crate) alpha: Sbox,
    pub(crate) full_rounds: usize,
    pub(crate) partial_rounds: usize,
    pub(crate) custom_gate: CustomGate,
}

impl<E: Engine, const RATE: usize, const WIDTH: usize> PartialEq
    for PoseidonParams<E, RATE, WIDTH>
{
    fn eq(&self, other: &Self) -> bool {
        self.hash_family() == other.hash_family()
    }
}

impl<E: Engine, const RATE: usize, const WIDTH: usize> Default for PoseidonParams<E, RATE, WIDTH> {
    fn default() -> Self {
        let (params, 
            alpha, 
            optimized_round_constants, 
            (optimized_mds_matrixes_0, optimized_mds_matrixes_1)
        ) =
            super::params::poseidon_light_params::<E, RATE, WIDTH>();
        Self {
            state: [E::Fr::zero(); WIDTH],
            mds_matrix: params.mds_matrix,
            alpha: Sbox::Alpha(alpha),
            optimized_round_constants,
            optimized_mds_matrixes_0,
            optimized_mds_matrixes_1,
            full_rounds: params.full_rounds,
            partial_rounds: params.partial_rounds,
            custom_gate: CustomGate::None,
        }
    }
}

impl<E: Engine, const RATE: usize, const WIDTH: usize> HashParams<E, RATE, WIDTH>
    for PoseidonParams<E, RATE, WIDTH>
{
    fn hash_family(&self) -> HashFamily {
        HashFamily::Poseidon
    }

    fn constants_of_round(&self, _round: usize) -> &[E::Fr; WIDTH] {
        unimplemented!("Poseidon uses optimized constants")
    }

    fn mds_matrix(&self) -> &[[E::Fr; WIDTH]; WIDTH] {
        &self.mds_matrix
    }

    fn number_of_full_rounds(&self) -> usize {
        self.full_rounds
    }

    fn number_of_partial_rounds(&self) -> usize {
        self.partial_rounds
    }

    fn alpha(&self) -> &Sbox {
        &self.alpha
    }

    fn alpha_inv(&self) -> &Sbox {
        unimplemented!("Poseidon doesn't have inverse direction")
    }

    fn optimized_round_constants(&self) -> &[[E::Fr; WIDTH]] {
        &self.optimized_round_constants
    }

    fn optimized_mds_matrixes(&self) -> (&[[E::Fr; WIDTH]; WIDTH], &[[[E::Fr; WIDTH]; WIDTH]]) {
        (
            &self.optimized_mds_matrixes_0,
            &self.optimized_mds_matrixes_1,
        )
    }

    fn custom_gate(&self) -> CustomGate {
        self.custom_gate
    }

    fn use_custom_gate(&mut self, custom_gate: CustomGate) {
        self.custom_gate = custom_gate;
    }
}

pub fn poseidon_params<E: Engine, const RATE: usize, const WIDTH: usize>(
) -> (InnerHashParameters<E, RATE, WIDTH>, u64) {
    let security_level = 80;
    let full_rounds = 8;
    // let partial_rounds = 83;
    let partial_rounds = 33;

    let mut params = InnerHashParameters::new(security_level, full_rounds, partial_rounds);

    let number_of_rounds = full_rounds + partial_rounds;
    let rounds_tag = b"Rescue_f";
    params.compute_round_constants(number_of_rounds, rounds_tag);
    params.compute_mds_matrix_for_poseidon();

    let alpha = 5u64;

    (params, alpha)
}

pub(crate) fn poseidon_light_params<E: Engine, const RATE: usize, const WIDTH: usize>() -> (
    InnerHashParameters<E, RATE, WIDTH>,
    u64,
    Vec<[E::Fr; WIDTH]>,
    ([[E::Fr; WIDTH]; WIDTH], Vec<[[E::Fr; WIDTH]; WIDTH]>),
) {
    let (params, alpha) = poseidon_params();

    let optimized_constants = compute_optimized_round_constants::<E, WIDTH>(
        params.round_constants(),
        &params.mds_matrix,
        params.partial_rounds,
        params.full_rounds,
    );

    const SUBDIM: usize = 2; // TODO:
    assert!(
        WIDTH - SUBDIM == 1,
        "only dim 2 and dim 3 matrixes are allowed for now."
    );
    let optimized_matrixes =
        compute_optimized_matrixes::<E, WIDTH, SUBDIM>(params.partial_rounds, &params.mds_matrix);
    (params, alpha, optimized_constants, optimized_matrixes)
}

// start from last round and walk to first round
// compute equivalent eq_k_i = MC^-1*k_i
// split it into two parts one for non-linear other for accumulation
// move it further to top
pub(crate) fn compute_optimized_round_constants<E: Engine, const WIDTH: usize>(
    constants: &[[E::Fr; WIDTH]],
    original_mds: &[[E::Fr; WIDTH]; WIDTH],
    number_of_partial_rounds: usize,
    number_of_full_rounds: usize,
) -> Vec<[E::Fr; WIDTH]> {
    assert_eq!(
        constants.len(),
        number_of_full_rounds + number_of_partial_rounds,
        "non-optimized constants length does not match with total number of rounds"
    );
    let mds_inverse = try_inverse::<E, WIDTH>(original_mds).expect("has inverse");
    let number_of_half_rounds = number_of_full_rounds / 2;
    let start = number_of_half_rounds;
    let end = start + number_of_partial_rounds - 1;
    let mut acc: [E::Fr; WIDTH] = constants[end];
    let mut optimized_constants: Vec<[E::Fr; WIDTH]> = vec![];
    for round in (start..end).rev() {
        let mut inv = acc;
        mmul_assign::<E, WIDTH>(&mds_inverse, &mut inv);
        // make it two parts

        let mut second = [E::Fr::zero(); WIDTH];
        second[0] = inv[0];
        optimized_constants.push(second);

        let mut first = inv;
        first[0] = E::Fr::zero();

        // vector addition
        acc = [E::Fr::zero(); WIDTH];
        constants[round]
            .iter()
            .enumerate()
            .zip(first.iter())
            .for_each(|((idx, a), b)| {
                let mut tmp = a.clone();
                tmp.add_assign(&b);
                acc[idx] = tmp;
            });
    }
    optimized_constants.push(acc);
    optimized_constants.reverse();

    let mut final_constants = constants.to_vec();
    final_constants[start..end + 1]
        .iter_mut()
        .zip(optimized_constants)
        .for_each(|(a, b)| {
            *a = b;
        });

    final_constants
}
