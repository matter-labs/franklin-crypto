use super::super::common::{matrix::mmul_assign, sbox::{sbox}};
use super::super::sponge::{generic_hash};
use super::super::traits::{HashFamily, HashParams};
use bellman::{Engine, Field};
use super::params::RescueParams;

/// Receives inputs whose length `known` prior(fixed-length).
/// Also uses custom domain strategy which basically sets value of capacity element to
/// length of input and applies a padding rule which makes input size equals to multiple of
/// rate parameter.
/// Uses pre-defined state-width=3 and rate=2.
pub fn rescue_hash<E: Engine, const L: usize>(input: &[E::Fr; L]) -> [E::Fr; 2] {
    const WIDTH: usize = 3;
    const RATE: usize = 2;
    let params = RescueParams::<E, RATE, WIDTH>::default();
    generic_hash(&params, input, None)
}

pub(crate) fn rescue_round_function<
    E: Engine,
    P: HashParams<E, RATE, WIDTH>,
    const RATE: usize,
    const WIDTH: usize,
>(
    params: &P,
    state: &mut [E::Fr; WIDTH]
) {
    assert_eq!(params.hash_family(), HashFamily::Rescue, "Incorrect hash family!");

    // round constants for first step
    state
        .iter_mut()
        .zip(params.constants_of_round(0).iter())
        .for_each(|(s, c)| s.add_assign(c));

    for round in 0..2 * params.number_of_full_rounds() {
        // sbox
        if round & 1 == 0 {
            sbox::<E>(params.alpha_inv(), state);
        } else {
            sbox::<E>(params.alpha(), state);
        }

        if params.allows_specialization() {
            // may be we get a cool MDS and can spedup a little
            let constants = params.constants_of_round(round + 1);
            params.specialized_affine_transformation_for_round(state, &constants);
        } else {
            // mds
            mmul_assign::<E, WIDTH>(params.mds_matrix(), state);

            // round constants
            state
                .iter_mut()
                .zip(params.constants_of_round(round + 1).iter())
                .for_each(|(s, c)| s.add_assign(c));
        }
    }
}
