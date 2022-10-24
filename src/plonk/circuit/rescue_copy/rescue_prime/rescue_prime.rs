
use super::super::sponge::{generic_hash};
use super::super::traits::{HashFamily, HashParams};
use crate::bellman::pairing::{
    Engine,
};
use crate::bellman::pairing::ff::{
    Field,
    PrimeField,
    PrimeFieldRepr,
    BitIterator
};
use super::params::RescuePrimeParams;
// use plonk::circuit::rescue_copy::*;
use plonk::circuit::rescue_copy::common::sbox::sbox;
use plonk::circuit::rescue_copy::common::matrix::mmul_assign;

/// Receives inputs whose length `known` prior(fixed-length).
/// Also uses custom domain strategy which basically sets value of capacity element to
/// length of input and applies a padding rule which makes input size equals to multiple of
/// rate parameter.
/// Uses pre-defined state-width=3 and rate=2.
pub fn rescue_prime_hash<E: Engine, const L: usize>(input: &[E::Fr; L]) -> [E::Fr; 2] {
    const WIDTH: usize = 3;
    const RATE: usize = 2;

    let params = RescuePrimeParams::<E, RATE, WIDTH>::default();
    generic_hash(&params, input, None)
}


pub(crate) fn rescue_prime_round_function<
    E: Engine,
    P: HashParams<E, RATE, WIDTH>,
    const RATE: usize,
    const WIDTH: usize,
>(
    params: &P,
    state: &mut [E::Fr; WIDTH],
) {
    assert_eq!(
        params.hash_family(),
        HashFamily::RescuePrime,
        "Incorrect hash family!"
    );
    for round in 0..params.number_of_full_rounds() - 1 {
        // sbox alpha
        sbox::<E>(params.alpha(), state);
        // mds
        mmul_assign::<E, WIDTH>(&params.mds_matrix(), state);

        // round constants
        state
            .iter_mut()
            .zip(params.constants_of_round(round).iter())
            .for_each(|(s, c)| s.add_assign(c));
        // sbox alpha inv
        sbox::<E>(params.alpha_inv(), state);

        // mds
        mmul_assign::<E, WIDTH>(&params.mds_matrix(), state);

        // round constants
        state
            .iter_mut()
            .zip(params.constants_of_round(round + 1).iter())
            .for_each(|(s, c)| s.add_assign(c));
    }
}
