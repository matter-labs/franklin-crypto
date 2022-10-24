use super::sbox::*;
use super::sponge::circuit_generic_hash_num;
use super::matrix::matrix_vector_product;
use plonk::circuit::rescue_copy::common::domain_strategy::DomainStrategy;
use super::super::traits::{HashFamily, HashParams};
use bellman::plonk::better_better_cs::cs::ConstraintSystem;
use bellman::SynthesisError;
use {
    bellman::Engine,
    plonk::circuit::{allocated_num::Num, linear_combination::LinearCombination},
};
use plonk::circuit::rescue_copy::rescue_prime::params::RescuePrimeParams;

/// Receives inputs whose length `known` prior(fixed-length).
/// Also uses custom domain strategy which basically sets value of capacity element to
/// length of input and applies a padding rule which makes input size equals to multiple of
/// rate parameter.
/// Uses pre-defined state-width=3 and rate=2.
pub fn gadget_rescue_prime_hash<E: Engine, CS: ConstraintSystem<E>, const L: usize>(
    cs: &mut CS,
    input: &[Num<E>; L],
    domain_strategy: Option<DomainStrategy>,
) -> Result<[Num<E>; 2], SynthesisError> {
    const WIDTH: usize = 3;
    const RATE: usize = 2;
    let params = RescuePrimeParams::<E, RATE, WIDTH>::default();
    circuit_generic_hash_num(cs, input, &params, domain_strategy)
}

pub(crate) fn gadget_rescue_prime_round_function<
    E: Engine,
    CS: ConstraintSystem<E>,
    P: HashParams<E, RATE, WIDTH>,
    const RATE: usize,
    const WIDTH: usize,
>(
    cs: &mut CS,
    params: &P,
    state: &mut [LinearCombination<E>; WIDTH],
) -> Result<(), SynthesisError> {
    assert_eq!(
        params.hash_family(),
        HashFamily::RescuePrime,
        "Incorrect hash family!"
    );

    for round in 0..params.number_of_full_rounds() - 1 {
        // apply sbox
        // each lc will have 3 terms but there will be 1 in first iteration
        // total cost 2 gate per state vars = 6
        sbox(
            cs,
            params.alpha(),
            state,
            None,
            params.custom_gate(),
        )?;

        // mul by mds
        matrix_vector_product(&params.mds_matrix(), state)?;

        // round constants
        let constants = params.constants_of_round(round);
        for (s, c) in state.iter_mut().zip(constants.iter().cloned()) {
            s.add_assign_constant(c);
        }
        // apply inverse sbox
        sbox(
            cs,
            params.alpha_inv(),
            state,
            None,
            params.custom_gate(),
        )?;

        // mul by mds
        matrix_vector_product(&params.mds_matrix(), state)?;

        // round constants
        let constants = params.constants_of_round(round + 1);
        for (s, c) in state.iter_mut().zip(constants.iter().cloned()) {
            s.add_assign_constant(c);
        }
    }
    Ok(())
}
