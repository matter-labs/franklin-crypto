use super::sbox::sbox;
use super::matrix::matrix_vector_product;
use bellman::plonk::better_better_cs::cs::ConstraintSystem;
use plonk::circuit::rescue_copy::common::domain_strategy::DomainStrategy;
use plonk::circuit::rescue_copy::traits::HashParams;
use bellman::SynthesisError;
use {
    bellman::Engine, plonk::circuit::allocated_num::Num,
    plonk::circuit::linear_combination::LinearCombination,
};
use plonk::circuit::rescue_copy::circuit_rescue::sponge::circuit_generic_hash_num;
use plonk::circuit::rescue_copy::rescue::params::RescueParams;
/// Receives inputs whose length `known` prior(fixed-length).
/// Also uses custom domain strategy which basically sets value of capacity element to
/// length of input and applies a padding rule which makes input size equals to multiple of
/// rate parameter.
/// Uses pre-defined state-width=3 and rate=2.
pub fn circuit_rescue_hash<E: Engine, CS: ConstraintSystem<E>, const L: usize>(
    cs: &mut CS,
    input: &[Num<E>; L],
    domain_strategy: Option<DomainStrategy>,
) -> Result<[Num<E>; 2], SynthesisError> {
    const WIDTH: usize = 3;
    const RATE: usize = 2;
    let params = RescueParams::<E, RATE, WIDTH>::default();
    circuit_generic_hash_num(cs, input, &params, domain_strategy)
}

pub(crate) fn circuit_rescue_round_function<
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
        super::super::traits::HashFamily::Rescue,
        "Incorrect hash family!"
    );
    state
        .iter_mut()
        .zip(params.constants_of_round(0).iter())
        .for_each(|(s, c)| s.add_assign_constant(*c));

    for round in 0..2 * params.number_of_full_rounds() {
        // apply sbox
        if round & 1 == 0 {
            sbox(
                cs,
                params.alpha_inv(),
                state,
                None,
                params.custom_gate(),
            )?;
        } else {
            sbox(
                cs,
                params.alpha(),
                state,
                None,
                params.custom_gate(),
            )?;
        }
        // mds row
        matrix_vector_product(&params.mds_matrix(), state)?;

        // round constants
        for (s, c) in state
            .iter_mut()
            .zip(params.constants_of_round(round + 1).iter().cloned())
        {
            s.add_assign_constant(c);
        }
    }
    Ok(())
}
