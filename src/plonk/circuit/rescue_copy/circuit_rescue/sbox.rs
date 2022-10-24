use {
    bellman::{
        plonk::better_better_cs::cs::{
            ArithmeticTerm, ConstraintSystem, MainGateTerm, PlonkConstraintSystemParams,
        },
        Engine,
    },
    bellman::{Field, SynthesisError},
    plonk::circuit::allocated_num::AllocatedNum,
    plonk::circuit::{
        allocated_num::Num, custom_rescue_gate::apply_5th_power,
        linear_combination::LinearCombination,
    },
};

use plonk::circuit::Assignment;

use super::super::traits::{CustomGate, Sbox};
use plonk::circuit::rescue_copy::add_chain_pow_smallvec;


// Substitution box is non-linear part of permutation function.
// It basically computes 5th power of each element in the state.
// Poseidon uses partial sbox which basically computes power of
// single element of state. If constraint system has support of
// custom gate then computation costs only single gate.
// TODO use const generics here
pub(crate) fn sbox<E: Engine, CS: ConstraintSystem<E>, const WIDTH: usize>(
    cs: &mut CS,
    power: &Sbox,
    prev_state: &mut [LinearCombination<E>; WIDTH],
    use_partial_state: Option<std::ops::Range<usize>>,
    custom_gate: CustomGate,
) -> Result<(), SynthesisError> {
    let state_range = if let Some(partial_range) = use_partial_state{
        partial_range
    }else{
        0..WIDTH
    };

    match power {
        Sbox::Alpha(alpha) => sbox_alpha(
            cs,
            alpha,
            prev_state,
            state_range,
            custom_gate,
        ),
        Sbox::AlphaInverse(alpha_inv, alpha) => {           
            sbox_alpha_inv(cs, alpha_inv, alpha, prev_state, custom_gate)
        },
        Sbox::AddChain(chain, alpha) => {         
            // in circuit there is no difference  
            sbox_alpha_inv_via_add_chain(cs, chain, alpha, prev_state, custom_gate)
        },
    }
}

fn sbox_alpha<E: Engine, CS: ConstraintSystem<E>, const WIDTH: usize>(
    cs: &mut CS,
    alpha: &u64,
    prev_state: &mut [LinearCombination<E>; WIDTH],
    state_range: std::ops::Range<usize>,
    custom_gate: CustomGate,
) -> Result<(), SynthesisError> {
    let use_custom_gate = match custom_gate {
        CustomGate::None => false,
        _ => true,
    };
    let use_custom_gate =
        use_custom_gate && CS::Params::HAS_CUSTOM_GATES == true && CS::Params::STATE_WIDTH >= 4;

    if *alpha != 5u64 {
        unimplemented!("only 5th power is supported!")
    }
    for lc in prev_state[state_range].iter_mut() {
        match lc.clone().into_num(cs)? {
            Num::Constant(value) => {
                let result = value.pow(&[*alpha]);
                *lc = LinearCombination::zero();
                lc.add_assign_constant(result);
            }
            Num::Variable(ref value) => {
                let result = if use_custom_gate {
                    // apply_5th_power(cs, value, None)?
                    inner_apply_5th_power(cs, value, None, custom_gate)?
                } else {
                    let square = value.square(cs)?;
                    let quad = square.square(cs)?;
                    quad.mul(cs, value)?
                };
                *lc = LinearCombination::from(result);
            }
        }
    }

    return Ok(());
}

// This function computes power of inverse of alpha to each element of state.
// By custom gate support, it costs only single gate. Under the hood, it proves
// that 5th power of each element of state is equal to itself.(x^(1/5)^5==x)
fn sbox_alpha_inv<E: Engine, CS: ConstraintSystem<E>, const WIDTH: usize>(
    cs: &mut CS,
    alpha_inv: &[u64],
    alpha: &u64,
    prev_state: &mut [LinearCombination<E>; WIDTH],
    custom_gate: CustomGate,
) -> Result<(), SynthesisError> {
    let use_custom_gate = match custom_gate {
        CustomGate::None => false,
        _ => true,
    };

    if *alpha != 5u64 {
        unimplemented!("only inverse for 5th power is supported!")
    }

    for lc in prev_state.iter_mut() {
        match lc.clone().into_num(cs)? {
            Num::Constant(value) => {
                let result = value.pow(alpha_inv);
                *lc = LinearCombination::zero();
                lc.add_assign_constant(result);
            }
            Num::Variable(ref value) => {
                let wit: Option<E::Fr> = value.get_value().map(|base| {
                    let result = base.pow(alpha_inv);
                    result
                });

                let powered = AllocatedNum::alloc(cs, || wit.grab())?;

                if use_custom_gate {
                    // let _ = apply_5th_power(cs, &powered, Some(*value))?;
                    let _ = inner_apply_5th_power(cs, &powered, Some(*value), custom_gate)?;
                } else {
                    let squared = powered.square(cs)?;
                    let quad = squared.square(cs)?;

                    let mut term = MainGateTerm::<E>::new();
                    let fifth_term = ArithmeticTerm::from_variable(quad.get_variable())
                        .mul_by_variable(powered.get_variable());
                    let el_term = ArithmeticTerm::from_variable(value.get_variable());
                    term.add_assign(fifth_term);
                    term.sub_assign(el_term);
                    cs.allocate_main_gate(term)?;
                };
                *lc = LinearCombination::from(powered);
            }
        }
    }

    return Ok(());
}


// This function computes power of inverse of alpha to each element of state.
// By custom gate support, it costs only single gate. Under the hood, it proves
// that 5th power of each element of state is equal to itself.(x^(1/5)^5==x)
fn sbox_alpha_inv_via_add_chain<E: Engine, CS: ConstraintSystem<E>, const WIDTH: usize>(
    cs: &mut CS,
    addition_chain: &[super::super::traits::Step],
    alpha: &u64,
    prev_state: &mut [LinearCombination<E>; WIDTH],
    custom_gate: CustomGate,
) -> Result<(), SynthesisError> {
    let use_custom_gate = match custom_gate {
        CustomGate::None => false,
        _ => true,
    };

    if *alpha != 5u64 {
        unimplemented!("only inverse for 5th power is supported!")
    }

    for lc in prev_state.iter_mut() {
        match lc.clone().into_num(cs)? {
            Num::Constant(value) => {
                let mut scratch = smallvec::SmallVec::<[E::Fr; 512]>::new();
                let result = add_chain_pow_smallvec(value, addition_chain, &mut scratch);
                *lc = LinearCombination::zero();
                lc.add_assign_constant(result);
            }
            Num::Variable(ref value) => {
                let wit: Option<E::Fr> = value.get_value().map(|el| {
                    let mut scratch = smallvec::SmallVec::<[E::Fr; 512]>::new();
                    let result = add_chain_pow_smallvec(el, addition_chain, &mut scratch);

                    result
                });

                let powered = AllocatedNum::alloc(cs, || wit.grab())?;

                if use_custom_gate {
                    // let _ = apply_5th_power(cs, &powered, Some(*value))?;
                    let _ = inner_apply_5th_power(cs, &powered, Some(*value), custom_gate)?;
                } else {
                    let squared = powered.square(cs)?;
                    let quad = squared.square(cs)?;

                    let mut term = MainGateTerm::<E>::new();
                    let fifth_term = ArithmeticTerm::from_variable(quad.get_variable())
                        .mul_by_variable(powered.get_variable());
                    let el_term = ArithmeticTerm::from_variable(value.get_variable());
                    term.add_assign(fifth_term);
                    term.sub_assign(el_term);
                    cs.allocate_main_gate(term)?;
                };
                *lc = LinearCombination::from(powered);
            }
        }
    }

    return Ok(());
}

fn inner_apply_5th_power<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    value: &AllocatedNum<E>,
    existing_5th: Option<AllocatedNum<E>>,
    custom_gate: CustomGate,
) -> Result<AllocatedNum<E>, SynthesisError> {
    assert!(
        CS::Params::HAS_CUSTOM_GATES,
        "CS should have custom gate support"
    );
    match custom_gate {
        CustomGate::QuinticWidth4 => {
            assert!(
                CS::Params::STATE_WIDTH >= 4,
                "state width should equal or large then 4"
            );
            apply_5th_power(
                cs,
                value,
                existing_5th,
            )
        }
        CustomGate::QuinticWidth3 => {
            assert!(
                CS::Params::STATE_WIDTH >= 3,
                "state width should equal or large then 3"
            );
            apply_5th_power(
                cs,
                value,
                existing_5th,
            )
        }
        _ => unimplemented!(),
    }
}

// #[cfg(test)]
// mod test {
//     use {
//         bellman::{bn256::Bn256, PrimeField},
//         plonk::circuit::linear_combination::LinearCombination,
//     };
//     use std::convert::TryInto;

//     use super::super::tests::test_inputs;
//     use crate::tests::{init_cs, init_cs_no_custom_gate};

//     use super::*;

//     fn run_test_sbox<E: Engine, CS: ConstraintSystem<E>, const N: usize>(
//         cs: &mut CS,
//         power: Sbox,
//         number_of_rounds: usize,
//         custom_gate: CustomGate,
//         use_partial_state: bool,
//         use_allocated: bool,
//     ) {
//         let (mut state, state_as_nums) = test_inputs::<E, _, N>(cs, use_allocated);

//         let mut state_as_lc = vec![];
//         for num in std::array::IntoIter::new(state_as_nums) {
//             let lc = LinearCombination::from(num);
//             state_as_lc.push(lc);
//         }
//         let mut state_as_lc: [LinearCombination<E>; N] = state_as_lc.try_into().expect("array");

//         let state_range = if use_partial_state {
//             Some(0..1)
//         } else {
//             Some(0..N)
//         };

//         assert_eq!(state_range.as_ref().unwrap().len(), N);

//         for _ in 0..number_of_rounds {
//             crate::common::sbox::sbox::<E>(&power, &mut state);
//             sbox(
//                 cs,
//                 &power,
//                 &mut state_as_lc,
//                 state_range.clone(),
//                 custom_gate.clone(),
//             )
//             .expect("5th apply successfu");
//         }
//     }
//     fn test_sbox(power: Sbox) {
//         let cs = &mut init_cs::<Bn256>();

//         const INPUT_LENGTH: usize = 3;
//         const NUM_ROUNDS: usize = 1;

//         run_test_sbox::<_, _, INPUT_LENGTH>(
//             cs,
//             power.clone(),
//             NUM_ROUNDS,
//             CustomGate::QuinticWidth4,
//             false,
//             true,
//         ); // variable inputs
//         println!(
//             "{:?} sbox takes {} gates with custom gate(width4) for {} iteration ",
//             power,
//             cs.n(),
//             NUM_ROUNDS,
//         );
//         let mut end = cs.n();

//         run_test_sbox::<_, _, INPUT_LENGTH>(
//             cs,
//             power.clone(),
//             NUM_ROUNDS,
//             CustomGate::QuinticWidth3,
//             false,
//             true,
//         ); // variable inputs
//         println!(
//             "{:?} takes {} gates with custom gate(width3) for {} iteration ",
//             power,
//             cs.n()-end,
//             NUM_ROUNDS,
//         );
//         end = cs.n();
//         run_test_sbox::<_, _, INPUT_LENGTH>(
//             cs,
//             power.clone(),
//             NUM_ROUNDS,
//             CustomGate::None,
//             false,
//             true,
//         ); // variable inputs + no custom gate
//         println!(
//             "{:?} takes {} gates without custom gate for {} iteration ",
//             power,
//             cs.n() - end,
//             NUM_ROUNDS,
//         );
//         run_test_sbox::<_, _, INPUT_LENGTH>(
//             cs,
//             power.clone(),
//             NUM_ROUNDS,
//             CustomGate::None,
//             false,
//             false,
//         ); // constant inputs + no custom gate
//         run_test_sbox::<_, _, INPUT_LENGTH>(
//             cs,
//             power.clone(),
//             NUM_ROUNDS,
//             CustomGate::QuinticWidth4,
//             false,
//             false,
//         ); // constant inputs
//         run_test_sbox::<_, _, INPUT_LENGTH>(
//             cs,
//             power.clone(),
//             NUM_ROUNDS,
//             CustomGate::QuinticWidth3,
//             false,
//             false,
//         ); // constant inputs

//         cs.finalize();
//         assert!(cs.is_satisfied());
//     }

//     #[test]
//     fn test_sbox_quintic() {
//         let alpha = Sbox::Alpha(5);
//         test_sbox(alpha);
//     }
//     #[test]
//     fn test_sbox_quintic_inv() {
//         let alpha = 5;
//         let alpha_inv = Sbox::AlphaInverse(compute_inverse_alpha::<Bn256, 4>(alpha).to_vec(), 5);
//         test_sbox(alpha_inv);
//     }

//     fn compute_inverse_alpha<E: Engine, const N: usize>(alpha: u64) -> [u64; N] {
//         crate::common::utils::compute_gcd::<E, N>(alpha).expect("inverse of alpha")
//     }
// }
