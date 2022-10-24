// use rand::XorShiftRng;
// // plonk::circuit::rescue_copy::*;
// use plonk::circuit::Width4WithCustomGates;
// use bellman::plonk::better_better_cs::cs::TrivialAssembly;
// use plonk::circuit::Engine;
// use bellman::plonk::better_better_cs::gates::main_gate_with_d_next::Width4MainGateWithDNext;
// use bellman::plonk::better_better_cs::cs::PlonkCsWidth4WithNextStepParams;
// use rescue::bn256::Bn256RescueParams;
// use rescue::StatefulRescue;
// use plonk::circuit::rescue_copy::rescue::params::RescueParams;
// use bellman::pairing::ff::{
//     Field,
//     PrimeField
// };
// use bellman::pairing::bn256::{Bn256, Fr};
// use plonk::circuit::rescue::rescue_hash;
// use plonk::circuit::rescue_copy::sponge::GenericSponge;

// pub(crate) fn init_rng() -> XorShiftRng {
//     XorShiftRng::from_seed(crate::common::TEST_SEED)
// }
// pub(crate) fn init_cs<E: Engine>(
// ) -> TrivialAssembly<E, Width4WithCustomGates, Width4MainGateWithDNext> {
//     TrivialAssembly::<E, Width4WithCustomGates, Width4MainGateWithDNext>::new()
// }
// pub(crate) fn init_cs_no_custom_gate<E: Engine>(
// ) -> TrivialAssembly<E, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext> {
//     TrivialAssembly::<E, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new()
// }

// fn test_inputs<E: Engine, const L: usize>() -> [E::Fr; L] {
//     let rng = &mut init_rng();
//     let mut inputs = [E::Fr::zero(); L];
//     for inp in inputs.iter_mut(){
//         *inp = E::Fr::rand(rng);
//     }

//     inputs
// }

// #[test]
// fn test_rescue_bn256_fixed_length() {
//     const INPUT_LENGTH: usize = 2;
//     let rng = &mut init_rng();
//     let input = (0..INPUT_LENGTH).map(|_| Fr::rand(rng)).collect::<Vec<Fr>>();

//     let old_params = Bn256RescueParams::new_checked_2_into_1();
//     let expected = rescue_hash::<Bn256>(&old_params, &input);

//     let actual =
//         rescue_hash::<Bn256, INPUT_LENGTH>(&input.try_into().expect("static vector"));
//     assert_eq!(expected[0], actual[0]);
// }

// #[test]
// fn test_poseidon_bn256_fixed_length() {
//     // use poseidon_hash::bn256::Bn256PoseidonParams;
//     // const WIDTH: usize = 3;
//     // const RATE: usize = 2;
//     // let rng = &mut init_rng();
//     // let input = (0..2).map(|_| Fr::rand(rng)).collect::<Vec<Fr>>();

//     // let old_params = Bn256PoseidonParams::new_checked_2_into_1();
//     // let expected = poseidon_hash::poseidon_hash::<Bn256>(&old_params, &input);

//     // let actual =
//     //     crate::poseidon::poseidon_hash(&input);
//     // assert_eq!(expected[0], actual[0]);
// }

// #[test]
// fn test_rescue_params() {
//     const WIDTH: usize = 3;
//     const RATE: usize = 2;

//     let old_params = Bn256RescueParams::new_checked_2_into_1();

//     let (new_params, _, _) = crate::rescue::params::compute_params::<Bn256, RATE, WIDTH>();

//     let number_of_rounds = new_params.full_rounds;

//     for round in 0..number_of_rounds {
//         assert_eq!(
//             old_params.round_constants(round as u32),
//             new_params.constants_of_round(round)
//         )
//     }

//     for row in 0..WIDTH {
//         assert_eq!(
//             old_params.mds_matrix_row(row as u32),
//             new_params.mds_matrix[row]
//         );
//     }
// }

// #[test]
// fn test_poseidon_params() {
//     // const WIDTH: usize = 3;
//     // const RATE: usize = 2;
//     // use franklin_crypto::bellman::bn256::Bn256;

//     // let old_params = Bn256PoseidonParams::new_checked_2_into_1();
//     // let (new_params, _) = crate::poseidon::params::poseidon_params::<Bn256, RATE, WIDTH>();

//     // let number_of_rounds = new_params.full_rounds;

//     // for round in 0..number_of_rounds {
//     //     assert_eq!(
//     //         old_params.round_constants(round as u32),
//     //         new_params.constants_of_round(round)
//     //     )
//     // }

//     // for row in 0..WIDTH {
//     //     assert_eq!(
//     //         old_params.mds_matrix_row(row as u32),
//     //         new_params.mds_matrix[row]
//     //     );
//     // }
// }

// #[test]
// fn test_poseidon_hash_var_len() {
//     // const WIDTH: usize = 3;
//     // const RATE: usize = 2;
//     // let mut el = Fr::one();
//     // el.double();

//     // let input = vec![el; 2];

//     // let original_params = Bn256PoseidonParams::new_checked_2_into_1();
//     // let mut original_poseidon = PoseidonSponge::<Bn256>::new(&original_params);
//     // original_poseidon.absorb(&input);
//     // let mut expected = [Fr::zero(); 2];
//     // expected[0] = original_poseidon.squeeze_out_single();
//     // expected[1] = original_poseidon.squeeze_out_single();

//     // let new_params = PoseidonParams::<Bn256, RATE, WIDTH>::default();
//     // let mut hasher = GenericHasher::new_from_params(&new_params);
//     // hasher.absorb_multiple(&input);
//     // let actual = hasher.squeeze(None);

//     // assert_eq!(actual, expected);
// }

// #[test]
// fn test_rescue_hash_var_len() {
//     const WIDTH: usize = 3;
//     const RATE: usize = 2;
//     let mut el = Fr::one();
//     el.double();

//     let input = test_inputs::<Bn256, 2>();

//     let original_params = Bn256RescueParams::new_checked_2_into_1();
//     let mut original_rescue = StatefulRescue::<Bn256>::new(&original_params);
//     original_rescue.absorb(&input);
//     let mut expected = [Fr::zero(); 2];
//     expected[0] = original_rescue.squeeze_out_single();
//     expected[1] = original_rescue.squeeze_out_single();

//     let new_params = RescueParams::<Bn256, RATE, WIDTH>::default();
//     let mut hasher = GenericSponge::new();
//     hasher.absorb_multiple(&input,&new_params);
//     let mut actual = [Fr::zero(); 2];
//     actual[0] = hasher.squeeze(&new_params).expect("an element");
//     actual[1] = hasher.squeeze(&new_params).expect("an element");

//     assert_eq!(actual, expected);
// }



// #[test]
// fn test_new_generic_hasher_fixed_length_single_output_with_hardcoded_input() {
//     const LENGTH: usize = 3;

//     let i1 = hex::decode("29d8221459d2f65b3ff75fe514f17dce17b76735fb60d834ee07faa88894590d").unwrap();
//     let i2 = hex::decode("009d3ac090220e3539f4cdcaf48f246aecb8b340bffa751fe47ed70576a3bbc2").unwrap();
//     let i3 = hex::decode("0000000000000000000000000000000000000000000000000000000000000090").unwrap();

//     let mut el1_repr = <Fr as PrimeField>::Repr::default();
//     el1_repr.read_be(&i1[..]).unwrap();
//     let el1 = Fr::from_repr(el1_repr).unwrap();
    
//     let mut el2_repr = <Fr as PrimeField>::Repr::default();
//     el2_repr.read_be(&i2[..]).unwrap();
//     let el2 = Fr::from_repr(el2_repr).unwrap();
    
//     let mut el3_repr = <Fr as PrimeField>::Repr::default();
//     el3_repr.read_be(&i3[..]).unwrap();
//     let el3 = Fr::from_repr(el3_repr).unwrap();

//     let input = [el1, el2, el3];
    

//     let params = RescueParams::<Bn256, 2, 3>::default();

//     let mut original_params  = Bn256RescueParams::new_checked_2_into_1();
//     original_params.set_allow_custom_gate(true);

//     let original = rescue_hash::<Bn256>(&original_params, &input);
    
//     let expected = crate::rescue::rescue_hash::<Bn256, LENGTH>(&input);

//     let actual = GenericSponge::<_, 2, 3>::hash(&input, &params, None);

//     assert_eq!(original[0], expected[0]);
//     assert_eq!(expected[0], actual[0]);
// }

// #[test]
// fn test_var_length_multiple_absorbs_without_padding_when_pad_needed() {
//     const WIDTH: usize = 3;
//     const RATE: usize = 2;
//     const LENGTH: usize = 7;

//     let input = test_inputs::<Bn256, LENGTH>();

//     let original_params = Bn256RescueParams::new_checked_2_into_1();

//     let mut original_rescue = StatefulRescue::<Bn256>::new(&original_params);
//     original_rescue.absorb(&input[..2]);
//     original_rescue.absorb(&input[2..4]);
//     original_rescue.absorb(&input[4..6]);
//     original_rescue.absorb(&input[6..]);

//     let expected = original_rescue.squeeze_out_single();

//     let new_params = RescueParams::<Bn256, RATE, WIDTH>::default();
//     let mut generic_hasher = GenericSponge::new();
//     generic_hasher.absorb_multiple(&input[..2], &new_params);
//     generic_hasher.absorb_multiple(&input[2..4], &new_params);
//     generic_hasher.absorb_multiple(&input[4..6], &new_params);
//     generic_hasher.absorb_multiple(&input[6..], &new_params);

//     let actual = generic_hasher.squeeze(&new_params).expect("a squeezed elem");

//     assert_eq!(actual, expected);
// }

// #[test]
// #[should_panic(expected="padding was necessary!")]
// fn test_var_length_single_absorb_without_padding_when_pad_needed() {
//     const WIDTH: usize = 3;
//     const RATE: usize = 2;
//     const LENGTH: usize = 1;

//     let input = test_inputs::<Bn256, LENGTH>();    

//     let new_params = RescueParams::<Bn256, RATE, WIDTH>::default();
//     let mut generic_hasher = GenericSponge::new();
//     generic_hasher.absorb(input[0], &new_params);

//     let _ = generic_hasher.squeeze(&new_params).is_none();

//     let original_params = Bn256RescueParams::new_checked_2_into_1();
//     let mut original_rescue = StatefulRescue::<Bn256>::new(&original_params);
//     original_rescue.absorb_single_value(input[0]);
//     let _ = original_rescue.squeeze_out_single();
// }

// #[test]
// fn test_multiple_absorb_steps() {
//     const WIDTH: usize = 3;
//     const RATE: usize = 2;
//     const LENGTH: usize = 7;

//     let input = test_inputs::<Bn256, LENGTH>();

//     let original_params = Bn256RescueParams::new_checked_2_into_1();

//     let mut original_rescue = StatefulRescue::<Bn256>::new(&original_params);
//     original_rescue.absorb(&input[..2]);
//     original_rescue.absorb(&input[2..4]);
//     original_rescue.absorb(&input[4..6]);
//     original_rescue.absorb(&input[6..]);
//     original_rescue.pad_if_necessary();

//     let expected = original_rescue.squeeze_out_single();

//     let new_params = RescueParams::<Bn256, RATE, WIDTH>::default();
//     let mut generic_hasher = GenericSponge::new();
//     generic_hasher.absorb_multiple(&input[..2], &new_params);
//     generic_hasher.absorb_multiple(&input[2..4], &new_params);
//     generic_hasher.absorb_multiple(&input[4..6], &new_params);
//     generic_hasher.absorb_multiple(&input[6..], &new_params);
//     generic_hasher.pad_if_necessary();

//     let actual = generic_hasher.squeeze(&new_params).expect("a squeezed elem");

//     assert_eq!(actual, expected);
// }
// #[test]
// fn test_new_generic_hasher_single_absorb_compare_with_old_rescue_sponge() {
//     const WIDTH: usize = 3;
//     const RATE: usize = 2;
//     const LENGTH: usize =1;

//     let input = test_inputs::<Bn256, LENGTH>();

//     let original_params = Bn256RescueParams::new_checked_2_into_1();

//     let mut original_rescue = StatefulRescue::<Bn256>::new(&original_params);
//     original_rescue.absorb_single_value(input[0]);
//     original_rescue.pad_if_necessary();
    
//     let expected = original_rescue.squeeze_out_single();

//     let new_params = RescueParams::<Bn256, RATE, WIDTH>::default();
//     let mut generic_hasher = GenericSponge::new();
//     generic_hasher.absorb(input[0], &new_params);
//     generic_hasher.pad_if_necessary();


//     let actual = generic_hasher.squeeze(&new_params).expect("a squeezed elem");

//     assert_eq!(actual, expected);
// }

// #[test]
// fn test_generic_hasher_squeeze_before_no_absorbing() {
//     const WIDTH: usize = 3;
//     const RATE: usize = 2;
//     let params = RescueParams::default();
//     let mut sponge = GenericSponge::<Bn256, RATE, WIDTH>::new();

//     let _ = sponge.squeeze(&params).is_none();
// }

// #[test]
// fn test_multiple_squeeze() {
//     const WIDTH: usize = 3;
//     const RATE: usize = 2;
//     const LENGTH: usize = 3;

//     let input = test_inputs::<Bn256, LENGTH>();

//     let original_params = Bn256RescueParams::new_checked_2_into_1();

//     let mut original_rescue = StatefulRescue::<Bn256>::new(&original_params);
//     original_rescue.absorb(&input);        
//     let mut expected = [Fr::zero(); RATE];
//     expected[0] = original_rescue.squeeze_out_single();
//     expected[1] = original_rescue.squeeze_out_single();

//     let new_params = RescueParams::<Bn256, RATE, WIDTH>::default();
//     let mut generic_hasher = GenericSponge::new();
//     generic_hasher.absorb_multiple(&input, &new_params);
//     let mut actual = [Fr::zero(); RATE];
//     actual[0] = generic_hasher.squeeze(&new_params).expect("a squeezed elem");
//     actual[1] = generic_hasher.squeeze(&new_params).expect("a squeezed elem");

//     assert_eq!(expected, actual);
// }

// #[test]
// fn test_excessive_multiple_squeeze() {
//     const WIDTH: usize = 3;
//     const RATE: usize = 2;        
//     const ILENGTH: usize = 2;

//     let input = test_inputs::<Bn256, ILENGTH>();
//     let params = RescueParams::<Bn256, RATE, WIDTH>::default();

//     let mut generic_hasher = GenericSponge::new();

//     generic_hasher.absorb_multiple(&input, &params);

//     let _ = generic_hasher.squeeze(&params).expect("a squeezed elem");
//     let _ = generic_hasher.squeeze(&params).expect("a squeezed elem");
//     let _ = generic_hasher.squeeze(&params).is_none();

// }
// #[test]
// fn test_rate_absorb_and_squeeze() {
//     const WIDTH: usize = 3;
//     const RATE: usize = 2;
//     const LENGTH: usize = RATE;

//     let input = test_inputs::<Bn256, LENGTH>();

//     let original_params = Bn256RescueParams::new_checked_2_into_1();

//     let mut original_rescue = StatefulRescue::<Bn256>::new(&original_params);
//     original_rescue.absorb(&input);
    
//     let expected = original_rescue.squeeze_out_single();

//     let new_params = RescueParams::<Bn256, RATE, WIDTH>::default();
//     let mut generic_hasher = GenericSponge::new();
//     generic_hasher.absorb_multiple(&input, &new_params);

//     let actual = generic_hasher.squeeze(&new_params).expect("a squeezed elem");

//     assert_eq!(actual, expected);

// }