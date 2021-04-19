use super::{RescueEngine, RescueHashParams};
use super::StatefulRescue;
use crate::bellman::pairing::ff::{PrimeField, PrimeFieldRepr};
use crate::bellman::pairing::{Engine, GenericCurveAffine};
use crate::byteorder::{ByteOrder, BigEndian};

use crate::bellman::plonk::commitments::transcript::{Transcript, Prng};

use super::*;

use crate::plonk::circuit::bigint::bigint::*;
use crate::plonk::circuit::bigint::field::*;

#[derive(Clone)]
pub struct RescueTranscriptForRNS<'a, E: RescueEngine> {
    state: StatefulRescue<'a, E>,
    rns_parameters: &'a RnsParameters<E, <<E as Engine>::G1Affine as GenericCurveAffine>::Base>
}

// impl<'a, E: RescueEngine> RescueTranscriptForRNS<'a, E> {
//     pub fn from_params(params: &'a E::Params) -> Self {
//         let stateful = StatefulRescue::new(params);

//         Self {
//             state: stateful
//         }
//     }
// }


impl<'a, E: RescueEngine> Prng<E::Fr> for RescueTranscriptForRNS<'a, E> {
    type Input = E::Fr;
    type InitializationParameters = (&'a E::Params, &'a RnsParameters<E, <<E as Engine>::G1Affine as GenericCurveAffine>::Base>);

    fn new() -> Self {
        unimplemented!("must initialize from parameters");
    }

    fn new_from_params(params: Self::InitializationParameters) -> Self {
        let (rescue_params, rns_params) = params;
        let stateful = StatefulRescue::new(rescue_params);

        Self {
            state: stateful,
            rns_parameters: rns_params,
        }
    }

    fn commit_input(&mut self, input: &Self::Input) {
        self.state.absorb_single_value(*input);
    }

    fn get_challenge(&mut self) -> E::Fr {
        self.state.pad_if_necessary();
        let value = self.state.squeeze_out_single();

        value
    }
}


impl<'a, E: RescueEngine> Transcript<E::Fr> for RescueTranscriptForRNS<'a, E> {
    fn commit_bytes(&mut self, _bytes: &[u8]) {
        unimplemented!();
    }

    fn commit_field_element(&mut self, element: &E::Fr) {
        self.state.absorb_single_value(*element);
    }

    fn get_challenge_bytes(&mut self) -> Vec<u8> {
        unimplemented!();
    }

    fn commit_fe<FF: PrimeField>(&mut self, element: &FF) 
    {
        let expected_field_char = <<<E as Engine>::G1Affine as GenericCurveAffine>::Base as PrimeField>::char();
        let this_field_char = FF::char();
        assert_eq!(expected_field_char.as_ref(), this_field_char.as_ref(), "can only commit base curve field element");

        // convert into RNS limbs

        let params = self.rns_parameters;

        let limb_values = if params.can_allocate_from_double_limb_witness() {
            let mut num_witness = params.num_limbs_for_in_field_representation / 2;
            if params.num_limbs_for_in_field_representation % 2 != 0 {
                num_witness += 1;
            }

            let value = fe_to_biguint(element);

            let witness_limbs = split_into_fixed_number_of_limbs(
                value, 
                params.binary_limbs_params.limb_size_bits * 2, 
                num_witness
            );

            let witness_as_fe: Vec<E::Fr> = witness_limbs.into_iter().map(|el| biguint_to_fe(el)).collect();

            witness_as_fe
        } else {
            let value = fe_to_biguint(element);

            let witness_limbs = split_into_fixed_number_of_limbs(
                value, 
                params.binary_limbs_params.limb_size_bits, 
                params.num_binary_limbs
            );

            let witness_as_fe: Vec<E::Fr> = witness_limbs.into_iter().map(|el| biguint_to_fe(el)).collect();

            witness_as_fe
        };

        for el in limb_values.into_iter() {
            self.state.absorb_single_value(el);
        }
    }
}