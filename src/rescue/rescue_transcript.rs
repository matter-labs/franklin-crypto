use super::{RescueEngine, RescueHashParams};
use super::StatefulRescue;
use crate::bellman::pairing::ff::{PrimeField, PrimeFieldRepr};
use crate::byteorder::{ByteOrder, BigEndian};

use crate::bellman::plonk::commitments::transcript::{Transcript, Prng};

use super::*;

#[derive(Clone)]
pub struct RescueTranscript<'a, E: RescueEngine> {
    state: StatefulRescue<'a, E>,
}

impl<'a, E: RescueEngine> RescueTranscript<'a, E> {
    pub fn from_params(params: &'a E::Params) -> Self {
        let stateful = StatefulRescue::new(params);

        Self {
            state: stateful
        }
    }
}


impl<'a, E: RescueEngine> Prng<E::Fr> for RescueTranscript<'a, E> {
    type Input = E::Fr;
    type InitializationParameters = &'a E::Params;

    fn new() -> Self {
        unimplemented!("must initialize from parameters");
    }

    fn new_from_params(params: Self::InitializationParameters) -> Self {
        Self::from_params(params)
    }

    fn commit_input(&mut self, input: &Self::Input) {
        self.state.absorb_single_value(*input);
    }

    fn get_challenge(&mut self) -> E::Fr {
        let value = self.state.squeeze_out_single();

        value
    }
}


impl<'a, E: RescueEngine> Transcript<E::Fr> for RescueTranscript<'a, E> {
    fn commit_bytes(&mut self, bytes: &[u8]) {
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
        // we assume that FF is strictly smaller than F (in bitlength)

        let repr = element.into_repr();
        let mut bytes: Vec<u8> = vec![0u8; <E::Fr as PrimeField>::CAPACITY as usize / 8];
        //repr.write_le(&mut bytes[..]).expect("should write");

        // let mut repr_F = <E::Fr as PrimeField>::Repr::default();
        // repr_F.read_le(&bytes[..]).expect("should read");
        // let res = E::Fr::from_repr(repr_F).expect("should convert");

        let res = E::Fr::zero();

        self.state.absorb_single_value(res);
    }
}