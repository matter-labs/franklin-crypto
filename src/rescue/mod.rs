use bellman::pairing::ff::{Field, PrimeField, PrimeFieldRepr};
use bellman::pairing::{Engine};
use std::marker::PhantomData;
use super::group_hash::GroupHasher;

use rand::{Rand, Rng};

pub mod bn256;
pub mod rescue_transcript;

pub trait SBox<E: Engine>: Sized + Clone {
    fn apply(&self, elements: &mut [E::Fr]);
}

#[derive(Clone)]
pub struct CubicSBox<E: Engine> {
    pub _marker: PhantomData<E>
}

impl<E: Engine>SBox<E> for CubicSBox<E> {

    fn apply(&self, elements: &mut [E::Fr]) {
        for element in elements.iter_mut() {
            let mut squared = *element;
            squared.square();
            element.mul_assign(&squared);
        }
    }
}

#[derive(Clone)]
pub struct QuinticSBox<E: Engine> {
    pub _marker: PhantomData<E>
}

impl<E: Engine>SBox<E> for QuinticSBox<E> {
    fn apply(&self, elements: &mut [E::Fr]) {
        for element in elements.iter_mut() {
            let mut quad = *element;
            quad.square();
            quad.square();
            element.mul_assign(&quad);
        }
    }
}

#[derive(Clone)]
pub struct PowerSBox<E: Engine> {
    pub power: <E::Fr as PrimeField>::Repr,
    pub inv: u64,
}

impl<E: Engine>SBox<E> for PowerSBox<E> {
    fn apply(&self, elements: &mut [E::Fr]) {
        for element in elements.iter_mut() {
            *element = element.pow(&self.power);
        }
    }
}

#[derive(Clone)]
pub struct InversionSBox<E: Engine> {
    pub _marker: PhantomData<E>
}

fn batch_inversion<E: Engine>(v: &mut [E::Fr]) {
    // Montgomery’s Trick and Fast Implementation of Masked AES
    // Genelle, Prouff and Quisquater
    // Section 3.2

    // First pass: compute [a, ab, abc, ...]
    let mut prod = Vec::with_capacity(v.len());
    let mut tmp = E::Fr::one();
    for g in v.iter()
        // Ignore zero elements
        .filter(|g| !g.is_zero())
    {
        tmp.mul_assign(&g);
        prod.push(tmp);
    }

    // Invert `tmp`.
    tmp = tmp.inverse().unwrap(); // Guaranteed to be nonzero.

    // Second pass: iterate backwards to compute inverses
    for (g, s) in v.iter_mut()
                    // Backwards
                    .rev()
                    // Ignore normalized elements
                    .filter(|g| !g.is_zero())
                    // Backwards, skip last element, fill in one for last term.
                    .zip(prod.into_iter().rev().skip(1).chain(Some(E::Fr::one())))
    {
        // tmp := tmp * g.z; g.z := tmp * s = 1/z
        let mut newtmp = tmp;
        newtmp.mul_assign(&g);
        *g = tmp;
        g.mul_assign(&s);
        tmp = newtmp;
    }
}

impl<E: Engine>SBox<E> for InversionSBox<E> {
    fn apply(&self, elements: &mut [E::Fr]) {
        batch_inversion::<E>(elements);
    }
}

use crate::circuit::rescue::CsSBox;

pub trait RescueHashParams<E: Engine>: RescueParamsInternal<E> {
    type SBox0: CsSBox<E>;
    type SBox1: CsSBox<E>;
    fn capacity(&self) -> u32;
    fn rate(&self) -> u32;
    fn state_width(&self) -> u32 {
        self.capacity() + self.rate()
    }
    fn num_rounds(&self) -> u32;
    fn round_constants(&self, round: u32) -> &[E::Fr];
    fn mds_matrix_row(&self, row: u32) -> &[E::Fr];
    fn security_level(&self) -> u32;
    fn output_len(&self) -> u32 {
        self.capacity()
    }
    fn absorbtion_cycle_len(&self) -> u32 {
        self.rate()
    }
    fn compression_rate(&self) -> u32 {
        self.absorbtion_cycle_len() / self.output_len()
    }

    fn sbox_0(&self) -> &Self::SBox0;
    fn sbox_1(&self) -> &Self::SBox1;
}

pub trait RescueParamsInternal<E: Engine>: Send + Sync + Sized + Clone {
    fn set_round_constants(&mut self, to: Vec<E::Fr>);
}

pub trait RescueEngine: Engine {
    type Params: RescueHashParams<Self>; 
}

pub fn rescue_hash<E: RescueEngine>(
    params: &E::Params,
    input: &[E::Fr]
) -> Vec<E::Fr> {
    sponge_fixed_length::<E>(params, input)
}

fn sponge_fixed_length<E: RescueEngine>(
    params: &E::Params,
    input: &[E::Fr]
) -> Vec<E::Fr> {
    assert!(input.len() > 0);
    assert!(input.len() < 256);
    let input_len = input.len() as u64;
    let mut state = vec![E::Fr::zero(); params.state_width() as usize];
    // specialized for input length
    let mut repr = <E::Fr as PrimeField>::Repr::default();
    repr.as_mut()[0] = input_len;
    let len_fe = <E::Fr as PrimeField>::from_repr(repr).unwrap();
    let last_state_elem_idx = state.len() - 1;
    state[last_state_elem_idx] = len_fe;

    let rate = params.rate() as usize;
    let mut absorbtion_cycles = input.len() / rate;
    if input.len() % rate != 0 {
        absorbtion_cycles += 1;
    }
    let padding_len = absorbtion_cycles * rate - input.len();
    let padding = vec![E::Fr::one(); padding_len];

    let mut it = input.iter().chain(&padding);
    for _ in 0..absorbtion_cycles {
        for i in 0..rate {
            state[i].add_assign(&it.next().unwrap());
        }
        state = rescue_mimc::<E>(params, &state);
    }

    debug_assert!(it.next().is_none());

    state[..(params.capacity() as usize)].to_vec()
}   

pub fn rescue_mimc<E: RescueEngine>(
    params: &E::Params,
    old_state: &[E::Fr]
) -> Vec<E::Fr> {
    let mut state = old_state.to_vec();
    let mut mds_application_scratch = vec![E::Fr::zero(); state.len()];
    assert_eq!(state.len(), params.state_width() as usize);
    // add round constatnts
    for (s, c)  in state.iter_mut()
                .zip(params.round_constants(0).iter()) {
        s.add_assign(c);
    }

    // parameters use number of rounds that is number of invocations of each SBox,
    // so we double
    for round_num in 0..(2*params.num_rounds()) {
        // apply corresponding sbox
        if round_num & 1u32 == 0 {
            params.sbox_0().apply(&mut state);
        } else {
            params.sbox_1().apply(&mut state);
        }

        // add round keys right away
        mds_application_scratch.copy_from_slice(params.round_constants(round_num + 1));

        // mul state by MDS
        for (row, place_into) in mds_application_scratch.iter_mut()
                                        .enumerate() {
            let tmp = scalar_product::<E>(& state[..], params.mds_matrix_row(row as u32));
            place_into.add_assign(&tmp);                                
            // *place_into = scalar_product::<E>(& state[..], params.mds_matrix_row(row as u32));
        }

        // place new data into the state
        state.copy_from_slice(&mds_application_scratch[..]);
    }

    state
}

fn scalar_product<E: Engine> (input: &[E::Fr], by: &[E::Fr]) -> E::Fr {
    assert!(input.len() == by.len());
    let mut result = E::Fr::zero();
    for (a, b) in input.iter().zip(by.iter()) {
        let mut tmp = *a;
        tmp.mul_assign(b);
        result.add_assign(&tmp);
    }

    result
}

// For simplicity we'll not generate a matrix using a way from the paper and sampling
// an element with some zero MSBs and instead just sample and retry
fn generate_mds_matrix<E: RescueEngine, R: Rng>(t: u32, rng: &mut R) -> Vec<E::Fr> {
    loop {
        let x: Vec<E::Fr> = (0..t).map(|_| rng.gen()).collect();
        let y: Vec<E::Fr> = (0..t).map(|_| rng.gen()).collect();

        let mut invalid = false;

        // quick and dirty check for uniqueness of x
        for i in 0..(t as usize) {
            if invalid {
                continue;
            }
            let el = x[i];
            for other in x[(i+1)..].iter() {
                if el == *other {
                    invalid = true;
                    break;
                }
            }
        }

        if invalid {
            continue;
        }

        // quick and dirty check for uniqueness of y
        for i in 0..(t as usize) {
            if invalid {
                continue;
            }
            let el = y[i];
            for other in y[(i+1)..].iter() {
                if el == *other {
                    invalid = true;
                    break;
                }
            }
        }

        if invalid {
            continue;
        }

        // quick and dirty check for uniqueness of x vs y
        for i in 0..(t as usize) {
            if invalid {
                continue;
            }
            let el = x[i];
            for other in y.iter() {
                if el == *other {
                    invalid = true;
                    break;
                }
            }
        }

        if invalid {
            continue;
        }

        // by previous checks we can be sure in uniqueness and perform subtractions easily
        let mut mds_matrix = vec![E::Fr::zero(); (t*t) as usize];
        for (i, x) in x.into_iter().enumerate() {
            for (j, y) in y.iter().enumerate() {
                let place_into = i*(t as usize) + j;
                let mut element = x;
                element.sub_assign(y);
                mds_matrix[place_into] = element;
            }
        }

        // now we need to do the inverse
        batch_inversion::<E>(&mut mds_matrix[..]);

        return mds_matrix;
    }
}

pub fn make_keyed_params<E: RescueEngine>(
    default_params: &E::Params,
    key: &[E::Fr]
) -> E::Params {
    // for this purpose we feed the master key through the rescue itself
    // in a sense that we make non-trivial initial state and run it with empty input

    assert_eq!(default_params.state_width() as usize, key.len());

    let mut new_round_constants = vec![];

    let mut state = key.to_vec();
    let mut mds_application_scratch = vec![E::Fr::zero(); state.len()];
    assert_eq!(state.len(), default_params.state_width() as usize);
    // add round constatnts
    for (s, c)  in state.iter_mut()
                .zip(default_params.round_constants(0).iter()) {
        s.add_assign(c);
    }

    // add to round constants
    new_round_constants.extend_from_slice(&state);

    // parameters use number of rounds that is number of invocations of each SBox,
    // so we double
    for round_num in 0..(2*default_params.num_rounds()) {
        // apply corresponding sbox
        if round_num & 1u32 == 0 {
            default_params.sbox_0().apply(&mut state);
        } else {
            default_params.sbox_1().apply(&mut state);
        }

        // add round keys right away
        mds_application_scratch.copy_from_slice(default_params.round_constants(round_num + 1));

        // mul state by MDS
        for (row, place_into) in mds_application_scratch.iter_mut()
                                        .enumerate() {
            let tmp = scalar_product::<E>(& state[..], default_params.mds_matrix_row(row as u32));
            place_into.add_assign(&tmp);                                
            // *place_into = scalar_product::<E>(& state[..], params.mds_matrix_row(row as u32));
        }

        // place new data into the state
        state.copy_from_slice(&mds_application_scratch[..]);

        new_round_constants.extend_from_slice(&state);
    }
    
    let mut new_params = default_params.clone();

    new_params.set_round_constants(new_round_constants);

    new_params
}
#[derive(Clone, Debug)]
enum RescueOpMode<E: RescueEngine> {
    AccumulatingToAbsorb(Vec<E::Fr>),
    SqueezedInto(Vec<E::Fr>)
}

#[derive(Clone, Debug)]
pub struct StatefulRescue<'a, E: RescueEngine> {
    params: &'a E::Params,
    internal_state: Vec<E::Fr>,
    mode: RescueOpMode<E>
}

impl<'a, E: RescueEngine> StatefulRescue<'a, E> {
    pub fn new(
        params: &'a E::Params
    ) -> Self {
        let op = RescueOpMode::AccumulatingToAbsorb(Vec::with_capacity(params.rate() as usize));

        StatefulRescue::<_> {
            params,
            internal_state: vec![E::Fr::zero(); params.state_width() as usize],
            mode: op
        }
    }

    pub fn specialize(
        &mut self,
        dst: u8
    ) {
        match self.mode {
            RescueOpMode::AccumulatingToAbsorb(ref into) => {
                assert_eq!(into.len(), 0, "can not specialize sponge that absorbed something")
            },
            _ => {
                panic!("can not specialized sponge in squeezing state");
            }
        }
        let dst = dst as u64;
        let mut repr = <E::Fr as PrimeField>::Repr::default();
        repr.as_mut()[0] = dst;
        let as_fe = <E::Fr as PrimeField>::from_repr(repr).unwrap();
        let last_state_elem_idx = self.internal_state.len() - 1;
        self.internal_state[last_state_elem_idx] = as_fe;
    }

    fn absorb_single_value(
        &mut self,
        value: E::Fr
    ) {
        match self.mode {
            RescueOpMode::AccumulatingToAbsorb(ref mut into) => {
                // two cases
                // either we have accumulated enough already and should to 
                // a mimc round before accumulating more, or just accumulate more
                let rate = self.params.rate() as usize;
                if into.len() < rate {
                    into.push(value);
                } else {
                    for i in 0..rate {
                        self.internal_state[i].add_assign(&into[i]);
                    }

                    self.internal_state = rescue_mimc::<E>(self.params, &self.internal_state);

                    into.truncate(0);
                    into.push(value);
                }
            },
            RescueOpMode::SqueezedInto(_) => {
                // we don't need anything from the output, so it's dropped

                let mut s = Vec::with_capacity(self.params.rate() as usize);
                s.push(value);

                let op = RescueOpMode::AccumulatingToAbsorb(s);
                self.mode = op;
            }
        }
    }

    pub fn absorb(
        &mut self,
        input: &[E::Fr]
    ) {
        assert!(input.len() > 0);
        let rate = self.params.rate() as usize;
        let mut absorbtion_cycles = input.len() / rate;
        if input.len() % rate != 0 {
            absorbtion_cycles += 1;
        }
        let padding_len = absorbtion_cycles * rate - input.len();
        let padding = vec![E::Fr::one(); padding_len];

        let it = input.iter().chain(&padding);

        for &val in it {
            self.absorb_single_value(val);
        }
    }

    pub fn pad_if_necessary(&mut self) {
        match self.mode {
            RescueOpMode::AccumulatingToAbsorb(ref mut into) => {
                let rate = self.params.rate() as usize;
                if into.len() != rate {
                    into.resize(rate, E::Fr::one());
                }
            },
            RescueOpMode::SqueezedInto(_) => {}
        }
    }

    pub fn squeeze_out_single(
        &mut self,
    ) -> E::Fr {
        match self.mode {
            RescueOpMode::AccumulatingToAbsorb(ref mut into) => {
                let rate = self.params.rate() as usize;
                assert_eq!(into.len(), rate, "padding was necessary!");
                // two cases
                // either we have accumulated enough already and should to 
                // a mimc round before accumulating more, or just accumulate more
                for i in 0..rate {
                    self.internal_state[i].add_assign(&into[i]);
                }
                self.internal_state = rescue_mimc::<E>(self.params, &self.internal_state);

                // we don't take full internal state, but only the rate
                let mut sponge_output = self.internal_state[0..rate].to_vec();
                let output = sponge_output.drain(0..1).next().unwrap();

                let op = RescueOpMode::SqueezedInto(sponge_output);
                self.mode = op;

                return output;
            },
            RescueOpMode::SqueezedInto(ref mut into) => {
                assert!(into.len() > 0, "squeezed state is depleted!");
                let output = into.drain(0..1).next().unwrap();

                return output;
            }
        }
    }
}

