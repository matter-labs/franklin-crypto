use bellman::pairing::ff::{Field, PrimeField, PrimeFieldRepr};
use bellman::pairing::{Engine};
use std::marker::PhantomData;
use super::group_hash::GroupHasher;

use rand::{Rand, Rng};

pub mod bn256_2_into_1;

pub trait SBox<E: Engine>: Sized {
    fn apply(&self, elements: &mut [E::Fr]);
}

pub struct CubicSBox<E: Engine> {
    _marker: PhantomData<E>
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

pub struct QuinticSBox<E: Engine> {
    _marker: PhantomData<E>
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

pub struct PowerSBox<E: Engine> {
    power: <E::Fr as PrimeField>::Repr,
}

impl<E: Engine>SBox<E> for PowerSBox<E> {
    fn apply(&self, elements: &mut [E::Fr]) {
        for element in elements.iter_mut() {
            *element = element.pow(&self.power);
        }
    }
}

pub struct InversionSBox<E: Engine> {
    _marker: PhantomData<E>
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

pub trait RescueHashParams<E: Engine>: Sized {
    type SBox0: SBox<E>;
    type SBox1: SBox<E>;
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

pub trait RescueEngine: Engine {
    type Params: RescueHashParams<Self>; 
}

pub fn rescue_hash<E: RescueEngine>(
    params: &E::Params,
    input: &[E::Fr]
) -> Vec<E::Fr> {
    sponge::<E>(params, input)
}

fn sponge<E: RescueEngine>(
    params: &E::Params,
    input: &[E::Fr]
) -> Vec<E::Fr> {
    let mut state = vec![E::Fr::zero(); params.state_width() as usize];
    let rate = params.rate() as usize;
    let padding_len = rate - (input.len() % rate);
    let padding = vec![E::Fr::one(); padding_len];

    let mut it = input.iter().chain(&padding);
    let absorbtion_cycles = (input.len() + padding_len) / rate;
    for _ in 0..absorbtion_cycles {
        for i in 0..rate {
            state[i].add_assign(&it.next().unwrap());
        }
        state = rescue_mimc::<E>(params, &state);
    }

    state[..(params.capacity() as usize)].to_vec()
}   


fn rescue_mimc<E: RescueEngine>(
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
            *place_into = scalar_product::<E>(& state[..], params.mds_matrix_row(row as u32));
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