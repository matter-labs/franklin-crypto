/// Initial implementation of https://eprint.iacr.org/2019/458.pdf
use bellman::pairing::ff::{Field, PrimeField, PrimeFieldRepr};
use bellman::pairing::{Engine};
use std::marker::PhantomData;
use super::group_hash::GroupHasher;

use rand::{Rand, Rng};

pub mod bn256;

pub trait SBox<E: Engine>: Sized {
    fn apply(elements: &mut [E::Fr]);
}

pub struct CubicSBox<E: Engine> {
    _marker: PhantomData<E>
}

impl<E: Engine>SBox<E> for CubicSBox<E> {

    fn apply(elements: &mut [E::Fr]) {
        for element in elements.iter_mut() {
            let mut squared = *element;
            squared.square();
            element.mul_assign(&squared);
        }
    }
}

pub struct QuanticSBox<E: Engine> {
    _marker: PhantomData<E>
}

impl<E: Engine>SBox<E> for QuanticSBox<E> {

    fn apply(elements: &mut [E::Fr]) {
        for element in elements.iter_mut() {
            let mut quad = *element;
            quad.square();
            quad.square();
            element.mul_assign(&quad);
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

    fn apply(elements: &mut [E::Fr]) {
        batch_inversion::<E>(elements);
    }
}


// TODO: Later use const functions
pub trait PoseidonHashParams<E: Engine>: Sized {
    fn t(&self) -> u32;
    fn r_f(&self) -> u32;
    fn r_p(&self) -> u32;
    fn full_round_key(&self, round: u32) -> &[E::Fr];
    fn partial_round_key(&self, round: u32) -> &[E::Fr];
    fn mds_matrix_row(&self, row: u32) -> &[E::Fr];
    fn security_level(&self) -> u32;
}

pub trait PoseidonEngine: Engine {
    type Params: PoseidonHashParams<Self>; 
    type SBox: SBox<Self>;
}

pub fn poseidon_hash<E: PoseidonEngine>(
    params: &E::Params,
    input: &[E::Fr]
) -> Vec<E::Fr> {
    let output_bits = 2*params.security_level();
    let mut output_len = (E::Fr::CAPACITY / output_bits) as usize;
    if E::Fr::CAPACITY % output_bits != 0 && E::Fr::CAPACITY < output_bits {
        output_len += 1;
    }

    let expected_input_len = params.t() as usize;
    assert!(input.len() == expected_input_len);

    let mut state = input.to_vec();
    let state_len = state.len();

    // we have to perform R_f -> R_p -> R_f

    // no optimization will be done in the first version in terms of reordering of 
    // linear transformations, round constants additions and S-Boxes

    let mut round = 0;

    let r_f = params.r_f();
    let r_p = params.r_p();

    for full_round in 0..r_f {
        let round_constants = params.full_round_key(full_round);
        for (el, c) in state.iter_mut().zip(round_constants.iter()) {
            el.add_assign(c);
        }

        E::SBox::apply(&mut state[..]);

        let mut new_state = vec![E::Fr::zero(); state_len];

        for (row, el) in new_state.iter_mut().enumerate() {
            *el = scalar_product::<E>(& state[..], params.mds_matrix_row(row as u32));
        }

        state = new_state;

        round += 1;
    }

    for partial_round in 0..r_p {
        let round_constants = params.partial_round_key(partial_round);
        for (el, c) in state.iter_mut().zip(round_constants.iter()) {
            el.add_assign(c);
        }

        E::SBox::apply(&mut state[0..1]);

        let mut new_state = vec![E::Fr::zero(); state_len];

        for (row, el) in new_state.iter_mut().enumerate() {
            *el = scalar_product::<E>(& state[..], params.mds_matrix_row(row as u32));
        }

        state = new_state;

        round += 1;
    }

    // reference implementation says that last round does not have matrix muptiplication step
    for full_round in r_f..(2*r_f - 1) {
    // for full_round in r_f..(2*r_f) {
        let round_constants = params.full_round_key(full_round);
        for (el, c) in state.iter_mut().zip(round_constants.iter()) {
            el.add_assign(c);
        }

        E::SBox::apply(&mut state[..]);

        let mut new_state = vec![E::Fr::zero(); state_len];

        for (row, el) in new_state.iter_mut().enumerate() {
            *el = scalar_product::<E>(& state[..], params.mds_matrix_row(row as u32));
        }

        state = new_state;

        round += 1;
    }

    {
        let full_round = 2*r_f - 1;
        let round_constants = params.full_round_key(full_round);
        for (el, c) in state.iter_mut().zip(round_constants.iter()) {
            el.add_assign(c);
        }

        E::SBox::apply(&mut state[..]);
    }


    state[..output_len].to_vec()
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
fn generate_mds_matrix<E: PoseidonEngine, R: Rng>(t: u32, rng: &mut R) -> Vec<E::Fr> {
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

