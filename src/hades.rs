/// Initial implementation of https://eprint.iacr.org/2019/458.pdf
use bellman::pairing::ff::{Field, PrimeField, PrimeFieldRepr};
use bellman::pairing::{Engine};
use std::marker::PhantomData;
use super::group_hash::GroupHasher;

use rand::{Rand, Rng};

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
    fn round_key(&self, round: u32) -> &E::Fr;
    fn mds_matrix_row(&self, row: u32) -> &[E::Fr];
    fn security_level(&self) -> u32;
}

pub trait PoseidonEngine: Engine {
    type Params: PoseidonHashParams<Self>; 
    type SBox: SBox<Self>;
}

use bellman::pairing::bn256;

impl PoseidonEngine for bn256::Bn256 {
    type Params = Bn256PoseidonParams;
    type SBox = QuanticSBox<bn256::Bn256>;
}

pub struct Bn256PoseidonParams {
    t: u32,
    r_f: u32,
    r_p: u32,
    round_keys: Vec<bn256::Fr>,
    mds_matrix: Vec<bn256::Fr>,
    security_level: u32,
}

impl Bn256PoseidonParams {
    pub fn new<H: GroupHasher>() -> Self {
        use byteorder::{WriteBytesExt, ReadBytesExt, BigEndian};
        use constants;

        let t = 6u32;
        let r_f = 8u32;
        let r_p = 84u32;

        // generate round constants based on some seed and hashing
        let round_constants = {
            let tag = b"Hadescon";
            let mut round_constants = vec![];
            let mut nonce = 0u32;
            let mut nonce_bytes = [0u8; 4];

            loop {
                (&mut nonce_bytes[0..4]).write_u32::<BigEndian>(nonce).unwrap();
                let mut h = H::new(&tag[..]);
                h.update(constants::GH_FIRST_BLOCK);
                h.update(&nonce_bytes[..]);
                let h = h.finalize();
                assert!(h.len() == 32);

                let mut constant_repr = <bn256::Fr as PrimeField>::Repr::default();
                constant_repr.read_le(&h[..]).unwrap();

                if let Ok(constant) = bn256::Fr::from_repr(constant_repr) {
                    if !constant.is_zero() {
                        round_constants.push(constant);
                    }
                }

                if round_constants.len() == ((2*r_f + r_p) as usize) {
                    break;
                }

                nonce += 1;
            }

            round_constants
        };

        let mds_matrix = {
            use rand::{SeedableRng};
            use rand::chacha::ChaChaRng;
            // Create an RNG based on the outcome of the random beacon
            let mut rng = {
                let tag = b"Hadesmds";
                let mut h = H::new(&tag[..]);
                h.update(constants::GH_FIRST_BLOCK);
                let h = h.finalize();
                assert!(h.len() == 32);
                let mut seed = [0u32; 8];
                for i in 0..8 {
                    seed[i] = (&h[..]).read_u32::<BigEndian>().expect("digest is large enough for this to work");
                }

                ChaChaRng::from_seed(&seed)
            };

            generate_mds_matrix::<bn256::Bn256, _>(t, &mut rng)
        };

        Self {
            t: t,
            r_f: r_f,
            r_p: r_f,
            round_keys: round_constants,
            mds_matrix: mds_matrix,
            security_level: 126
        }
    }
}

impl PoseidonHashParams<bn256::Bn256> for Bn256PoseidonParams {
    fn t(&self) -> u32 {
        self.t
    }
    fn r_f(&self) -> u32 {
        self.r_f
    }
    fn r_p(&self) -> u32 {
        self.r_p
    }
    fn round_key(&self, round: u32) -> &bn256::Fr {
        &self.round_keys[round as usize]
    }
    fn mds_matrix_row(&self, row: u32) -> &[bn256::Fr] {
        let t = self.t;
        let start = (t*row) as usize;
        let end = (t*(row+1)) as usize;

        &self.mds_matrix[start..end]
    }
    fn security_level(&self) -> u32 {
        self.security_level
    }
}

pub fn poseidon_hash<E: PoseidonEngine>(
    params: &E::Params,
    input: &[E::Fr]
) -> Vec<E::Fr> {
    let output_bits = 2*params.security_level();
    let mut output_len = E::Fr::CAPACITY / output_bits;
    if E::Fr::CAPACITY % output_bits != 0 {
        output_len += 1;
    }

    let expected_input_len = input.len() - (output_len as usize);
    assert!(input.len() == expected_input_len);

    let mut output = input.to_vec();
    let output_len = output.len();

    // we have to perform R_f -> R_p -> R_f

    // no optimization will be done in the first version in terms of reordering of 
    // linear transformations, round constants additions and S-Boxes

    let mut round = 0;

    for _ in 0..(params.r_f() as usize) {
        let round_constant = params.round_key(round);
        for el in output.iter_mut() {
            el.add_assign(round_constant);
        }

        let mut new_output = vec![E::Fr::zero(); output_len];

        for (row, el) in new_output.iter_mut().enumerate() {
            *el = scalar_product::<E>(& output[..], params.mds_matrix_row(row as u32));
        }

        output = new_output;

        E::SBox::apply(&mut output[..]);

        round += 1;
    }

    for _ in 0..(params.r_p() as usize) {
        let round_constant = params.round_key(round);
        for el in output.iter_mut() {
            el.add_assign(round_constant);
        }

        let mut new_output = vec![E::Fr::zero(); output_len];

        for (row, el) in new_output.iter_mut().enumerate() {
            *el = scalar_product::<E>(& output[..], params.mds_matrix_row(row as u32));
        }

        output = new_output;

        E::SBox::apply(&mut output[0..1]);

        round += 1;
    }

    for _ in 0..(params.r_f() as usize) {
        let round_constant = params.round_key(round);
        for el in output.iter_mut() {
            el.add_assign(round_constant);
        }

        let mut new_output = vec![E::Fr::zero(); output_len];

        for (row, el) in new_output.iter_mut().enumerate() {
            *el = scalar_product::<E>(& output[..], params.mds_matrix_row(row as u32));
        }

        output = new_output;

        E::SBox::apply(&mut output[..]);

        round += 1;
    }


    output
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

#[cfg(test)]
mod test {
    use rand::{Rand, Rng, thread_rng};
    use bellman::pairing::bn256::{Bn256, Fr};
    use super::Bn256PoseidonParams;
    use super::super::group_hash::BlakeHasher;

    #[test]
    fn test_generate_bn256_poseidon_params() {
        let params = Bn256PoseidonParams::new::<BlakeHasher>();
    }
}