use std::convert::TryInto;

use byteorder::{BigEndian, ReadBytesExt, WriteBytesExt};
use bellman::pairing::ff::{Field, PrimeField, PrimeFieldRepr};
use bellman::pairing::Engine;
use constants;
use group_hash::{BlakeHasher, GroupHasher};
use rand::{chacha::ChaChaRng, Rng, SeedableRng};

use super::super::common::utils::construct_mds_matrix;

#[derive(Debug, Clone)]
pub struct InnerHashParameters<E: Engine, const RATE: usize, const WIDTH: usize> {
    pub security_level: usize,
    pub full_rounds: usize,
    pub partial_rounds: usize,
    pub round_constants: Vec<[E::Fr; WIDTH]>,
    pub mds_matrix: [[E::Fr; WIDTH]; WIDTH],
}


type H = BlakeHasher;

impl<E: Engine, const RATE: usize, const WIDTH: usize> InnerHashParameters<E, RATE, WIDTH> {
    pub fn new(security_level: usize, full_rounds: usize, partial_rounds: usize) -> Self {
        assert_ne!(RATE, 0);
        assert_ne!(WIDTH, 0);
        assert_ne!(full_rounds, 0);

        Self {
            security_level,
            full_rounds,
            partial_rounds,
            round_constants: vec![[E::Fr::zero(); WIDTH]],
            mds_matrix: [[E::Fr::zero(); WIDTH]; WIDTH],
        }
    }

    pub fn constants_of_round(&self, round: usize) -> [E::Fr; WIDTH] {
        self.round_constants[round]
    }

    pub fn round_constants(&self) -> &[[E::Fr; WIDTH]] {
        &self.round_constants
    }
    pub fn mds_matrix(&self) -> &[[E::Fr; WIDTH]; WIDTH] {
        &self.mds_matrix
    }

    pub(crate) fn compute_round_constants(&mut self, number_of_rounds: usize, tag: &[u8]) {
        let total_round_constants = WIDTH * number_of_rounds; 

        let mut round_constants = Vec::with_capacity(total_round_constants);
        let mut nonce = 0u32;
        let mut nonce_bytes = [0u8; 4];

        loop {
            (&mut nonce_bytes[0..4])
                .write_u32::<BigEndian>(nonce)
                .unwrap();
            let mut h = H::new(&tag[..]);
            h.update(constants::GH_FIRST_BLOCK);
            h.update(&nonce_bytes[..]);
            let h = h.finalize();
            assert!(h.len() == 32);

            let mut constant_repr = <E::Fr as PrimeField>::Repr::default();
            constant_repr.read_le(&h[..]).unwrap();

            if let Ok(constant) = E::Fr::from_repr(constant_repr) {
                if !constant.is_zero() {
                    round_constants.push(constant);
                }
            }

            if round_constants.len() == total_round_constants {
                break;
            }

            nonce += 1;
        }
        self.round_constants = vec![[E::Fr::zero(); WIDTH]; number_of_rounds];
        round_constants
            .chunks_exact(WIDTH)
            .zip(self.round_constants.iter_mut())
            .for_each(|(values, constants)| {
                *constants = values.try_into().expect("round constants in const")
            });
    }

    pub(crate) fn compute_round_constants_with_prefixed_blake2s(&mut self, number_of_rounds: usize, tag: &[u8]) {
        let total_round_constants = WIDTH * number_of_rounds; 
        let round_constants = get_random_field_elements_from_seed::<E>(total_round_constants, tag);

        self.round_constants = vec![[E::Fr::zero(); WIDTH]; number_of_rounds];
        round_constants
            .chunks_exact(WIDTH)
            .zip(self.round_constants.iter_mut())
            .for_each(|(values, constants)| {
                *constants = values.try_into().expect("round constants in const")
            });
    }

    pub(crate) fn compute_mds_matrix_for_poseidon(&mut self) {
        let rng = &mut init_rng_for_poseidon();
        self.compute_mds_matrix(rng)
    }

    pub(crate) fn compute_mds_matrix_for_rescue(&mut self) {
        let rng = &mut init_rng_for_rescue();
        self.compute_mds_matrix(rng)
    }

    pub(crate) fn set_circular_optimized_mds(&mut self) {
        assert_eq!(WIDTH, 3, "Circuilar (2, 1, 1) matrix is MDS only for state width = 3");
        let one = E::Fr::one();
        let mut two = one;
        two.double();
        let tmp = [
            [two, one, one],
            [one, two, one],
            [one, one, two]
        ];

        for (dst_row, src_row) in self.mds_matrix.iter_mut().zip(tmp.iter()) {
            for (dst, src) in dst_row.iter_mut().zip(src_row.iter()) {
                *dst = *src;
            }
        }
    }

    fn compute_mds_matrix<R: Rng>(&mut self, rng: &mut R) {
        self.mds_matrix = construct_mds_matrix::<E, _, WIDTH>(rng);
    }
}

fn init_rng_for_rescue() -> ChaChaRng {
    let tag = b"ResM0003";
    let mut h = H::new(&tag[..]);
    h.update(constants::GH_FIRST_BLOCK);
    let h = h.finalize();
    assert!(h.len() == 32);
    let mut seed = [0u32; 8];
    for i in 0..8 {
        seed[i] = (&h[..])
            .read_u32::<BigEndian>()
            .expect("digest is large enough for this to work");
    }

    ChaChaRng::from_seed(&seed)
}

fn init_rng_for_poseidon() -> ChaChaRng {
    let tag = b"ResM0003"; // TODO: change tag?
    let mut h = H::new(&tag[..]);
    h.update(constants::GH_FIRST_BLOCK);
    let h = h.finalize();
    assert!(h.len() == 32);
    let mut seed = [0u32; 8];

    for (i, chunk) in h.chunks_exact(4).enumerate() {
        seed[i] = (&chunk[..])
            .read_u32::<BigEndian>()
            .expect("digest is large enough for this to work");
    }

    ChaChaRng::from_seed(&seed)
}


pub(crate) fn get_random_field_elements_from_seed<E: Engine>(num_elements: usize, tag: &[u8]) -> Vec<E::Fr> {
    let mut round_constants = Vec::with_capacity(num_elements);
    let mut nonce = 0u32;
    let mut nonce_bytes = [0u8; 4];

    assert!((E::Fr::NUM_BITS + 7) / 8 <= 32);

    loop {
        (&mut nonce_bytes[0..4])
            .write_u32::<BigEndian>(nonce)
            .unwrap();
        use blake2::Digest;
        let mut h = blake2::Blake2b::new();
        h.update(tag);
        h.update(constants::GH_FIRST_BLOCK);
        h.update(&nonce_bytes[..]);
        let h = h.finalize();
        assert!(h.len() == 32);

        let mut constant_repr = <E::Fr as PrimeField>::Repr::default();
        constant_repr.read_le(&h[..]).unwrap();

        if let Ok(constant) = E::Fr::from_repr(constant_repr) {
            if !constant.is_zero() {
                round_constants.push(constant);
            }
        }

        if round_constants.len() == num_elements {
            break;
        }

        nonce += 1;
    }

    round_constants
}