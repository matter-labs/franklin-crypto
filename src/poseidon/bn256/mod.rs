use bellman::pairing::bn256;
use bellman::pairing::ff::{Field, PrimeField, PrimeFieldRepr};
use super::{PoseidonEngine, PoseidonHashParams, PoseidonParamsInternal,
            QuinticSBox, generate_mds_matrix};
use group_hash::{GroupHasher, BlakeHasher};

impl PoseidonEngine for bn256::Bn256 {
    type Params = Bn256PoseidonParams;
}

#[derive(Clone, Debug)]
pub struct Bn256PoseidonParams {
    pub(crate) c: u32,
    pub(crate) r: u32,
    pub(crate) full_rounds: u32,
    pub(crate) partial_rounds: u32,
    pub(crate) round_constants: Vec<bn256::Fr>,
    pub(crate) mds_matrix: Vec<bn256::Fr>,
    pub(crate) security_level: u32,
    pub(crate) sbox: QuinticSBox<bn256::Bn256>,
    custom_gates_allowed: bool,
}

impl Bn256PoseidonParams {
    pub fn new_checked_2_into_1() -> Self {
        let c = 1u32;
        let r = 2u32;
        let partial_rounds = 83u32;
        let full_rounds = 8u32;
        let security_level = 126u32;

        Self::new_for_params::<BlakeHasher>(c, r, partial_rounds, full_rounds, security_level)
    }

    pub fn new_2_into_1<H: GroupHasher>() -> Self {
        let c = 1u32;
        let r = 2u32;
        let partial_rounds = 83u32;
        let full_rounds = 8u32;
        let security_level = 126u32;

        Self::new_for_params::<H>(c, r, partial_rounds, full_rounds, security_level)
    }

    pub fn new_3_into_1<H: GroupHasher>() -> Self {
        let c = 1u32;
        let r = 3u32;
        let partial_rounds = 83u32;
        let full_rounds = 8u32;
        let security_level = 126u32;

        Self::new_for_params::<H>(c, r, partial_rounds, full_rounds, security_level)
    }

    pub fn new_for_params<H: GroupHasher>(c: u32, r: u32, partial_rounds: u32, full_rounds: u32, _security_level: u32) -> Self {
        use byteorder::{WriteBytesExt, ReadBytesExt, BigEndian};
        use constants;

        let state_width = c + r;
        let num_round_constants = (full_rounds + partial_rounds) * state_width;
        let num_round_constants = num_round_constants as usize;

        // generate round constants based on some seed and hashing
        let round_constants = {
            let tag = b"Rescue_f";
            let mut round_constants = Vec::with_capacity(num_round_constants);
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

                if round_constants.len() == num_round_constants {
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
                // This tag is a first one in a sequence of b"ResMxxxx"
                // that produces MDS matrix without eigenvalues for rate = 2,
                // capacity = 1 variant over Bn254 curve
                let tag = b"ResM0003";
                let mut h = H::new(&tag[..]);
                h.update(constants::GH_FIRST_BLOCK);
                let h = h.finalize();
                assert!(h.len() == 32);
                let mut seed = [0u32; 8];
                for (i, chunk) in h.chunks_exact(4).enumerate() {
                    seed[i] = (&chunk[..]).read_u32::<BigEndian>().expect("digest is large enough for this to work");
                }

                ChaChaRng::from_seed(&seed)
            };

            generate_mds_matrix::<bn256::Bn256, _>(state_width, &mut rng)
        };

        Self {
            c: c,
            r: r,
            full_rounds,
            partial_rounds,
            round_constants: round_constants,
            mds_matrix: mds_matrix,
            security_level: 126,
            sbox: QuinticSBox { _marker: std::marker::PhantomData },
            custom_gates_allowed: false,
        }
    }

    pub fn set_allow_custom_gate(&mut self, allowed: bool) {
        self.custom_gates_allowed = allowed;
    }
}

impl PoseidonParamsInternal<bn256::Bn256> for Bn256PoseidonParams {
    fn set_round_constants(&mut self, to: Vec<bn256::Fr>) {
        assert_eq!(self.round_constants.len(), to.len());
        self.round_constants = to;
    }
}

impl PoseidonHashParams<bn256::Bn256> for Bn256PoseidonParams {
    type SBox = QuinticSBox<bn256::Bn256>;

    fn capacity(&self) -> u32 {
        self.c
    }
    fn rate(&self) -> u32 {
        self.r
    }
    fn num_full_rounds(&self) -> u32 {
        self.full_rounds
    }
    fn num_partial_rounds(&self) -> u32 {
        self.partial_rounds
    }
    fn round_constants(&self, round: u32) -> &[bn256::Fr] {
        let t = self.c + self.r;
        let start = (t*round) as usize;
        let end = (t*(round+1)) as usize;

        &self.round_constants[start..end]
    }
    fn mds_matrix_row(&self, row: u32) -> &[bn256::Fr] {
        let t = self.c + self.r;
        let start = (t*row) as usize;
        let end = (t*(row+1)) as usize;

        &self.mds_matrix[start..end]
    }
    fn security_level(&self) -> u32 {
        self.security_level
    }
    fn output_len(&self) -> u32 {
        self.capacity()
    }
    fn absorbtion_cycle_len(&self) -> u32 {
        self.rate()
    }
    fn compression_rate(&self) -> u32 {
        self.absorbtion_cycle_len() / self.output_len()
    }

    fn sbox(&self) -> &Self::SBox {
        &self.sbox
    }
    fn can_use_custom_gates(&self) -> bool {
        self.custom_gates_allowed
    }
}


#[cfg(test)]
mod test {
    use rand::{Rand, Rng, thread_rng, XorShiftRng, SeedableRng};
    use bellman::pairing::bn256::{Bn256, Fr};
    use bellman::pairing::ff::PrimeField;
    use bellman::pairing::ff::Field;
    use super::*;
    use crate::*;
    use crate::poseidon::*;
    use crate::group_hash::BlakeHasher;

    #[test]
    fn test_generate_bn256_params() {
        let params = Bn256PoseidonParams::new_2_into_1::<BlakeHasher>();
    }

    #[test]
    fn test_bn256_stateful_hash() {
        let rng = &mut thread_rng();
        let params = Bn256PoseidonParams::new_2_into_1::<BlakeHasher>();
        let input: Vec<Fr> = (0..params.rate()).map(|_| rng.gen()).collect();

        let mut stateful_rescue = super::super::StatefulPoseidon::<Bn256>::new(&params);
        stateful_rescue.specialize(input.len() as u8);
        stateful_rescue.absorb(&input);

        let _ = stateful_rescue.squeeze_out_single();
    }

    #[test]
    fn print_mds() {
        let params = Bn256PoseidonParams::new_2_into_1::<BlakeHasher>();
        println!("MDS_MATRIX");
        let mut vec = vec![];
        for i in 0..params.state_width() {
            vec.push(format!("{:?}", params.mds_matrix_row(i)));
        }

        println!("[ {} ]", vec.join(","));
    }
}