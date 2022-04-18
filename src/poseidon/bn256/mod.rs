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
    //use crate::*;
    use crate::poseidon::*;
    use crate::group_hash::BlakeHasher;

    #[test]
    fn test_generate_bn256_params() {
        let params = Bn256PoseidonParams::new_2_into_1::<BlakeHasher>();
    }

    #[test]
    fn test_bn256_poseidon_hash() {
        let rng = &mut thread_rng();
        let params = Bn256PoseidonParams::new_2_into_1::<BlakeHasher>();
        let input: Vec<Fr> = (0..params.rate()).map(|_| rng.gen()).collect();
        let output = poseidon_hash::<Bn256>(&params, &input[..]);
        assert_eq!(output.len(), 1);
    }

    #[test]
    fn output_bn256_poseidon_hash() {
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        let params = Bn256PoseidonParams::new_checked_2_into_1();
        for len in 1..=3 {
            let input: Vec<Fr> = (0..len).map(|_| rng.gen()).collect();
            println!("Input = {:?}", input);
            let output = poseidon_hash::<Bn256>(&params, &input[..]);
            println!("Output = {:?}", output);
        }
        /*
        Input =
        [Fr(0x27014c0bd27dddc8514b53831287e0ba02b26875bdcb34f0d4699681f487cf7b)]
        Output =
        [Fr(0x0a384dc586fd786dfd6dbb3052cdf937983fed31ede00dd95c17e2d6c3b2221e)]
        Input =
        [Fr(0x238ba289e8783d31585aa75bba8ddc2269c0c2d8c45d0769943b16f009ff5510),
        Fr(0x069fd7f225dd46f03e4e0059d187419eb51b5ab5a33368e4ac05e62353dda0c3)]
        Output =
        [Fr(0x088e9a4d8d5620405ec9970a113547a5282ec9ab8987dc560c00af19ced21318)]
        Input =
        [Fr(0x2f61d41a22e59d0c97c01e805e94254ee2931fdd577e157b3c2498479f5ae867),
        Fr(0x29d4bfd78903c5cfefe4eb802d3a0eae55b49650e59aac93bf4af56b9e71e462),
        Fr(0x0f4434eb4b70fb4bc32548e4e89d6d6fcefbeba3fd9a4fd6ff6d0afcc15ed5b3)]
        Output =
        [Fr(0x0f5fcbffb8df8f5d380ff3efbc69236c11569666af614a81c6a84538ba7595c1)]
         */
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
    /*
    MDS_MATRIX
[ [ Fr(0x05bb9226b9b9dd753cb5b4d591564d707a488ed2f9d742036b95e8f4436e174a),
Fr(0x13055a3600b9006696c372f97fc8aff2da96bb28ccf61dd24fcb60b92192de3d),
Fr(0x1adaa409f15b0fd9af93b539cefe7bce471c4f2e4df1db4f29503f27d7c452ef) ],
[ Fr(0x26d32f41d05b6a97c14aa448b15c1f46ecbb256c742547d3852a47d9a91fd950),
Fr(0x1f917d5481f29eb012f2c3d475e73588f0a50b813900e63794108bb987cb3d29),
Fr(0x235af5cba632d769b957383ad8321850c1cdecb4ba312026b5758e0422435988) ],
[ Fr(0x1bbb5d95192b03039485455554ed1eb73e7909f9db951d82cf6777d3e5a85a51),
Fr(0x026019a0051ebb21312d1f0107ede2a609d3bfe0a96da2ee89420fe70a756bf4),
Fr(0x258dfe047aede7c4f3cd7b324ab784b0a84ce4cf1a81dafa88e89138fcd45133) ] ]

     */
}