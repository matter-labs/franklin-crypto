use bellman::pairing::bn256;
use super::*;

extern crate num_bigint;
extern crate num_integer;
extern crate num_traits;
use self::num_bigint::{BigUint, BigInt};
use self::num_integer::{Integer, ExtendedGcd};
use self::num_traits::{ToPrimitive, Zero, One};

impl RescueEngine for bn256::Bn256 {
    type Params = Bn256RescueParams2Into1;
}

#[derive(Clone)]
pub struct Bn256RescueParams2Into1 {
    c: u32,
    r: u32,
    rounds: u32,
    round_constants: Vec<bn256::Fr>,
    mds_matrix: Vec<bn256::Fr>,
    security_level: u32,
    sbox_0: QuinticSBox<bn256::Bn256>,
    sbox_1: PowerSBox<bn256::Bn256>,
}

impl Bn256RescueParams2Into1 {
    pub fn new<H: GroupHasher>() -> Self {
        let c = 1u32;
        let r = 2u32;
        let rounds = 22u32;
        let security_level = 126u32;

        Self::new_for_params::<H>(c, r, rounds, security_level)
    }

    pub fn new_for_params<H: GroupHasher>(c: u32, r: u32, rounds: u32, security_level: u32) -> Self {
        use byteorder::{WriteBytesExt, ReadBytesExt, BigEndian};
        use constants;

        let state_width = c + r;
        let num_round_constants = (1 + rounds * 2) * state_width;
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
                let tag = b"Rescue_m";
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

            generate_mds_matrix::<bn256::Bn256, _>(state_width, &mut rng)
        };


        let alpha = BigUint::from(5u64);

        let mut p_minus_one_biguint = BigUint::from(0u64);
        for limb in bn256::Fr::char().as_ref().iter().rev() {
            p_minus_one_biguint <<= 64;
            p_minus_one_biguint += BigUint::from(*limb);
        }

        p_minus_one_biguint -= BigUint::one();

        fn biguint_to_u64_array(mut v: BigUint) -> [u64; 4] {
            let m = BigUint::from(1u64) << 64;
            let mut ret = [0; 4];

            for idx in 0..4 {
                ret[idx] = (&v % &m).to_u64().expect("is guaranteed to fit");
                v >>= 64;
            }
            assert!(v.is_zero());
            ret
        }

        let alpha_signed = BigInt::from(alpha);
        let p_minus_one_signed = BigInt::from(p_minus_one_biguint);

        let ExtendedGcd{ gcd, x: _, y, .. } = p_minus_one_signed.extended_gcd(&alpha_signed); 
        assert!(gcd.is_one());
        let y = if y < BigInt::zero() {
            let mut y = y;
            y += p_minus_one_signed;

            y.to_biguint().expect("must be > 0")
        } else {
            y.to_biguint().expect("must be > 0")
        };

        println!("Y = {}", y.clone().to_str_radix(16));

        let inv_alpha = biguint_to_u64_array(y);

        let mut alpha_inv_repr = <bn256::Fr as PrimeField>::Repr::default();
        for (r, limb) in alpha_inv_repr.as_mut().iter_mut().zip(inv_alpha.iter()) {
            *r = *limb;
        }

        Self {
            c: c,
            r: r,
            rounds: rounds,
            round_constants: round_constants,
            mds_matrix: mds_matrix,
            security_level: 126,
            sbox_0: QuinticSBox { _marker: std::marker::PhantomData },
            sbox_1: PowerSBox { power: alpha_inv_repr, inv: 5u64 }
        }
    }
}

impl RescueHashParams<bn256::Bn256> for Bn256RescueParams2Into1 {
    type SBox0 = QuinticSBox<bn256::Bn256>;
    type SBox1 = PowerSBox<bn256::Bn256>;

    fn capacity(&self) -> u32 {
        self.c
    }
    fn rate(&self) -> u32 {
        self.r
    }
    fn num_rounds(&self) -> u32 {
        self.rounds
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

    fn sbox_0(&self) -> &Self::SBox0 {
        &self.sbox_0
    }
    fn sbox_1(&self) -> &Self::SBox1 {
        &self.sbox_1
    }
}


#[cfg(test)]
mod test {
    use rand::{Rand, Rng, thread_rng};
    use bellman::pairing::bn256::{Bn256, Fr};
    use bellman::pairing::ff::PrimeField;
    use bellman::pairing::ff::Field;
    use super::Bn256RescueParams2Into1;
    use crate::rescue::*;
    use crate::group_hash::BlakeHasher;

    #[test]
    fn test_generate_bn256_rescue_params() {
        let params = Bn256RescueParams2Into1::new::<BlakeHasher>();
    }

    #[test]
    fn test_bn256_rescue_params_permutation() {
        let rng = &mut thread_rng();
        let params = Bn256RescueParams2Into1::new::<BlakeHasher>();

        for _ in 0..1000 {
            let input: Fr = rng.gen();
            let mut input_arr: [Fr; 1] = [input];
            params.sbox_1().apply(&mut input_arr);
            params.sbox_0().apply(&mut input_arr);
            assert_eq!(input_arr[0], input);
        }

        for _ in 0..1000 {
            let input: Fr = rng.gen();
            let mut input_arr: [Fr; 1] = [input];
            params.sbox_0().apply(&mut input_arr);
            params.sbox_1().apply(&mut input_arr);
            assert_eq!(input_arr[0], input);
        }
    }

    #[test]
    fn test_bn256_rescue_hash() {
        let rng = &mut thread_rng();
        let params = Bn256RescueParams2Into1::new::<BlakeHasher>();
        let input: Vec<Fr> = (0..params.rate()).map(|_| rng.gen()).collect();
        let output = rescue_hash::<Bn256>(&params, &input[..]);
        assert!(output.len() == 1);
    }
}