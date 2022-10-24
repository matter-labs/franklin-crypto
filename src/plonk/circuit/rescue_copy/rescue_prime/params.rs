use super::super::common::params::InnerHashParameters;
use crate::bellman::pairing::ff::{PrimeFieldRepr, ScalarEngine};
use crate::bellman::pairing::{
    Engine,
};
extern crate num_bigint;
extern crate num_integer;
extern crate num_traits;
use super::super::common::utils::biguint_to_u64_vec;
use super::super::traits::{CustomGate, HashFamily, HashParams, Sbox};
use bellman::pairing::bn256::Bn256;
use crate::bellman::pairing::ff::{
    Field,
    PrimeField,
    BitIterator
};
use num_bigint::{BigInt, BigUint, Sign};
use num_integer::{ExtendedGcd, Integer};
use num_traits::{One, ToPrimitive, Zero};
use std::convert::TryInto;
use std::ops::{Mul, Sub};
use plonk::circuit::rescue_copy::{serialize_vec_of_arrays, deserialize_vec_of_arrays, serialize_array_of_arrays, deserialize_array_of_arrays};

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct RescuePrimeParams<E: Engine, const RATE: usize, const WIDTH: usize> {
    pub(crate) allows_specialization: bool,
    pub(crate) full_rounds: usize,
    #[serde(serialize_with = "serialize_vec_of_arrays")]
    #[serde(deserialize_with = "deserialize_vec_of_arrays")]
    pub(crate) round_constants: Vec<[E::Fr; WIDTH]>,
    #[serde(serialize_with = "serialize_array_of_arrays")]
    #[serde(deserialize_with = "deserialize_array_of_arrays")]
    pub(crate) mds_matrix: [[E::Fr; WIDTH]; WIDTH],
    pub(crate) alpha: Sbox,
    pub(crate) alpha_inv: Sbox,
    pub(crate) custom_gate: CustomGate,
}
impl<E: Engine, const RATE: usize, const WIDTH: usize> PartialEq
    for RescuePrimeParams<E, RATE, WIDTH>
{
    fn eq(&self, other: &Self) -> bool {
        self.hash_family() == other.hash_family()
    }
}

impl<E: Engine, const RATE: usize, const WIDTH: usize> Default
    for RescuePrimeParams<E, RATE, WIDTH>
{
    fn default() -> Self {
        let (params, alpha, alpha_inv) = super::params::rescue_prime_params::<E, RATE, WIDTH>();
        Self {
            allows_specialization: false,
            full_rounds: params.full_rounds,
            round_constants: params.round_constants().try_into().expect("constant array"),
            mds_matrix: *params.mds_matrix(),
            alpha: Sbox::Alpha(alpha),
            alpha_inv: Sbox::AlphaInverse(alpha_inv, alpha),
            custom_gate: CustomGate::None,
        }
    }
}
impl<E: Engine, const RATE: usize, const WIDTH: usize> RescuePrimeParams<E, RATE, WIDTH> {
    pub fn new_with_width3_custom_gate() -> Self {
        Self::new_with_custom_gate(CustomGate::QuinticWidth3)
    }
    pub fn new_with_width4_custom_gate() -> Self {
        Self::new_with_custom_gate(CustomGate::QuinticWidth4)
    }
    fn new_with_custom_gate(custom_gate: CustomGate) -> Self {
        let (params, alpha, alpha_inv) = super::params::rescue_prime_params::<E, RATE, WIDTH>();
        Self {
            allows_specialization: false,
            full_rounds: params.full_rounds,
            round_constants: params.round_constants().try_into().expect("constant array"),
            mds_matrix: *params.mds_matrix(),
            alpha: Sbox::Alpha(alpha),
            alpha_inv: Sbox::AlphaInverse(alpha_inv, alpha),
            custom_gate,
        }
    }
}

impl<E: Engine, const RATE: usize, const WIDTH: usize> HashParams<E, RATE, WIDTH>
    for RescuePrimeParams<E, RATE, WIDTH>
{
    #[inline]
    fn allows_specialization(&self) -> bool {
        self.allows_specialization
    }
    fn hash_family(&self) -> HashFamily {
        HashFamily::RescuePrime
    }

    fn constants_of_round(&self, round: usize) -> &[E::Fr; WIDTH] {
        &self.round_constants[round]
    }

    fn mds_matrix(&self) -> &[[E::Fr; WIDTH]; WIDTH] {
        &self.mds_matrix
    }

    fn number_of_full_rounds(&self) -> usize {
        self.full_rounds
    }

    fn number_of_partial_rounds(&self) -> usize {
        unimplemented!("RescuePrime doesn't have partial rounds.")
    }

    fn alpha(&self) -> &Sbox {
        &self.alpha
    }

    fn alpha_inv(&self) -> &Sbox {
        &self.alpha_inv
    }

    fn optimized_mds_matrixes(&self) -> (&[[E::Fr; WIDTH]; WIDTH], &[[[E::Fr; WIDTH]; WIDTH]]) {
        unimplemented!("RescuePrime doesn't use optimized mds matrixes")
    }

    fn optimized_round_constants(&self) -> &[[E::Fr; WIDTH]] {
        unimplemented!("RescuePrime doesn't use optimized round constants")
    }

    fn custom_gate(&self) -> CustomGate {
        self.custom_gate
    }

    fn use_custom_gate(&mut self, gate: CustomGate) {
        self.custom_gate = gate;
    }
}

fn get_number_of_rounds(m: usize, r: usize, security_level: usize, alpha: usize) -> usize {
    let capacity = m - r;
    fn factorial(n: &BigUint) -> BigUint {
        if n.is_zero() {
            return BigUint::one();
        } else {
            return n * factorial(&(n - &BigUint::one()));
        }
    }

    fn binomial(n: &BigUint, k: &BigUint) -> BigUint {
        factorial(n) / (factorial(&(n - k)) * factorial(k))
    }

    let rate = m - capacity;
    let dcon = |n: usize| -> BigUint {
        let tmp = ((alpha - 1) * m * (n - 1)) as f64;
        let result = BigUint::from((0.5 * tmp).floor() as u64) + BigUint::from(2u8);
        BigUint::from(result)
    };

    let v = |n| -> BigUint {
        let result = m * (n - 1) + rate;
        BigUint::from(result)
    };

    let target = BigUint::from(2u128.pow(security_level as u32));

    let mut actual_l1 = 0;
    for l1 in 1..25 {
        if (binomial(&(v(l1) + dcon(l1)), &v(l1)).pow(2u32)) > target {
            actual_l1 = l1;
            break;
        }
    }
    assert!(actual_l1 > 0, "l1 must be greater than zero");

    (1.5 * actual_l1.max(5) as f64).ceil() as usize
}

fn compute_alpha(p: &[u8]) -> (BigUint, BigUint) {
    let p_big = BigInt::from_bytes_le(Sign::Plus, p);
    let p_minus_one = p_big.sub(BigInt::from(1));
    let mut actual_alpha = BigInt::from(0);
    for alpha in num_iter::range_inclusive(BigInt::from(3), p_minus_one.to_owned()) {
        if p_minus_one.gcd(&alpha).is_one() {
            actual_alpha = alpha;
            break;
        }
    }
    let ExtendedGcd {
        gcd,
        y: mut alpha_inv,
        ..
    } = p_minus_one.extended_gcd(&actual_alpha);
    assert!(gcd.is_one());
    if alpha_inv < BigInt::zero() {
        alpha_inv += p_minus_one;
    };

    (
        actual_alpha.to_biguint().unwrap(),
        alpha_inv.to_biguint().unwrap(),
    )
}

fn compute_round_constants<E: Engine, const RATE: usize, const WIDTH: usize>(
    modulus_bytes: &[u8],
    p_big: BigInt,
    security_level: usize,
    n: usize,
) -> Vec<[E::Fr; WIDTH]> {
    fn shake256(input: &[u8], num_bytes: usize) -> Box<[u8]> {
        use sha3::digest::ExtendableOutput;
        use sha3::digest::Update;
        use sha3::Shake256;

        let mut shake = Shake256::default();
        shake.update(input);
        shake.finalize_boxed(num_bytes)
    }

    let m = WIDTH;
    let capacity = WIDTH - RATE;

    let modulus_bit_len = (modulus_bytes.len() * 8 - 2) as f32;

    let bytes_per_int = ((modulus_bit_len / 8f32) + 1f32).ceil() as usize;
    let num_bytes = bytes_per_int * 2 * m * n;
    let seed_string = format!(
        "Rescue-XLIX({},{},{},{})",
        p_big, m, capacity, security_level
    );
    let seed_bytes = seed_string.as_bytes();
    let byte_string = shake256(seed_bytes, num_bytes);
    let mut round_constants = vec![];
    for i in 0..2 * m * n {
        let chunk = byte_string[bytes_per_int * i..bytes_per_int * (i + 1)].to_vec();
        let constant = chunk
            .iter()
            .enumerate()
            .map(|(i, j)| {
                // (256^j) * ZZ(chunk[j])
                let pow = BigUint::from(256u16).pow(i as u32);
                let zz = BigUint::from_bytes_le(&[*j]);
                let result = pow.clone().mul(zz.clone());

                result
            })
            .fold(BigUint::zero(), |acc, next| acc + next);
        let remainder = constant.mod_floor(&p_big.to_biguint().expect("valid modulus"));
        let mut bytes_le = remainder.to_bytes_le();
        if bytes_le.len() < 64 {
            bytes_le.resize(64, 0u8);
        }

        let mut repr = <E::Fr as PrimeField>::Repr::default();
        repr.read_le(&bytes_le[..]).unwrap();
        let constant_fe = E::Fr::from_repr(repr).unwrap();
        round_constants.push(constant_fe);
    }
    let mut final_constants = vec![[E::Fr::zero(); WIDTH]; n];

    round_constants
        .chunks_exact(WIDTH)
        .zip(final_constants.iter_mut())
        .for_each(|(src, dst)| *dst = src.try_into().expect("constants in const"));

    final_constants
}

pub fn rescue_prime_params<E: Engine, const RATE: usize, const WIDTH: usize>(
) -> (InnerHashParameters<E, RATE, WIDTH>, u64, Vec<u64>) {
    let security_level = 80;

    let mut modulus_bytes = vec![];
    let p_fe = <Bn256 as ScalarEngine>::Fr::char();
    p_fe.write_le(&mut modulus_bytes).unwrap();
    let p_big = BigInt::from_bytes_le(Sign::Plus, &modulus_bytes);
    let (alpha, alpha_inv) = compute_alpha(&modulus_bytes);
    let alpha = alpha.to_u64().expect("u64");
    let number_of_rounds =
        get_number_of_rounds(WIDTH, WIDTH - RATE, security_level, alpha as usize);

    let mut params = InnerHashParameters::new(security_level, number_of_rounds, 0);
    params.round_constants = compute_round_constants::<E, RATE, WIDTH>(
        &modulus_bytes,
        p_big,
        security_level,
        number_of_rounds,
    );

    params.compute_mds_matrix_for_rescue();

    let alpha_inv = biguint_to_u64_vec(alpha_inv);

    (params, alpha, alpha_inv)
}

#[cfg(test)]
mod tests {
    use super::*;
    use bellman::pairing::bn256::{Bn256, Fr};
    use bellman::{PrimeField, ScalarEngine};
    use num_bigint::{BigInt, Sign};
    #[test]
    fn test_rescue_prime_calculate_number_of_rounds() {
        let p_fe = <Bn256 as ScalarEngine>::Fr::char();
        let m = 3;
        let capacity = 1;
        let security_level = 80;
        let mut modulus_bytes = vec![];
        p_fe.write_le(&mut modulus_bytes).unwrap();
        let p_big = BigInt::from_bytes_le(Sign::Plus, &modulus_bytes);
        let (alpha, alpha_inv) = compute_alpha(&modulus_bytes);
        let alpha = alpha.to_u32_digits()[0] as usize;
        let n = get_number_of_rounds(m, capacity, security_level, alpha);

        println!(
            "alpha {} alpha inv {:x} number of rounds {}",
            alpha, alpha_inv, n
        );

        let round_constants =
            compute_round_constants::<Bn256, 2, 3>(&modulus_bytes, p_big, security_level, n);

        println!("number of rounds {}", n);
        println!("number of round constants {}", round_constants.len());

        let expected_in_str = expected_round_constants::<Fr>();

        let field_capacity = 64;
        assert_eq!(field_capacity, 64);

        let expected_constants: Vec<Fr> = expected_in_str
            .iter()
            .map(|constant_str| {
                let constant_str = String::from(*constant_str);

                let constant_str = if constant_str.len() < field_capacity {
                    let num_prepended = field_capacity - constant_str.len();
                    let mut prepended = String::new();
                    for _ in 0..num_prepended {
                        prepended.push_str("0");
                    }

                    [prepended, constant_str].concat()
                } else {
                    constant_str
                };
                let decoded = hex::decode(constant_str).expect("decoded array");

                let mut repr = <Fr as PrimeField>::Repr::default();
                repr.read_be(&decoded[..]).expect("consume all bytes");
                let el = Fr::from_repr(repr).expect("a field element");
                el
            })
            .collect();

        round_constants
            .iter()
            .flatten()
            .zip(expected_constants.iter())
            .for_each(|(actual, expected)| assert_eq!(actual, expected));
    }

    fn expected_round_constants<'a, F: PrimeField>() -> Vec<&'a str> {
        vec![
            "25fa60d3d93901eabe9b6cc8682b1c141261bf7e9355e4565a7d6a79efaa1272",
            "dae0e024afc871a113d48c03c92cc288bbd15a178b9d93774b3eaf2c1a2605f",
            "5fe864da3b3c5521bb6bebac86069db232d11b78333ee611765389683dcf3c6",
            "1a99b7baf31a8e1dd7ef87d2755c025eb57176a1f700f6d228585c9c6838d8bf",
            "2f98a3d18d33e8bd3781825326e2c4d6db9cf3d9d755ef4294bb8d596d6caa38",
            "2f3fed1cb0b4e6f9f813bf751e9afb53c73aed1ccaae1294ddf1c753ba79e18d",
            "20186920c258098ef469e8ae6bbe6beb4955f7f88a92a15ac4139b2d147b42e4",
            "19ef5f5ffcad4c3381e6c1964f01eb996a638b4127fe94bc0b495c72de8cae04",
            "2fdfcb251801d2db13e27d027717a53ab1f6bc0680605b59d482b53e468ab99",
            "22ad87556b80145a8af70c7867518747e2174a9f4a2772d2dd49a036d37b3d53",
            "14e1f06e2c2b48e3ff0411826105c4dafe91634ecaf3caf384e1bfbf283d2046",
            "2945ed57283a711a93608e45c489b59e89b922bc93c48a6d978dd75cc505e0fd",
            "1405de7bd28acf49e75fcdd8adbe064b21f2161d1d8a1cca9ff546e63150e5ad",
            "138faf83cf006c7902c40f39437f5332caad13ddf1fa37698127a5e12b1334de",
            "292ed82d5a6cc1881df7a1c46c57c463004bb1e33264deff7471b0a70171e48a",
            "2a146067116f8b385140c1ace0895c3771dda3e69fe5d55b2a48a0c2adc9764a",
            "1889bffca466b5d9f597471786e21dfbd73a406ca6b653b80f419bff4b688798",
            "1814aaf2ab928359f5cfa916f089cece4bd440b60f510fda3845a7b806346e0c",
            "1052e190f82c8442c25c68d7c629a561946fac1dcdbc4da11e8a9967ff87a263",
            "1534af995d7100359b0072a77f48f38cf033fe8f5b70dc8f08a7df94fc07e24b",
            "233537c566a37243ab5e70c1336b6526cf121614339c8ef86ed88e22ec6d7ff8",
            "2e143c68e90534ae3f8c3c8849cc59845513af3fce778ad14b6e8a8c29c755f",
            "108413eb4e666856171ac74a62c4df2851987747b01a88e721a87f8327f8ed44",
            "a0ffcb13e3eae903c14e312c546e44babdc12c1211ca0c6d065ca4dfd9f14b1",
            "2b6194fe873fc72809ae41fd5ee22f7dc722ac490706241a1bd6fd0729286a39",
            "2d64fcfba8bdcec449fac8015dd9ee434e1e7edc7fcdc1bcd8edce103521acf0",
            "1548a6f6ea798afe70f485e32e9a9fe65d195c3541c52f3e531c30bc61e72ce8",
            "10a236bce3b0f5a53b32441aeb1bdc8db26ea6b061cc7d28abe4ba9e79d1d412",
            "2f22e1b88c33a95fef0eab5e5041bc3f61aa73911914aa31a6223ee529bec670",
            "25370119d0137c7f42dd2cfecc13554a4bb5b32ff0da414be6f47582ade92537",
            "d201528b642de38c93af48b47afa13b57417043aa997d9f9058e6c7b435bdd1",
            "1f4a28f22f5bcdb8f23fcd743001dde1c6c3937db8f262803c51a0bec8d9b4cf",
            "1f975e4712833fa3b59db29926b66f1a50db92b6b3aa6e0eaf44ab536c8b3e1d",
            "179909f97d5543125b2ee1bf158a03722f7b491a5254eb3ec9d118af7c864f69",
            "22943f6b79cdff6cc0e47b78f036bff4262191241057352f3264730a20d10907",
            "bb5b64b66c43f386917a6862be9f9c65e60bc5294ca6b8703147c6b99786c82",
            "587527d20f0d81c8a4e876c84abc675fbbf7447397e10950297787869b7edd0",
            "214cda3c03d933c9f960d39dcdb8fc8190a68f4e29346e275ee9640e73c8d3a1",
            "399a8f0765e3e56baca5b8338feb45dd02615bc80206fd6192ff75418837a5f",
            "3f42a1bfc4a75969a7b2310b1ad29327299ddfc49bf8d1023428b550fe14ff2",
            "10865432980530fb782caea0ebb7623a5997f3999101e426abe5b785a3ec6949",
            "227133d6bb1702f3b6c64035df18e5c6f422b107b0dff5cd5bcc6a51e5699da5",
            "5428e96dec6f45c38b76a77b151430d7f2e2dee9551c292dfc8ff57b3498912",
            "1dc41a91c6a16665a47b4951f017d27590fd4611fcf06e1e8b9bce3bbcb17507",
            "20ec4e1e2450283bee21616df3d33130fd9d5eb1adcf1d5c0fea6c261d705c42",
            "2511de7e262fd8f69ba1563f04684c6ccfef3d1e83b25d6140a73999079e1da3",
            "23647324e36cb9b9c56a41c86bf8520e7ffe544ca716d609f7cb82ff336b2154",
            "876885cafcec24dfa28ee9b4101f893f88fd6ffcaca69192321c1e21483e12",
            "285ff7d0163d36b519a66997f9b2b85ebf43463015391aeea051832e73566978",
            "22c7388dc021faf2ac8dff2fab25939b8ac12c20369526a4b3533e3a9f01a4c3",
            "67856eb54b103f39af1306e70d0b282bda9803abb8a5d2294518b0d8f9107ef",
            "28fb90e5f6957f95a982f55f25b171ca294749525ec31995a49214ddc59d5611",
            "29b56408f5049e94e17defd72561a05d358850cfd97c444f2827ba35f051c9ae",
            "df4b2e5766e08a196b4c6ede2c7b6a9f9a03e48709951686263784d28dad8c3",
        ]
    }
}
