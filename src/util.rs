use blake2_rfc::blake2b::Blake2b;
use blake2_rfc::blake2s::Blake2s;
use sha2::{Sha256, Digest};

use jubjub::{JubjubEngine, ToUniform};
use rescue::{self, RescueEngine};
use circuit::multipack;

pub fn hash_to_scalar<E: JubjubEngine>(persona: &[u8], a: &[u8], b: &[u8]) -> E::Fs {
    let mut hasher = Blake2b::with_params(64, &[], &[], persona);
    hasher.update(a);
    hasher.update(b);
    let ret = hasher.finalize();
    E::Fs::to_uniform(ret.as_ref())
}

pub fn hash_to_scalar_s<E: JubjubEngine>(persona: &[u8], a: &[u8], b: &[u8]) -> E::Fs {
    let mut hasher = Blake2s::with_params(32, &[], &[], persona);
    hasher.update(a);
    hasher.update(b);
    let ret = hasher.finalize();
    E::Fs::to_uniform_32(ret.as_ref())
}

pub fn sha256_hash_to_scalar<E: JubjubEngine>(persona: &[u8], a: &[u8], b: &[u8]) -> E::Fs {
    let mut hasher = Sha256::new();
    hasher.input(persona);
    hasher.input(a);
    hasher.input(b);
    let result = hasher.result();
    E::Fs::to_uniform_32(result.as_slice())
}

pub fn rescue_hash_to_scalar<E: RescueEngine + JubjubEngine>(
    persona: &[u8], 
    a: &[u8], 
    b: &[u8], 
    params: &<E as RescueEngine>::Params
) -> E::Fs {
    let trim_bits: u32 = (E::Fr::NUM_BITS + 63) / 64 * 64 - E::Fs::CAPACITY;
    assert!(trim_bits < 64);
    let mask: u64 = (1u64 << (64 - trim_bits)) - 1;

    let mut input_bools = Vec::with_capacity((persona.len() + a.len() + b.len()) * 8);

    input_bools.extend(multipack::bytes_to_bits(&persona));
    input_bools.extend(multipack::bytes_to_bits(&a));
    input_bools.extend(multipack::bytes_to_bits(&b));

    let inputs = multipack::compute_multipacking::<E>(&input_bools);

    let mut sponge_output: Vec<E::Fr> = rescue::rescue_hash::<E>(&params, &inputs);
    assert_eq!(sponge_output.len(), 1);

    let hash = sponge_output.pop().unwrap();

    use bellman::PrimeField;
    let mut hash_repr = hash.into_repr();

    let highest_limb: &mut u64 = hash_repr.as_mut().last_mut().unwrap();
    *highest_limb = *highest_limb & mask;

    let mut fs_repr = <<E as JubjubEngine>::Fs as PrimeField>::Repr::default();
    assert_eq!(fs_repr.as_ref().len(), hash_repr.as_ref().len());

    for (fs, fr) in fs_repr.as_mut().iter_mut().zip(hash_repr.as_ref().iter()) {
        *fs = *fr;
    }

    E::Fs::from_repr(fs_repr).unwrap()
}