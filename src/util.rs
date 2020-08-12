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
    use crate::rescue::RescueHashParams;
    use bellman::{Field, PrimeField};
    use bellman::pairing::ff::BitIterator;

    assert!(params.rate() >= 2, "we will need to squeeze twice");

    // in the essence we perform modular reduction, so to ensure
    // uniformity we only take half of the bits, so non-uniformity is
    // around 1 / (char / (E::Fs::CAPACITY / 2))
    // that is around 1/2^126
    let take_bits = (E::Fs::CAPACITY / 2) as usize;

    let mut input_bools = Vec::with_capacity((persona.len() + a.len() + b.len()) * 8);

    input_bools.extend(multipack::bytes_to_bits(&persona));
    input_bools.extend(multipack::bytes_to_bits(&a));
    input_bools.extend(multipack::bytes_to_bits(&b));

    let inputs = multipack::compute_multipacking::<E>(&input_bools);

    let mut sponge = rescue::StatefulRescue::<E>::new(&params);
    sponge.specialize(inputs.len() as u8);
    sponge.absorb(&inputs);

    // draw two values from hash and use lowest bits
    let s0 = sponge.squeeze_out_single().into_repr();
    let s1 = sponge.squeeze_out_single().into_repr();

    let mut s0_le_bits: Vec<_> = BitIterator::new(&s0).collect();
    s0_le_bits.reverse();

    let mut s1_le_bits: Vec<_> = BitIterator::new(&s1).collect();
    s1_le_bits.reverse();

    let mut fs_bits = s0_le_bits;
    fs_bits.truncate(take_bits);
    fs_bits.extend_from_slice(&s1_le_bits[0..take_bits]);
    assert!(fs_bits.len() == E::Fs::CAPACITY as usize);

    // perform bit reconstruction starting from LSB
    let mut current = E::Fs::one();
    let mut scalar = E::Fs::zero();
    for bit in fs_bits.into_iter() {
        if bit {
            scalar.add_assign(&current);
        }
        current.double();
    }
       
    scalar
}

pub fn resize_grow_only<T: Clone>(to_resize: &mut Vec<T>, new_size: usize, pad_with: T) {
    assert!(to_resize.len() <= new_size);
    to_resize.resize(new_size, pad_with);
}
