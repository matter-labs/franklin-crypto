use blake2_rfc::blake2b::Blake2b;
use blake2_rfc::blake2s::Blake2s;
use crypto::sha2::Sha256;

use jubjub::{JubjubEngine, ToUniform};


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
    use crypto::digest::Digest;
    let mut hasher = Sha256::new();
    hasher.input(persona);
    hasher.input(a);
    hasher.input(b);
    let mut bytes = [0u8; 32];
    hasher.result(&mut bytes[..]);
    E::Fs::to_uniform_32(bytes.as_ref())
}