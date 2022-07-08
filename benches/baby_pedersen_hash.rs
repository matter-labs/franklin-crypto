#![feature(test)]

extern crate bellman;
extern crate franklin_crypto;
extern crate rand;
extern crate test;

use bellman::pairing::bn256::Bn256;
use franklin_crypto::alt_babyjubjub::AltJubjubBn256;
use franklin_crypto::pedersen_hash::{pedersen_hash, Personalization};
use rand::{thread_rng, Rand};

#[bench]
fn bench_baby_pedersen_hash(b: &mut test::Bencher) {
    let params = AltJubjubBn256::new();
    let rng = &mut thread_rng();
    let bits = (0..510).map(|_| bool::rand(rng)).collect::<Vec<_>>();
    let personalization = Personalization::MerkleTree(31);

    b.iter(|| pedersen_hash::<Bn256, _>(personalization, bits.clone(), &params));
}
