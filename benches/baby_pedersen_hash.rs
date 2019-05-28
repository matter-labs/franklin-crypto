#![feature(test)]

extern crate rand;
extern crate test;
extern crate bellman_ce as bellman;
extern crate franklin_crypto;

use rand::{Rand, thread_rng};
use bellman::pairing::bn256::Bn256;
use franklin_crypto::alt_babyjubjub::AltJubjubBn256;
use franklin_crypto::pedersen_hash::{pedersen_hash, Personalization};

#[bench]
fn bench_baby_pedersen_hash(b: &mut test::Bencher) {
    let params = AltJubjubBn256::new();
    let rng = &mut thread_rng();
    let bits = (0..510).map(|_| bool::rand(rng)).collect::<Vec<_>>();
    let personalization = Personalization::MerkleTree(31);

    b.iter(|| {
        pedersen_hash::<Bn256, _>(personalization, bits.clone(), &params)
    });
}
