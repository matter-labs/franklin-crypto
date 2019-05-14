#![feature(test)]

extern crate rand;
extern crate test;
extern crate bellman_ce as bellman;
extern crate sapling_crypto_ce as sapling_crypto;

use rand::{XorShiftRng, SeedableRng, Rng};
use sapling_crypto::group_hash::BlakeHasher;
use bellman::pairing::bn256::{Bn256, Fr};
use sapling_crypto::poseidon::{poseidon_hash, PoseidonHashParams};
use sapling_crypto::poseidon::bn256::Bn256PoseidonParams;

#[bench]
fn bench_poseidon_hash(b: &mut test::Bencher) {
    let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
    let params = Bn256PoseidonParams::new::<BlakeHasher>();
    let input: Vec<Fr> = (0..(params.t()-1)*2).map(|_| rng.gen()).collect();

    b.iter(|| {
        poseidon_hash::<Bn256>(&params, &input[..]);
    });
}
