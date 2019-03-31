#![feature(test)]

extern crate blake2_rfc;
extern crate test;

use std::iter::repeat;
use std::vec::Vec;
use test::Bencher;

use blake2_rfc::blake2b::Blake2b;
use blake2_rfc::_selftest_seq as selftest_seq;

fn bench_blake2b(bytes: usize, b: &mut Bencher) {
    let data: Vec<u8> = repeat(selftest_seq(1024))
        .flat_map(|v| v)
        .take(bytes)
        .collect();

    b.bytes = bytes as u64;
    b.iter(|| {
        let mut state = Blake2b::default();
        state.update(&data[..]);
        state.finalize()
    })
}

#[bench] fn blake2b_16(b: &mut Bencher) { bench_blake2b(16, b) }
#[bench] fn blake2b_4k(b: &mut Bencher) { bench_blake2b(4096, b) }
#[bench] fn blake2b_64k(b: &mut Bencher) { bench_blake2b(65536, b) }
