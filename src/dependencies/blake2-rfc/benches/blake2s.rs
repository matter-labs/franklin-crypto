#![feature(test)]

extern crate blake2_rfc;
extern crate test;

use std::iter::repeat;
use std::vec::Vec;
use test::Bencher;

use blake2_rfc::blake2s::Blake2s;
use blake2_rfc::_selftest_seq as selftest_seq;

fn bench_blake2s(bytes: usize, b: &mut Bencher) {
    let data: Vec<u8> = repeat(selftest_seq(1024))
        .flat_map(|v| v)
        .take(bytes)
        .collect();

    b.bytes = bytes as u64;
    b.iter(|| {
        let mut state = Blake2s::default();
        state.update(&data[..]);
        state.finalize()
    })
}

#[bench] fn blake2s_16(b: &mut Bencher) { bench_blake2s(16, b) }
#[bench] fn blake2s_4k(b: &mut Bencher) { bench_blake2s(4096, b) }
#[bench] fn blake2s_64k(b: &mut Bencher) { bench_blake2s(65536, b) }
