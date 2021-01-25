#![allow(dead_code, unused_imports, unused_macros)]
#![warn(unused_assignments)]

pub extern crate bellman;
extern crate blake2_rfc_bellman_edition as blake2_rfc;
extern crate digest;
extern crate rand;
extern crate byteorder;
extern crate tiny_keccak;
extern crate sha2;
extern crate hmac;
//extern crate poseidon_hash;
extern crate num_bigint;
extern crate num_traits;
extern crate num_integer;

extern crate itertools;
extern crate splitmut;
extern crate blake2;

#[cfg(test)]
#[macro_use]
extern crate hex_literal;

#[cfg(test)]
extern crate hex;

pub mod babyjubjub;
pub mod jubjub;
pub mod alt_babyjubjub;
pub mod baby_group_hash;
pub mod group_hash;
pub mod circuit;
pub mod baby_pedersen_hash;
pub mod pedersen_hash;
pub mod primitives;
pub mod constants;
pub mod redbabyjubjub;
pub mod redjubjub;
pub mod baby_util;
pub mod util;
pub mod eddsa;
pub mod interpolation;
pub mod as_waksman;
pub mod rescue;

#[cfg(feature = "plonk")]
pub mod plonk;

extern crate serde;
#[macro_use]
extern crate serde_derive;

pub fn log2_floor(num: usize) -> u32 {
    assert!(num > 0);

    let mut pow = 0;

    while (1 << (pow+1)) <= num {
        pow += 1;
    }

    pow
}