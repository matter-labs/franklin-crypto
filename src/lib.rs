#![allow(dead_code, unused_imports, unused_macros)]
#![allow(macro_expanded_macro_exports_accessed_by_absolute_paths)]
#![warn(unused_assignments)]


pub extern crate bellman;
pub extern crate boojum;
extern crate blake2_rfc_bellman_edition as blake2_rfc;
extern crate digest;
extern crate rand;
extern crate byteorder;
extern crate tiny_keccak;
extern crate sha2;
extern crate sha3;
extern crate num_bigint;
extern crate num_traits;
extern crate num_integer;
extern crate itertools;
extern crate splitmut;
extern crate blake2;
extern crate serde;
extern crate num_derive;
extern crate indexmap;
extern crate derivative;

use bellman::pairing;
use bellman::pairing::ff;


#[macro_use]
extern crate lazy_static;

#[macro_use]
extern crate arr_macro;


#[cfg(test)]
extern crate hex;

pub mod jubjub;
pub mod alt_babyjubjub;
pub mod group_hash;
pub mod pedersen_hash;
pub mod primitives;
pub mod constants;
pub mod redjubjub;
pub mod util;
pub mod interpolation;
pub mod as_waksman;
pub mod rescue;
pub mod generic_twisted_edwards;
pub mod plonk;

pub fn log2_floor(num: usize) -> u32 {
    assert!(num > 0);

    let mut pow = 0;

    while (1 << (pow+1)) <= num {
        pow += 1;
    }

    pow
}