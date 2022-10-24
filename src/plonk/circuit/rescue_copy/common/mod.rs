#![allow(dead_code)]
pub(crate) mod sbox;
pub(crate) mod utils;
pub(crate) mod matrix;
pub(crate) mod domain_strategy;
pub(crate) mod params;
pub(crate) const TEST_SEED: [u32; 4] = [0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654];
