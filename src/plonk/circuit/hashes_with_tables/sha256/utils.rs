use super::super::utils::*;
use crate::bellman::pairing::ff::*;

pub const SHA256_CHOOSE_BASE: u64 = 7;
pub const SHA256_MAJORITY_SHEDULER_BASE: u64 = 4;

// Sha256 choose (ch) transform:
// one of major components of Sha256 hash is bitwise application for a choose function
// choose(e, f, g) = (e & f) ^ (~e & g), where e, f, g - bits for current 32bit-words E, F, G
// in order to do it effectively we take the following approach:
// convert all of E, F, G into sparse form with base 7 with the help od Sha256SparseRotateTable
// now for a given bits (e, f, g) and  t = (e & f) ^ (~e & g) we apply Daira's trick: want to create a unique encoding of 't',
// using some arithmetic relationship between e, f and g.
// one of such possible algebraic mappings is between t and e + 2f + 3g:
//
// | e | f | g | t | e + 2f + 3g |
// -------------------------------
// | 0 | 0 | 0 | 0 |           0 |
// | 0 | 0 | 1 | 1 |           3 |
// | 0 | 1 | 0 | 0 |           2 |
// | 0 | 1 | 1 | 1 |           5 |
// | 1 | 0 | 0 | 0 |           1 |
// | 1 | 0 | 1 | 0 |           4 |
// | 1 | 1 | 0 | 1 |           3 |
// | 1 | 1 | 1 | 1 |           6 |
// --------------------------------
//
// so there is a well defined algebraic encoding for ch: t = f(x) from x = e + 2f + 3g \in [0, 6] to t \in [0, 1].
pub const CH_BIT_TABLE: [u64; SHA256_CHOOSE_BASE as usize] = [
    0, // e + 2f + 3g = 0 => e = 0, f = 0, g = 0 => t = 0
    0, // e + 2f + 3g = 1 => e = 1, f = 0, g = 0 => t = 0
    0, // e + 2f + 3g = 2 => e = 0, f = 1, g = 0 => t = 0
    1, // e + 2f + 3g = 3 => e = 0, f = 0, g = 1 OR e = 1, f = 1, g = 0 => t = 1
    0, // e + 2f + 3g = 4 => e = 1, f = 0, g = 1 => t = 0
    1, // e + 2f + 3g = 5 => e = 0, f = 1, g = 1 => t = 1
    1, // e + 2f + 3g = 6 => e = 1, f = 1, g = 1 => t = 1
];
pub fn ch_u64_normalizer(n: u64) -> u64 {
    assert!(n < (SHA256_CHOOSE_BASE as u64));
    CH_BIT_TABLE[n as usize]
}

pub fn ch_ff_normalizer<Fr: PrimeField>(fr: Fr) -> Fr {
    let bit_table: [u64; SHA256_CHOOSE_BASE as usize] = [0, 0, 0, 1, 0, 1, 1];
    let base = SHA256_CHOOSE_BASE;
    general_normalizer(fr, &bit_table[..], base)
}

// Sha256 majority subroutine : majority(e, f, g) = (a & b) ^ (a & c) ^ (b & c)
// all the comments related to Sha256 choose table are applicable here, the only difference is that now
// the algebraic mapping is from x = e + f + g to y = majority(e, f, g)
// indeed:
//
// | a | b | c | y |  a + b + c  |
//  -------------------------------
// | 0 | 0 | 0 | 0 |           0 |
// | 0 | 0 | 1 | 0 |           1 |
// | 0 | 1 | 0 | 0 |           1 |
// | 0 | 1 | 1 | 1 |           2 |
// | 1 | 0 | 0 | 0 |           1 |
// | 1 | 0 | 1 | 1 |           2 |
// | 1 | 1 | 0 | 1 |           2 |
// | 1 | 1 | 1 | 0 |           3 |
//
// this well-formed function f(x): [0; 3] -> [0;1] is called majority
pub const MAJ_BIT_TABLE: [u64; SHA256_MAJORITY_SHEDULER_BASE as usize] = [
    0, // a + b + c = 0 => (a & b) ^ (a & c) ^ (b & c) = 0
    0, // a + b + c = 1 => (a & b) ^ (a & c) ^ (b & c) = 0
    1, // a + b + c = 2 => (a & b) ^ (a & c) ^ (b & c) = 1
    1, // a + b + c = 3 => (a & b) ^ (a & c) ^ (b & c) = 0
];
pub fn maj_u64_normalizer(n: u64) -> u64 {
    assert!(n < (SHA256_MAJORITY_SHEDULER_BASE as u64));
    MAJ_BIT_TABLE[n as usize]
}

pub fn maj_ff_normalizer<Fr: PrimeField>(fr: Fr) -> Fr {
    let bit_table: [u64; SHA256_MAJORITY_SHEDULER_BASE as usize] = [0, 0, 1, 1];
    let base = SHA256_MAJORITY_SHEDULER_BASE;
    general_normalizer(fr, &bit_table[..], base)
}

pub fn ch_xor_ff_normalizer<Fr: PrimeField>(fr: Fr) -> Fr {
    let bit_table: [u64; SHA256_CHOOSE_BASE as usize] = [0, 1, 0, 1, 0, 1, 0];
    let base = SHA256_CHOOSE_BASE;
    general_normalizer(fr, &bit_table[..], base)
}

pub fn maj_and_sheduler_xor_ff_normalizer<Fr: PrimeField>(fr: Fr) -> Fr {
    let bit_table: [u64; SHA256_MAJORITY_SHEDULER_BASE as usize] = [0, 1, 0, 1];
    let base = SHA256_MAJORITY_SHEDULER_BASE;
    general_normalizer(fr, &bit_table[..], base)
}
