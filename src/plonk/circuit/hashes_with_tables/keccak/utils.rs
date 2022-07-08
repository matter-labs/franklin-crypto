use super::super::utils::*;
use crate::bellman::pairing::ff::*;

pub const KECCAK_FIRST_SPARSE_BASE: u64 = 13;
pub fn keccak_u64_first_converter(n: u64) -> u64 {
    assert!(n < KECCAK_FIRST_SPARSE_BASE);
    // simple xor
    n & 1
}

// conveter for the function that unites together xi and i trnasformations of keccak:
// f_log = a ^ (~b & c) ^ d
// the corresponding algebraic encoding is f_alg: 2a + b + 3c + 2d
// | idx | a | b | c | d | a ^ (~b & c) ^ d | 2a + b + 3c + 2d |
// -------------------------------------------------------------
// |  0  | 0 | 0 | 0 | 0 |         0        |          0       |
// |  1  | 0 | 0 | 0 | 1 |         1        |          2       |
// |  2  | 0 | 0 | 1 | 0 |         1        |          3       |
// |  3  | 0 | 0 | 1 | 1 |         0        |          5       |
// |  4  | 0 | 1 | 0 | 0 |         0        |          1       |
// |  5  | 0 | 1 | 0 | 1 |         1        |          3       |
// |  6  | 0 | 1 | 1 | 0 |         0        |          4       |
// |  7  | 0 | 1 | 1 | 1 |         1        |          6       |
// |  8  | 1 | 0 | 0 | 0 |         1        |          2       |
// |  9  | 1 | 0 | 0 | 1 |         0        |          4       |
// | 10  | 1 | 0 | 1 | 0 |         0        |          5       |
// | 11  | 1 | 0 | 1 | 1 |         1        |          7       |
// | 12  | 1 | 1 | 0 | 0 |         1        |          3       |
// | 13  | 1 | 1 | 0 | 1 |         0        |          5       |
// | 14  | 1 | 1 | 1 | 0 |         1        |          6       |
// | 15  | 1 | 1 | 1 | 1 |         0        |          8       |
// -----------------------------------------|------------------|
// this table shows that mapping f_alg -> f_log is indeed well-defined
pub const KECCAK_SECOND_SPARSE_BASE: u64 = 9;
pub fn keccak_u64_second_converter(n: u64) -> u64 {
    assert!(n < KECCAK_SECOND_SPARSE_BASE);
    let bit_table: [u64; KECCAK_SECOND_SPARSE_BASE as usize] = [0, 0, 1, 1, 0, 0, 1, 1, 0];
    bit_table[n as usize]
}
