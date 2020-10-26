use crate::bellman::pairing::ff::*;
use crate::num_bigint::BigUint;
use crate::num_traits::cast::ToPrimitive;
use crate::num_traits::{ Zero, One };
use std::{ iter, mem };


pub const SHA256_CHOOSE_BASE: u64 = 7;
pub const SHA256_MAJORITY_SHEDULER_BASE: u64 = 4;


pub fn pow(base: usize, exp: usize) -> usize {

    let mut res = 1;
    for _i in 0..exp {
        res *= base;
    }

    res
}

pub fn biguint_pow(base: usize, exp: usize) -> BigUint {
    let mut res = BigUint::one();
    for _i in 0..exp {
        res *= base;
    }

    res
}

pub fn u64_to_ff<Fr: PrimeField>(n: u64) -> Fr {
    let mut repr : <Fr as PrimeField>::Repr = Fr::zero().into_repr();
    repr.as_mut()[0] = n;
    let res = Fr::from_repr(repr).expect("should parse");
    res
}

pub fn u64_exp_to_ff<Fr: PrimeField>(n: u64, exp: u64) -> Fr {
    let mut repr : <Fr as PrimeField>::Repr = Fr::zero().into_repr();
    repr.as_mut()[0] = n;
    let mut res = Fr::from_repr(repr).expect("should parse");

    if exp != 0 {
        res = res.pow(&[exp]);
    }
    res
}

pub fn ff_to_u64<Fr: PrimeField>(fr: &Fr) -> u64 {
    let repr = fr.into_repr();
    for i in 1..4 {
        assert_eq!(repr.as_ref()[i], 0);
    }
    repr.as_ref()[0]
}

fn biguint_to_ff<Fr: PrimeField>(value: &BigUint) -> Fr {
    Fr::from_str(&value.to_str_radix(10)).unwrap()
}


// converts x = (x_0, x_1, ..., x_n) - bit decomposition of x into y = \sum_{i=1}^{n} x_i * base^i
pub fn map_into_sparse_form(input: usize, base: usize) -> BigUint
{
    // if base is zero, than no convertion is actually needed
    if base == 0 {
        return BigUint::from(input);
    }
    
    let mut out = BigUint::zero();
    let mut base_accumulator = BigUint::one();
    let mut converted = input;

    while converted > 0 {
        let sparse_bit = converted & 1;
        converted >>= 1;
        if sparse_bit > 0 {
            out += base_accumulator.clone();
        }
        base_accumulator *= base;
    }
    
    out
}

pub fn map_from_sparse_form(input: usize, base: usize) -> usize
{
    let mut target : usize = input;
    let mut output : usize = 0;
    let mut count : usize = 0;

    while target > 0 {
        let slice = target % base;
        // althoough slice is not bound to {0, 1} we are only interested in its value modulo 2
        let bit = slice & 1usize;
        output += bit << count;
        count += 1;
        target = target / base;
    }

    output
}

// for given x=(x_0, x_1, ..., x_n) extract the k lower bits: y = (x_0, x_1, ..., x_{k-1}, 0, ..., 0)
// and then rotate
// NOTE: by rotate we always mean right rotate of 32-bit numbers!
pub fn rotate_extract(value: usize, rotation: usize, extraction: usize) -> usize
{
    let temp = if extraction > 0 {value & ((1 << extraction) - 1)} else {value}; 
    let res = if rotation > 0 {(temp >> rotation) + ((temp << (32 - rotation)) & 0xffffffff) } else {temp};

    res
}

pub fn shift_right(value: usize, shift: usize) -> usize
{
    if shift > 0 {value >> shift} else {value}
}


// in general all bit-friendly transformations (such as xor or SHA256 majority and choose operations)
// are hadled by the gadget library itself with the use of tables
// however, in some our wires are actually constants and not allocated variables
// for them we do not want apply the common strategy 
// ( split in chunks -- chunk-by-chunk transform via tables -- compose chunks back )
// but want to do all the bitwise transformations on the whole constant number in one turn
// this is done by the corresponding "normalizer" mappings, contained in this module
fn general_normalizer<Fr: PrimeField>(fr : Fr, bit_table: &[u64], base: u64) -> Fr
{
    let mut input = BigUint::default();
    let fr_repr = fr.into_repr();
    for n in fr_repr.as_ref().iter().rev() {
        input <<= 64;
        input += *n;
    }

    let mut acc : u64 = 0; 
    let mut count = 0;
 
    while !input.is_zero() {
        let remainder = (input.clone() % BigUint::from(base)).to_u64().unwrap();
        let bit = bit_table[remainder as usize];
        acc += bit << count;
        input /= base;
        count += 1;
    }

    let mut repr : <Fr as PrimeField>::Repr = Fr::zero().into_repr();
    repr.as_mut()[0] = acc;
    let mut res = Fr::from_repr(repr).expect("should parse");

    res
}

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
pub const ch_bit_table : [u64; SHA256_CHOOSE_BASE as usize] = [
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
    ch_bit_table[n as usize]
}

pub fn ch_ff_normalizer<Fr: PrimeField>(fr: Fr) -> Fr 
{
    let bit_table : [u64; SHA256_CHOOSE_BASE as usize] = [ 0, 0, 0, 1, 0, 1, 1 ];
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
pub const maj_bit_table : [u64; SHA256_MAJORITY_SHEDULER_BASE as usize] = [
    0, // a + b + c = 0 => (a & b) ^ (a & c) ^ (b & c) = 0
    0, // a + b + c = 1 => (a & b) ^ (a & c) ^ (b & c) = 0
    1, // a + b + c = 2 => (a & b) ^ (a & c) ^ (b & c) = 1
    1, // a + b + c = 3 => (a & b) ^ (a & c) ^ (b & c) = 0
];
pub fn maj_u64_normalizer(n: u64) -> u64 {
    assert!(n < (SHA256_MAJORITY_SHEDULER_BASE as u64));
    maj_bit_table[n as usize]
}

pub fn maj_ff_normalizer<Fr: PrimeField>(fr: Fr) -> Fr 
{
    let bit_table : [u64; SHA256_MAJORITY_SHEDULER_BASE as usize] =  [ 0, 0, 1, 1 ]; 
    let base = SHA256_MAJORITY_SHEDULER_BASE;
    general_normalizer(fr, &bit_table[..], base)
}

pub fn ch_xor_ff_normalizer<Fr: PrimeField>(fr: Fr) -> Fr 
{
    let bit_table : [u64; SHA256_CHOOSE_BASE as usize] = [ 0, 1, 0, 1, 0, 1, 0 ];
    let base = SHA256_CHOOSE_BASE;
    general_normalizer(fr, &bit_table[..], base)
}

pub fn maj_and_sheduler_xor_ff_normalizer<Fr: PrimeField>(fr: Fr) -> Fr 
{
    let bit_table : [u64; SHA256_MAJORITY_SHEDULER_BASE as usize] =  [ 0, 1, 0, 1 ]; 
    let base = SHA256_MAJORITY_SHEDULER_BASE;
    general_normalizer(fr, &bit_table[..], base)
}


// returns closets upper integer to a / b
pub fn round_up(a: usize, b : usize) -> usize {
    let additional_chunks : usize = if a % b > 0 {1} else {0};
    a/b + additional_chunks
}


pub trait IdentifyFirstLast: Iterator + Sized {
    fn identify_first_last(self) -> Iter<Self>;
}

impl<I> IdentifyFirstLast for I where I: Iterator {
    fn identify_first_last(self) -> Iter<Self> {
        Iter(true, self.peekable())
    }
}

pub struct Iter<I>(bool, iter::Peekable<I>) where I: Iterator;

impl<I> Iterator for Iter<I> where I: Iterator {
    type Item = (bool, bool, I::Item);

    fn next(&mut self) -> Option<Self::Item> {
        let first = mem::replace(&mut self.0, false);
        self.1.next().map(|e| (first, self.1.peek().is_none(), e))
    }
}

