use crate::bellman::pairing::ff::*;
use crate::bellman::SynthesisError;
use crate::num_bigint::BigUint;
use crate::num_traits::cast::ToPrimitive;
use crate::num_traits::{ Zero, One };
use std::{ iter, mem };


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


// in general all bit-friendly transformations (such as xor or SHA256 majority and choose operations)
// are hadled by the gadget library itself with the use of tables
// however, in some our wires are actually constants and not allocated variables
// for them we do not want apply the common strategy 
// ( split in chunks -- chunk-by-chunk transform via tables -- compose chunks back )
// but want to do all the bitwise transformations on the whole constant number in one turn
// this is done by the corresponding "normalizer" mappings, contained in this module
pub fn general_normalizer<Fr: PrimeField>(fr : Fr, bit_table: &[u64], base: u64) -> Fr
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
    let res = Fr::from_repr(repr).expect("should parse");

    res
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
