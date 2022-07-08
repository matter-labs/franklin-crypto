use crate::bellman::pairing::Engine;

use crate::bellman::pairing::ff::{BitIterator, Field, PrimeField, PrimeFieldRepr};

use crate::bellman::SynthesisError;

use crate::bellman::plonk::better_better_cs::cs::{
    ArithmeticTerm, Coefficient, ConstraintSystem, Gate, GateInternal, LinearCombinationOfTerms,
    MainGate, MainGateTerm, PlonkConstraintSystemParams, PolynomialInConstraint,
    PolynomialMultiplicativeTerm, TimeDilation, Variable, Width4MainGateWithDNext,
};
use super::*;
use num_bigint::BigUint;

use super::super::allocated_num::{AllocatedNum, Num};
use super::super::linear_combination::LinearCombination;
use super::super::simple_term::Term;

use super::constraint_num_bits;

// in principle this is valid for both cases:
// when we represent some (field) element as a set of limbs
// that are power of two, or if it's a single element as in RNS

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LimbedRepresentationParameters<E: Engine> {
    pub limb_size_bits: usize,
    pub limb_max_value: BigUint,
    pub limb_max_intermediate_value: BigUint,
    pub limb_intermediate_value_capacity: usize,
    pub shift_left_by_limb_constant: E::Fr,
    pub shift_right_by_limb_constant: E::Fr,
    pub mul_two_constant: E::Fr,
    pub div_two_constant: E::Fr,
}

impl<E: Engine> LimbedRepresentationParameters<E> {
    pub fn new(limb_size: usize, intermediate_value_capacity: usize) -> Self {
        // assert!(limb_size <= (E::Fr::CAPACITY as usize) / 2);
        // assert!(intermediate_value_capacity <= E::Fr::CAPACITY as usize);

        let limb_max_value = (BigUint::from(1u64) << limb_size) - BigUint::from(1u64);

        let tmp = BigUint::from(1u64) << limb_size;

        let shift_left_by_limb_constant = E::Fr::from_str(&tmp.to_string()).unwrap();

        let shift_right_by_limb_constant = shift_left_by_limb_constant.inverse().unwrap();

        let mut two = E::Fr::one();
        two.double();

        let div_two_constant = two.inverse().unwrap();

        Self {
            limb_size_bits: limb_size,
            limb_max_value,
            limb_max_intermediate_value: (BigUint::from(1u64) << intermediate_value_capacity)
                - BigUint::from(1u64),
            limb_intermediate_value_capacity: intermediate_value_capacity,
            shift_left_by_limb_constant,
            shift_right_by_limb_constant,
            mul_two_constant: two,
            div_two_constant,
        }
    }
}

// Simple term and bit counter/max value counter that we can update
#[derive(Clone, Debug)]
pub struct Limb<E: Engine> {
    pub term: Term<E>,
    pub max_value: BigUint,
}

pub(crate) fn get_num_bits<F: PrimeField>(el: &F) -> usize {
    let repr = el.into_repr();
    let mut num_bits = repr.as_ref().len() * 64;
    for &limb in repr.as_ref().iter().rev() {
        if limb == 0 {
            num_bits -= 64;
        } else {
            num_bits -= limb.leading_zeros() as usize;
            break;
        }
    }

    num_bits
}

impl<E: Engine> Limb<E> {
    pub fn new(term: Term<E>, max_value: BigUint) -> Self {
        Self { term, max_value }
    }

    pub fn new_constant(value: BigUint) -> Self {
        let v = biguint_to_fe(value.clone());

        let term = Term::<E>::from_constant(v);

        Self {
            term,
            max_value: value,
        }
    }

    pub fn new_constant_from_field_value(value: E::Fr) -> Self {
        let term = Term::<E>::from_constant(value);

        Self {
            term,
            max_value: fe_to_biguint(&value),
        }
    }

    pub fn max_bits(&mut self) -> usize {
        (self.max_value.bits() as usize) + 1
    }

    pub fn inc_max(&mut self, by: &BigUint) {
        self.max_value += by;
    }

    pub fn scale_max(&mut self, by: &BigUint) {
        self.max_value *= by;
    }

    pub fn max_value(&self) -> BigUint {
        self.max_value.clone()
    }

    pub fn get_value(&self) -> Option<BigUint> {
        some_fe_to_biguint(&self.term.get_value())
    }

    pub fn scale(&mut self, by: &E::Fr) {
        self.term.scale(by);
    }

    pub fn negate(&mut self) {
        self.term.negate();
    }

    pub fn add_constant(&mut self, c: &E::Fr) {
        self.term.add_constant(&c);
    }

    pub fn get_field_value(&self) -> Option<E::Fr> {
        let v = self.term.get_value();

        v
    }

    pub fn is_constant(&self) -> bool {
        self.term.is_constant()
    }

    pub fn collapse_into_constant(&self) -> E::Fr {
        self.term.get_constant_value()
    }

    pub fn collapse_into_num<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<Num<E>, SynthesisError> {
        self.term.collapse_into_num(cs)
    }

    pub fn is_zero(&self) -> bool {
        if self.is_constant() {
            self.term.get_constant_value().is_zero()
        } else {
            false
        }
    }
}

pub fn repr_to_biguint<F: PrimeField>(repr: &F::Repr) -> BigUint {
    let mut b = BigUint::from(0u64);
    for &limb in repr.as_ref().iter().rev() {
        b <<= 64;
        b += BigUint::from(limb)
    }

    b
}

#[track_caller]
pub fn mod_inverse(el: &BigUint, modulus: &BigUint) -> BigUint {
    use crate::num_bigint::BigInt;
    use crate::num_integer::{ExtendedGcd, Integer};
    use crate::num_traits::{One, ToPrimitive, Zero};

    if el.is_zero() {
        panic!("division by zero");
    }

    let el_signed = BigInt::from(el.clone());
    let modulus_signed = BigInt::from(modulus.clone());

    let ExtendedGcd { gcd, x: _, y, .. } = modulus_signed.extended_gcd(&el_signed);
    assert!(gcd.is_one());
    let y = if y < BigInt::zero() {
        let mut y = y;
        y += modulus_signed;

        y.to_biguint().expect("must be > 0")
    } else {
        y.to_biguint().expect("must be > 0")
    };

    debug_assert!(el.clone() * &y % modulus == BigUint::from(1u64));

    debug_assert!(&y < modulus);

    y
}

pub fn biguint_to_fe<F: PrimeField>(value: BigUint) -> F {
    F::from_str(&value.to_str_radix(10)).unwrap()
}

pub fn biguint_to_repr<F: PrimeField>(mut value: BigUint) -> F::Repr {
    use num_traits::ToPrimitive;

    let mut repr = F::Repr::default();
    let mask = BigUint::from(1u64) << 64;
    for l in repr.as_mut().iter_mut() {
        let limb: BigUint = value.clone() % &mask;
        *l = limb.to_u64().unwrap();
        value >>= 64;
    }

    repr
}

pub fn some_biguint_to_fe<F: PrimeField>(value: &Option<BigUint>) -> Option<F> {
    match value {
        Some(value) => {
            let n = F::from_str(&value.to_str_radix(10)).unwrap();

            Some(n)
        }
        None => None,
    }
}

pub fn fe_to_biguint<F: PrimeField>(el: &F) -> BigUint {
    let repr = el.into_repr();

    repr_to_biguint::<F>(&repr)
}

pub fn some_fe_to_biguint<F: PrimeField>(el: &Option<F>) -> Option<BigUint> {
    match el {
        Some(el) => {
            let repr = el.into_repr();

            let ret = repr_to_biguint::<F>(&repr);

            Some(ret)
        }
        None => None,
    }
}

pub fn get_bit_slice(v: BigUint, start: usize, end: usize) -> BigUint {
    let mut tmp = v;
    tmp >>= start;

    let mask = BigUint::from(1u64) << (end - start);

    tmp % mask
}

pub fn split_into_fixed_width_limbs(mut fe: BigUint, bits_per_limb: usize) -> Vec<BigUint> {
    let mut num_limbs = (fe.bits() as usize) / bits_per_limb;
    if (fe.bits() as usize) % bits_per_limb != 0 {
        num_limbs += 1;
    }

    let mut limbs = Vec::with_capacity(num_limbs);

    let modulus = BigUint::from(1u64) << bits_per_limb;

    for _ in 0..num_limbs {
        let limb = fe.clone() % &modulus;
        limbs.push(limb);
        fe >>= bits_per_limb;
    }

    limbs.reverse();

    limbs
}

#[track_caller]
pub fn split_some_into_fixed_number_of_limbs(
    fe: Option<BigUint>,
    bits_per_limb: usize,
    num_limbs: usize,
) -> Vec<Option<BigUint>> {
    if let Some(fe) = fe {
        let mut fe = fe;
        assert!(fe.bits() as usize <= bits_per_limb * num_limbs);
        let mut limbs = Vec::with_capacity(num_limbs);

        let modulus = BigUint::from(1u64) << bits_per_limb;

        for _ in 0..num_limbs {
            let limb = fe.clone() % &modulus;
            limbs.push(Some(limb));
            fe >>= bits_per_limb;
        }

        limbs
    } else {
        vec![None; num_limbs]
    }
}

#[track_caller]
pub fn split_into_fixed_number_of_limbs(
    mut fe: BigUint,
    bits_per_limb: usize,
    num_limbs: usize,
) -> Vec<BigUint> {
    let mut limbs = Vec::with_capacity(num_limbs);

    let modulus = BigUint::from(1u64) << bits_per_limb;

    for _ in 0..num_limbs {
        let limb = fe.clone() % &modulus;
        limbs.push(limb);
        fe >>= bits_per_limb;
    }

    limbs
}

#[track_caller]
pub fn split_some_into_limbs_of_variable_width(
    fe: Option<BigUint>,
    bits_per_limb: &[usize],
) -> Vec<Option<BigUint>> {
    if let Some(fe) = fe {
        let mut fe = fe;
        let full_width = bits_per_limb.iter().sum();
        assert!(
            fe.bits() as usize <= full_width,
            "can fit {} bits maximum, but got {}",
            full_width,
            fe.bits()
        );
        let mut limbs = Vec::with_capacity(bits_per_limb.len());

        for &width in bits_per_limb.iter() {
            let modulus = BigUint::from(1u64) << width;
            let limb = fe.clone() % &modulus;
            limbs.push(Some(limb));
            fe >>= width;
        }

        limbs
    } else {
        vec![None; bits_per_limb.len()]
    }
}

pub fn slice_into_limbs_of_max_size(
    value: Option<BigUint>,
    max_width: usize,
    limb_width: usize,
) -> (Vec<Option<BigUint>>, Vec<usize>) {
    let mut limb_sizes = vec![];
    let mut tmp = max_width;
    loop {
        if tmp > limb_width {
            tmp -= limb_width;
            limb_sizes.push(limb_width);
        } else {
            limb_sizes.push(tmp);
            break;
        }
    }

    let mask = BigUint::from(1u64) << limb_width;

    let limb_values = if let Some(value) = value {
        let mut values = Vec::with_capacity(limb_sizes.len());
        let mut tmp = value.clone();
        for _ in 0..limb_sizes.len() {
            let value = tmp.clone() % &mask;
            values.push(Some(value));
            tmp >>= limb_width;
        }

        values
    } else {
        vec![None; limb_sizes.len()]
    };

    (limb_values, limb_sizes)
}

pub(crate) fn make_multiple(mut value: usize, multiple_of: usize) -> usize {
    let remainder = value % multiple_of;
    if remainder != 0 {
        value += multiple_of - remainder;
    }

    value
}
#[track_caller]
pub fn split_into_slices<F: PrimeField>(
    el: &F,
    slice_width: usize,
    num_slices: usize
) -> Vec<F> {
    let mut repr = el.into_repr();
    assert!(repr.num_bits() as usize <= slice_width * num_slices, "limit is {} bits, got {}", slice_width * num_slices, repr.num_bits());
    let mut slices = Vec::with_capacity(num_slices);
    if slice_width < 64 {    
        let mask = (1u64 << slice_width) - 1u64;
        for _ in 0..num_slices {
            let slice = repr.as_ref()[0] & mask;

            let mut r = F::Repr::default();
            r.as_mut()[0] = slice;

            let slice = F::from_repr(r).unwrap();
            slices.push(slice);

            repr.shr(slice_width as u32);
        }
    }
    else {
        let it = repr.as_ref().iter().map(|x| u64_to_fe::<F>(*x)).take(num_slices);
        slices.extend(it);
    };

    slices
}
use std::{ iter, mem };
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
pub fn compute_shifts<F: PrimeField>() -> Vec<F> {
    let mut result = Vec::with_capacity(F::CAPACITY as usize);
    let mut el = F::one();
    result.push(el);
    for _ in 1..F::CAPACITY {
        el.double();
        result.push(el);
    }

    result
}
use plonk::circuit::boolean::Boolean;
const RANGE_CHECK_TABLE_WIDTH: usize = 16;
const RANGE_CHECK_THRESHOLD: usize = 64;
pub fn add_range_check<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS, 
    for_element: &Num<E>, 
    marker: u8, 
    width: usize
) -> Result<(), SynthesisError> {
    assert!(width <= E::Fr::CAPACITY as usize);

    // split into variables of new length and enforce decomposition
    assert_eq!(for_element.is_constant(), false);
    let num_of_chunks = (width + RANGE_CHECK_THRESHOLD - 1) / RANGE_CHECK_THRESHOLD;
    let value = for_element.get_value();
    let witness_chunks = split_some_into_slices(value, RANGE_CHECK_THRESHOLD, num_of_chunks);

    let mut chunks = Vec::with_capacity(witness_chunks.len());
    let has_remainder = num_of_chunks * RANGE_CHECK_THRESHOLD != width;
    let last_chunk_width = if has_remainder {
        width % RANGE_CHECK_THRESHOLD
    }
    else {
        RANGE_CHECK_THRESHOLD
    };

    for (_, is_last, wit) in witness_chunks.iter().identify_first_last() {
        let allocated_num = AllocatedNum::alloc(cs, || wit.grab())?;
        let num = Num::Variable(allocated_num);
        chunks.push(num);
    }
      
    let shifts = compute_shifts();
    let mut offset = 0;
    let mut lc = LinearCombination::zero();
    for chunk in chunks.iter() {
        lc.add_assign_number_with_coeff(&chunk, shifts[offset]);
        offset += RANGE_CHECK_THRESHOLD;
    }
    let mut minus_one = E::Fr::one();
    minus_one.negate();
    lc.add_assign_number_with_coeff(&for_element, minus_one);
    lc.enforce_zero(cs)
}

use num_traits::Zero;
use plonk::circuit::boolean::AllocatedBit;
use plonk::circuit::bigint::single_table_range_constraint::enforce_using_single_column_table_for_shifted_variable_optimized;
pub fn simple_add<E: Engine, CS: ConstraintSystem<E>>(cs: &mut CS, a: [Num<E>; 4], b:[Num<E>; 4] )->Result<Vec<Num<E>>, SynthesisError>{
    let mut big_big_biguint_a = BigUint::zero();
    let mut big_big_biguint_b = BigUint::zero();
    for i in 0..4{
        let mut v_a = BigUint::zero();
        let mut v_b = BigUint::zero();
        match a[i] {
            Num::Constant(value) => {
                v_a = fe_to_biguint(&value);
            }

            Num::Variable(var) =>{
                enforce_using_single_column_table_for_shifted_variable_optimized(cs, &var, E::Fr::one(), 64);
                let mut w = var.get_value().unwrap();
                v_a = fe_to_biguint(&w);
            }
        }
        big_big_biguint_a += v_a * BigUint::from(1u64) << 64u32* (i as u32);
        match b[i] {
            Num::Constant(value) => {
                v_b = fe_to_biguint(&value);
            }

            Num::Variable(var) =>{
                enforce_using_single_column_table_for_shifted_variable_optimized(cs, &var, E::Fr::one(), 64);
                let mut w = var.get_value().unwrap();
                v_b = fe_to_biguint(&w);
            }
        }
        big_big_biguint_b += v_b * BigUint::from(1u64) << 64u32* (i as u32);
    }
    // let big_big_biguint_c = big_big_biguint_a.clone() + big_big_biguint_b.clone();
    // let c_in_limbs_with = split_some_into_fixed_number_of_limbs(Some(big_big_biguint_c), 64, 4 );

    // println!("test1{:?}", c_in_limbs_with);
    
    let a_in_limbs = split_some_into_fixed_number_of_limbs(Some(big_big_biguint_a), 64, 4 );
    let b_in_limbs = split_some_into_fixed_number_of_limbs(Some(big_big_biguint_b), 64, 4 );

    let mut c_in_limbs: Vec<Option<BigUint>> = vec![];
    let mut of = Some(BigUint::zero());
    let mut pre_of = Some(BigUint::zero());
    let mut alloc_pre_of = Boolean::zero();
    for (l, r) in a_in_limbs.into_iter().zip(b_in_limbs.into_iter()) {

        let fe_a =  some_biguint_to_fe::<E::Fr>(&l);
        let fe_b =  some_biguint_to_fe::<E::Fr>(&r);
        let allocated_a = Num::Variable(AllocatedNum::alloc(cs, || Ok(*fe_a.get()?)).unwrap());
        let allocated_b = Num::Variable(AllocatedNum::alloc(cs, || Ok(*fe_b.get()?)).unwrap());

        let new_limb = l.as_ref().unwrap() + r.as_ref().unwrap()+ pre_of.as_ref().unwrap();
        let modulus = BigUint::from(1u64) << 64u32;
        of = Some((( l.unwrap() % &modulus) + (r.unwrap() % &modulus)) >> 64u8);

        let intermediate_of_witness = Some(!of.as_ref().unwrap().is_zero());

        let alloc_of = Boolean::from(
            AllocatedBit::alloc(cs, intermediate_of_witness).unwrap()
        );
        let mut limbs_for_c= BigUint::zero();
        if intermediate_of_witness.unwrap() {
            let shift = BigUint::from(1u64) << 64u32;
            limbs_for_c = new_limb.clone() - of.as_ref().unwrap()*shift;
            c_in_limbs.push(Some(limbs_for_c.clone()));
        }
        else{
            limbs_for_c = new_limb.clone();
            c_in_limbs.push(Some(new_limb));
        }
        let fe_c =  some_biguint_to_fe::<E::Fr>(&Some(limbs_for_c.clone()));
        let allc_num = AllocatedNum::alloc(cs, || Ok(*fe_c.get()?)).unwrap();
        let allocated_c = Num::Variable(allc_num);
        enforce_using_single_column_table_for_shifted_variable_optimized(cs, &allc_num, E::Fr::one(), 64);


        let shifts = compute_shifts::<E::Fr>();
        let mut minus_one = E::Fr::one();
        minus_one.negate();
    
        let mut word_shift = shifts[64].clone();
        let mut minus_word_shift = word_shift;
        minus_word_shift.negate();

        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&allocated_a, E::Fr::one());
        lc.add_assign_number_with_coeff(&allocated_b, E::Fr::one());
        lc.add_assign_boolean_with_coeff(&alloc_pre_of, E::Fr::one());
        lc.add_assign_number_with_coeff(&allocated_c, minus_one);

        lc.add_assign_boolean_with_coeff(&alloc_of, minus_word_shift);
        lc.enforce_zero(cs).unwrap();

        pre_of = of;
        alloc_pre_of = alloc_of;

    }
    let mut result: Vec<Num<E>> = vec![];
    for i in 0..c_in_limbs.len(){
        let variable: Option<E::Fr>= some_biguint_to_fe(&c_in_limbs[i]);
        result.push(Num::Variable(AllocatedNum::alloc(cs, || Ok(*variable.get().unwrap())).unwrap()));


    }
    Ok(result)

}
pub fn simple_sub<E: Engine, CS: ConstraintSystem<E>>(cs: &mut CS, a: [Num<E>; 4], b:[Num<E>; 4] )->Result<Vec<Num<E>>, SynthesisError>{
    let mut big_big_biguint_a = BigUint::zero();
    let mut big_big_biguint_b = BigUint::zero();
    for i in 0..4{
        let mut v_a = BigUint::zero();
        let mut v_b = BigUint::zero();
        match a[i] {
            Num::Constant(value) => {
                v_a = fe_to_biguint(&value);
            }

            Num::Variable(var) =>{
                enforce_using_single_column_table_for_shifted_variable_optimized(cs, &var, E::Fr::one(), 64);
                let mut w = var.get_value().unwrap();
                v_a = fe_to_biguint(&w);
            }
        }
        big_big_biguint_a += v_a * BigUint::from(1u64) << 64u32* (i as u32);
        match b[i] {
            Num::Constant(value) => {
                v_b = fe_to_biguint(&value);
            }

            Num::Variable(var) =>{
                enforce_using_single_column_table_for_shifted_variable_optimized(cs, &var, E::Fr::one(), 64);
                let mut w = var.get_value().unwrap();
                v_b = fe_to_biguint(&w);
            }
        }
        big_big_biguint_b += v_b * BigUint::from(1u64) << 64u32* (i as u32);
    }
    
    let a_in_limbs = split_some_into_fixed_number_of_limbs(Some(big_big_biguint_a), 64, 4 );
    let b_in_limbs = split_some_into_fixed_number_of_limbs(Some(big_big_biguint_b), 64, 4 );

    let mut c_in_limbs: Vec<Option<BigUint>> = vec![];
    let mut borrow = Some(BigUint::zero());
    let mut pre_borrow = Some(BigUint::zero());
    let mut alloc_pre_borrow = Boolean::zero();
    for (l, r) in a_in_limbs.into_iter().zip(b_in_limbs.into_iter()) {

        let fe_a =  some_biguint_to_fe::<E::Fr>(&l);
        let fe_b =  some_biguint_to_fe::<E::Fr>(&r);
        let allocated_a = Num::Variable(AllocatedNum::alloc(cs, || Ok(*fe_a.get()?)).unwrap());
        let allocated_b = Num::Variable(AllocatedNum::alloc(cs, || Ok(*fe_b.get()?)).unwrap());

        let mut new_limb = BigUint::from(0u64);
        
        if l.clone().unwrap() - pre_borrow.clone().unwrap() < r.clone().unwrap() {
            new_limb = l.as_ref().unwrap()+ (BigUint::from(1u64) << 64u32) - r.as_ref().unwrap()- pre_borrow.as_ref().unwrap();
            borrow = Some(BigUint::from(1u64));
            c_in_limbs.push(Some(new_limb.clone()));
        }
        else{
            borrow = Some(BigUint::zero());
            new_limb = l.as_ref().unwrap() - r.as_ref().unwrap()- pre_borrow.as_ref().unwrap();
            c_in_limbs.push(Some(new_limb.clone()));
        }

        let intermediate_of_witness = Some(!borrow.clone().as_ref().unwrap().is_zero());

        let alloc_borrow = Boolean::from(
            AllocatedBit::alloc(cs, intermediate_of_witness).unwrap()
        );
        
        let fe_c =  some_biguint_to_fe::<E::Fr>(&Some(new_limb.clone()));
        let allc_num = AllocatedNum::alloc(cs, || Ok(*fe_c.get()?)).unwrap();
        let allocated_c = Num::Variable(allc_num);
        enforce_using_single_column_table_for_shifted_variable_optimized(cs, &allc_num, E::Fr::one(), 64);


        let shifts = compute_shifts::<E::Fr>();
        let mut minus_one = E::Fr::one();
        minus_one.negate();
    
        let mut word_shift = shifts[64].clone();
        let mut minus_word_shift = word_shift;
        minus_word_shift.negate();

        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&allocated_a, E::Fr::one());
        lc.add_assign_number_with_coeff(&allocated_b, minus_one);
        lc.add_assign_boolean_with_coeff(&alloc_pre_borrow, minus_one);
        lc.add_assign_number_with_coeff(&allocated_c, minus_one);

        lc.add_assign_boolean_with_coeff(&alloc_borrow, word_shift);
        lc.enforce_zero(cs).unwrap();

        pre_borrow = borrow.clone();
        alloc_pre_borrow = alloc_borrow;

    }
    let mut result: Vec<Num<E>> = vec![];
    for i in 0..c_in_limbs.len(){
        let variable: Option<E::Fr>= some_biguint_to_fe(&c_in_limbs[i]);
        result.push(Num::Variable(AllocatedNum::alloc(cs, || Ok(*variable.get().unwrap())).unwrap()));


    }
    Ok(result)

}
pub fn simple_mul<E: Engine, CS: ConstraintSystem<E>>(cs: &mut CS, a: [Num<E>; 4], b:[Num<E>; 4] )->Result<Vec<Num<E>>, SynthesisError>{
    let mut big_big_biguint_a = BigUint::zero();
    let mut big_big_biguint_b = BigUint::zero();
    for i in 0..4{
        let mut v_a = BigUint::zero();
        let mut v_b = BigUint::zero();
        match a[i] {
            Num::Constant(value) => {
                v_a = fe_to_biguint(&value);
            }

            Num::Variable(var) =>{
                enforce_using_single_column_table_for_shifted_variable_optimized(cs, &var, E::Fr::one(), 64);
                let w = var.get_value().unwrap();
                v_a = fe_to_biguint(&w);
            }
        }
        big_big_biguint_a += v_a * BigUint::from(1u64) << 64u32* (i as u32);
        match b[i] {
            Num::Constant(value) => {
                v_b = fe_to_biguint(&value);
            }

            Num::Variable(var) =>{
                enforce_using_single_column_table_for_shifted_variable_optimized(cs, &var, E::Fr::one(), 64);
                let w = var.get_value().unwrap();
                v_b = fe_to_biguint(&w);
            }
        }
        big_big_biguint_b += v_b * BigUint::from(1u64) << 64u32* (i as u32);
    }
    let big_big_biguint_c = big_big_biguint_a.clone() * big_big_biguint_b.clone();
    
    // split into one number
    let four_chunk = split_some_into_fixed_number_of_limbs(Some(big_big_biguint_c.clone()), 128, 4);
    // println!("four_chunk{:?}", four_chunk);
    let mut number_num: Vec<Num<E>> = vec![];
    for i in 0..four_chunk.len(){
        let variable: Option<E::Fr>= some_biguint_to_fe(&four_chunk[i]);
        number_num.push(Num::Variable(AllocatedNum::alloc(cs, || Ok(*variable.get().unwrap())).unwrap()));
    
    }

    let a_in_limbs = split_some_into_fixed_number_of_limbs(Some(big_big_biguint_a), 64, 4 );
    let b_in_limbs = split_some_into_fixed_number_of_limbs(Some(big_big_biguint_b), 64, 4 );

    let shifts = compute_shifts::<E::Fr>();
    let mut minus_one = E::Fr::one();
    minus_one.negate();

    let word_shift = shifts[64].clone();
    let two_words_shift = shifts[128].clone();
    let two_words_shift_right = two_words_shift.inverse().unwrap();

    let mut c_in_limbs: Vec<Option<BigUint>> = vec![];
    let mut of = Some(BigUint::zero());
    let mut pre_of = Some(BigUint::zero());
    const NUM_LIMBS_IN_MULTIPLIERS : usize = 4;
    let mut input_carry = Num::<E>::zero();
    for k in 0..4{
        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&input_carry, E::Fr::one()); // pre_of 
        
        let mut mul_term = BigUint::zero();
        let mut mul_term_1 = BigUint::zero();
        let mut mul_term_1_num = Num::<E>::zero();
        let mut mul_term_2 = BigUint::zero();
        let mut mul_term_2_num = Num::<E>::zero();
        for i in 0..2*k + 1 {
            let j = 2*k - i;

            if (i < NUM_LIMBS_IN_MULTIPLIERS) && (j < NUM_LIMBS_IN_MULTIPLIERS) {
                let fe_a = some_biguint_to_fe::<E::Fr>(&a_in_limbs[i].clone());
                let allc_num_a = AllocatedNum::alloc(cs, || Ok(*fe_a.get()?)).unwrap();
                let chunk_a_num = Num::Variable(allc_num_a);
                let fe_b = some_biguint_to_fe::<E::Fr>(&b_in_limbs[j].clone());
                let allc_num_b = AllocatedNum::alloc(cs, || Ok(*fe_b.get()?)).unwrap();
                let chunk_b_num = Num::Variable(allc_num_b);

                mul_term_1_num = chunk_a_num.mul(cs, &chunk_b_num)?;
                lc.add_assign_number_with_coeff(&mul_term_1_num, E::Fr::one());

                mul_term_1 = a_in_limbs[i].clone().unwrap() * b_in_limbs[j].clone().unwrap();
                mul_term += mul_term_1.clone();
            }
        }
        for i in 0..(2*k+2) {
            let j = 2*k + 1 - i;

            if (i < NUM_LIMBS_IN_MULTIPLIERS) && (j < NUM_LIMBS_IN_MULTIPLIERS) {
                let fe_a = some_biguint_to_fe::<E::Fr>(&a_in_limbs[i].clone());
                let allc_num_a = AllocatedNum::alloc(cs, || Ok(*fe_a.get()?)).unwrap();
                let chunk_a_num = Num::Variable(allc_num_a);
                let fe_b = some_biguint_to_fe::<E::Fr>(&b_in_limbs[j].clone());
                let allc_num_b = AllocatedNum::alloc(cs, || Ok(*fe_b.get()?)).unwrap();
                let chunk_b_num = Num::Variable(allc_num_b);

                mul_term_2_num = chunk_a_num.mul(cs, &chunk_b_num)?;
                lc.add_assign_number_with_coeff(&mul_term_2_num, word_shift.clone());


                mul_term_2 = a_in_limbs[i].clone().unwrap() * b_in_limbs[j].clone().unwrap();
                mul_term += mul_term_2.clone() * (BigUint::from(1u64) << 64u32);
            }
        }
        // lc.scale(&two_words_shift_right);
        mul_term +=pre_of.clone().unwrap();

        let modulus = BigUint::from(1u64) << 128u32;
        of = Some((mul_term.clone() % modulus) >> 128u8);
        let fe_of =  some_biguint_to_fe::<E::Fr>(&of);
        let allc_num = AllocatedNum::alloc(cs, || Ok(*fe_of.get()?)).unwrap();
        let allocated_of = Num::Variable(allc_num);
        enforce_using_single_column_table_for_shifted_variable_optimized(cs, &allc_num, E::Fr::one(), 75);
        lc.add_assign_number_with_coeff(&allocated_of, two_words_shift_right.clone());

        let mut limbs_for_c= BigUint::zero();
        let shift = BigUint::from(1u64) << 128u32;
        limbs_for_c = mul_term.clone() - of.as_ref().unwrap()*shift;
        c_in_limbs.push(Some(limbs_for_c.clone()));

        let fe_c =  some_biguint_to_fe::<E::Fr>(&Some(limbs_for_c));
        let allc_num = AllocatedNum::alloc(cs, || Ok(*fe_c.get()?)).unwrap();
        let allocated_c = Num::Variable(allc_num);
        lc.add_assign_number_with_coeff(&allocated_c, minus_one.clone());
        enforce_using_single_column_table_for_shifted_variable_optimized(cs, &allc_num, E::Fr::one(), 128);
        lc.enforce_zero(cs)?;
        
        pre_of = of.clone();
        input_carry = allocated_of;

    }
    // println!("four_chunk{:?}", four_chunk);
    // println!("c_in_limbs{:?}", c_in_limbs);

    // split into one number
    let mut number = BigUint::zero();
    for i in 0..c_in_limbs.len(){
        let step = BigUint::from(1u64) << 128u32 * (i as u32);
        number += c_in_limbs[i].as_ref().unwrap() * step;

    }

    let four_chunk = split_some_into_fixed_number_of_limbs(Some(number.clone()), 128, 4);
    let mut number_num: Vec<Num<E>> = vec![];
    for i in 0..four_chunk.len(){
        let variable: Option<E::Fr>= some_biguint_to_fe(&four_chunk[i]);
        number_num.push(Num::Variable(AllocatedNum::alloc(cs, || Ok(*variable.get().unwrap())).unwrap()));

    }

    use std::str::FromStr;
    let field_modulus = BigUint::from_str("21888242871839275222246405745257275088696311157297823662689037894645226208583").unwrap();
    let result_uint = number.clone() % field_modulus.clone();

    let remainder_uint = split_some_into_fixed_number_of_limbs(Some(result_uint.clone()), 128, 2);
    let mut result: Vec<Num<E>> = vec![];
    for i in 0..remainder_uint.len(){
        let variable: Option<E::Fr>= some_biguint_to_fe(&remainder_uint[i]);
        let r = AllocatedNum::alloc(cs, || Ok(*variable.get().unwrap())).unwrap();
        result.push(Num::Variable(r));
        enforce_using_single_column_table_for_shifted_variable_optimized(cs, &r, E::Fr::one(), 128);

    }

    use num_integer::Integer;
    // c = q*p +r; 
    //a/b = q and a%b = r
    let (quotient, remainder) = number.div_rem(&field_modulus);
    assert_eq!(remainder.clone(), result_uint.clone());

    let field_chunk = split_some_into_fixed_number_of_limbs(Some(field_modulus), 64, 4);
    let mut field_mod_num:Vec<Num<E>> = vec![]; 
    for i in 0..field_chunk.len(){
        let variable: Option<E::Fr>= some_biguint_to_fe(&field_chunk[i]);
        let m = AllocatedNum::alloc(cs, || Ok(*variable.get().unwrap())).unwrap();
        field_mod_num.push(Num::Variable(m));
    }

    let quotient_chunk = split_some_into_fixed_number_of_limbs(Some(quotient), 64, 4);
    let mut quotient_num:Vec<Num<E>> = vec![]; 
    for i in 0..quotient_chunk.len(){
        let variable: Option<E::Fr>= some_biguint_to_fe(&quotient_chunk[i]);
        let m =AllocatedNum::alloc(cs, || Ok(*variable.get().unwrap())).unwrap();
        quotient_num.push(Num::Variable(m));
        enforce_using_single_column_table_for_shifted_variable_optimized(cs, &m, E::Fr::one(), 64);
    }

    let mut of = Some(BigUint::zero());
    let mut pre_of = Some(BigUint::zero());
    let mut input_carry = Num::<E>::zero();
    let mut c_in_limbs: Vec<Option<BigUint>> = vec![];
    for k in 0..4{
        let mut lc = LinearCombination::zero();

        let mut mul_term_uint = BigUint::zero();
        let mut mul_term_1 = BigUint::zero();
        let mut mul_term_2 = BigUint::zero();

        lc.add_assign_number_with_coeff(&input_carry, E::Fr::one()); // pre_of 
        for i in 0..2*k + 1 {
            let j = 2*k - i;
            if (i < 4) && (j < 4) {
                let mul_term = field_mod_num[i].mul(cs, &quotient_num[j])?;
                lc.add_assign_number_with_coeff(&mul_term, E::Fr::one());

                mul_term_1 = quotient_chunk[i].clone().unwrap() * field_chunk[j].clone().unwrap();
                mul_term_uint += mul_term_1.clone();
            }

        }
    
        for i in 0..(2*k+2) {
            let j = 2*k + 1 - i;
            if (i < 4) && (j < 4) {
                let mul_term = field_mod_num[i].mul(cs, &quotient_num[j])?;
                lc.add_assign_number_with_coeff(&mul_term, shifts[64].clone());

                mul_term_2 = quotient_chunk[i].clone().unwrap() * field_chunk[j].clone().unwrap();
                mul_term_uint += mul_term_2.clone() * (BigUint::from(1u64) << 64u32);
            }
        }
        if k < 2 {
            lc.add_assign_number_with_coeff(&result[k], E::Fr::one());//remainder

            mul_term_uint +=pre_of.clone().unwrap() + remainder_uint[k].clone().unwrap();
        }

        let modulus = BigUint::from(1u64) << 128u32;
        of = Some((mul_term_uint.clone() % modulus) >> 128u8);
        let fe_of =  some_biguint_to_fe::<E::Fr>(&of);
        let allc_num = AllocatedNum::alloc(cs, || Ok(*fe_of.get()?)).unwrap();
        let allocated_of = Num::Variable(allc_num);
        enforce_using_single_column_table_for_shifted_variable_optimized(cs, &allc_num, E::Fr::one(), 75);
        lc.add_assign_number_with_coeff(&allocated_of, two_words_shift_right.clone());

        let intermediate_of_witness = Some(!of.as_ref().unwrap().is_zero());

        let mut limbs_for_c= BigUint::zero();
        if intermediate_of_witness.unwrap() {
            let shift = BigUint::from(1u64) << 128u32;
            limbs_for_c = mul_term_uint.clone() - of.as_ref().unwrap()*shift;
            c_in_limbs.push(Some(limbs_for_c.clone()));
        }
        else{
            limbs_for_c = mul_term_uint.clone();
            c_in_limbs.push(Some(mul_term_uint));
        }
        let fe_c =  some_biguint_to_fe::<E::Fr>(&Some(limbs_for_c));
        let allc_num = AllocatedNum::alloc(cs, || Ok(*fe_c.get()?)).unwrap();
        let allocated_c = Num::Variable(allc_num);
        lc.add_assign_number_with_coeff(&allocated_c, minus_one.clone());
        enforce_using_single_column_table_for_shifted_variable_optimized(cs, &allc_num, E::Fr::one(), 128);


        lc.enforce_zero(cs)?;
        
        pre_of = of;
        input_carry = allocated_of;

    }

    Ok(result)

}
pub fn more_simple_mul<E: Engine, CS: ConstraintSystem<E>>(cs: &mut CS, a: [Num<E>; 4], b:[Num<E>; 4] )->Result<Vec<Num<E>>, SynthesisError>{
    // converting a [Num<E>; 4] to type BigUint
    let mut big_big_biguint_a = BigUint::zero();
    let mut big_big_biguint_b = BigUint::zero();
    for i in 0..4{
        let mut v_a = BigUint::zero();
        let mut v_b = BigUint::zero();
        match a[i] {
            Num::Constant(value) => {
                v_a = fe_to_biguint(&value);
            }

            Num::Variable(var) =>{
                enforce_using_single_column_table_for_shifted_variable_optimized(cs, &var, E::Fr::one(), 64);
                let w = var.get_value().unwrap();
                v_a = fe_to_biguint(&w);
            }
        }
        big_big_biguint_a += v_a * BigUint::from(1u64) << 64u32* (i as u32);
        match b[i] {
            Num::Constant(value) => {
                v_b = fe_to_biguint(&value);
            }

            Num::Variable(var) =>{
                enforce_using_single_column_table_for_shifted_variable_optimized(cs, &var, E::Fr::one(), 64);
                let w = var.get_value().unwrap();
                v_b = fe_to_biguint(&w);
            }
        }
        big_big_biguint_b += v_b * BigUint::from(1u64) << 64u32* (i as u32);
    }

    let a_in_limbs = split_some_into_fixed_number_of_limbs(Some(big_big_biguint_a.clone()), 64, 4 );
    let mut a_num: Vec<Num<E>> = vec![];
    for i in 0..a_in_limbs.len(){
        let variable: Option<E::Fr>= some_biguint_to_fe(&a_in_limbs[i]);
        a_num.push(Num::Variable(AllocatedNum::alloc(cs, || Ok(*variable.get().unwrap())).unwrap()));
    
    }
    let b_in_limbs = split_some_into_fixed_number_of_limbs(Some(big_big_biguint_b.clone()), 64, 4 );
    let mut b_num: Vec<Num<E>> = vec![];
    for i in 0..b_in_limbs.len(){
        let variable: Option<E::Fr>= some_biguint_to_fe(&b_in_limbs[i]);
        b_num.push(Num::Variable(AllocatedNum::alloc(cs, || Ok(*variable.get().unwrap())).unwrap()));
    
    }

    let big_big_biguint_c = big_big_biguint_a.clone() * big_big_biguint_b.clone();
    // split into one number
    let four_chunk = split_some_into_fixed_number_of_limbs(Some(big_big_biguint_c.clone()), 128, 4);
    println!("optomizm{:?}", four_chunk);
    let mut number_num: Vec<Num<E>> = vec![];
    for i in 0..four_chunk.len(){
        let variable: Option<E::Fr>= some_biguint_to_fe(&four_chunk[i]);
        number_num.push(Num::Variable(AllocatedNum::alloc(cs, || Ok(*variable.get().unwrap())).unwrap()));
    
    }
    
    use std::str::FromStr;
    use num_integer::Integer;

    // c = q*p +r; 
    //a/b = q and a%b = r
    let field_modulus = BigUint::from_str("21888242871839275222246405745257275088696311157297823662689037894645226208583").unwrap();
    let (quotient, remainder) = big_big_biguint_c.div_rem(&field_modulus);

    //remainder to limbs
    let remainder_uint = split_some_into_fixed_number_of_limbs(Some(remainder.clone()), 128, 2);
    let mut result: Vec<Num<E>> = vec![];
    for i in 0..remainder_uint.len(){
        let variable: Option<E::Fr>= some_biguint_to_fe(&remainder_uint[i]);
        let r = AllocatedNum::alloc(cs, || Ok(*variable.get().unwrap())).unwrap();
        result.push(Num::Variable(r));
        enforce_using_single_column_table_for_shifted_variable_optimized(cs, &r, E::Fr::one(), 128);
    
    }

    //field parametr to limbs
    let field_chunk = split_some_into_fixed_number_of_limbs(Some(field_modulus), 64, 4);
    let mut field_mod_num:Vec<Num<E>> = vec![]; 
    for i in 0..field_chunk.len(){
        let variable: Option<E::Fr>= some_biguint_to_fe(&field_chunk[i]);
        let m = AllocatedNum::alloc(cs, || Ok(*variable.get().unwrap())).unwrap();
        field_mod_num.push(Num::Variable(m));
    }

    //quotient to limbs
    let quotient_chunk = split_some_into_fixed_number_of_limbs(Some(quotient), 64, 4);
    let mut quotient_num:Vec<Num<E>> = vec![]; 
    for i in 0..quotient_chunk.len(){
        let variable: Option<E::Fr>= some_biguint_to_fe(&quotient_chunk[i]);
        let m =AllocatedNum::alloc(cs, || Ok(*variable.get().unwrap())).unwrap();
        quotient_num.push(Num::Variable(m));
        enforce_using_single_column_table_for_shifted_variable_optimized(cs, &m, E::Fr::one(), 64);
    }

    let shifts = compute_shifts::<E::Fr>();
    let mut minus_one = E::Fr::one();
    minus_one.negate();

    let word_shift = shifts[64].clone();
    let words_shift_right = word_shift.inverse().unwrap();
    let two_words_shift = shifts[128].clone();
    let two_words_shift_right = two_words_shift.inverse().unwrap();

    let mut c_in_limbs: Vec<Option<BigUint>> = vec![];
    let mut c_in_limbs_another: Vec<Option<BigUint>> = vec![];
    let mut of = Some(BigUint::zero());
    let mut pre_of = Some(BigUint::zero());
    const NUM_LIMBS_IN_MULTIPLIERS : usize = 4;
    let mut input_carry = Num::<E>::zero();

    let mut of_another = Some(BigUint::zero());
    let mut pre_of_another = Some(BigUint::zero());
    let mut input_carry_another = Num::<E>::zero();

    //of_another + a*b + pre_of = p*q + r + of + pre_of_another;

    for k in 0..4{
        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&input_carry, E::Fr::one()); // pre_of 
        lc.add_assign_number_with_coeff(&input_carry_another, minus_one); // pre_of_another
        
        let mut mul_term = BigUint::zero();
        let mut mul_term_1 = BigUint::zero();
        let mut mul_term_2 = BigUint::zero();

        let mut mul_another = BigUint::zero();
        let mut mul_term_1_another = BigUint::zero();
        let mut mul_term_2_another = BigUint::zero();
        for i in 0..2*k + 1 {
            let j = 2*k - i;

            if (i < NUM_LIMBS_IN_MULTIPLIERS) && (j < NUM_LIMBS_IN_MULTIPLIERS) {

                let mul_term_1_num = a_num[i].mul(cs, &b_num[j])?;
                lc.add_assign_number_with_coeff(&mul_term_1_num, E::Fr::one());

                let whole_part = field_mod_num[i].mul(cs, &quotient_num[j])?;
                lc.add_assign_number_with_coeff(&whole_part, minus_one); 

                mul_term_1 = a_in_limbs[i].clone().unwrap() * b_in_limbs[j].clone().unwrap();
                mul_term += mul_term_1.clone();

                mul_term_1_another = field_chunk[i].clone().unwrap() * quotient_chunk[j].clone().unwrap();
                mul_another += mul_term_1_another.clone();
            }
        }
        for i in 0..(2*k+2) {
            let j = 2*k + 1 - i;

            if (i < NUM_LIMBS_IN_MULTIPLIERS) && (j < NUM_LIMBS_IN_MULTIPLIERS) {

                let mul_term_2_num = a_num[i].mul(cs, &b_num[j])?;
                lc.add_assign_number_with_coeff(&mul_term_2_num, word_shift.clone());

                let whole_part_2 = field_mod_num[i].mul(cs, &quotient_num[j])?;
                lc.add_assign_number_with_coeff(&whole_part_2, words_shift_right.clone()); // !!!!! coeff


                mul_term_2 = a_in_limbs[i].clone().unwrap() * b_in_limbs[j].clone().unwrap();
                mul_term += mul_term_2.clone() * (BigUint::from(1u64) << 64u32);

                mul_term_2_another = field_chunk[i].clone().unwrap() * quotient_chunk[j].clone().unwrap();
                mul_another += mul_term_2_another.clone() * (BigUint::from(1u64) << 64u32);
            }
        }
        if k < 2 {
            lc.add_assign_number_with_coeff(&result[k], minus_one.clone());//remainder part of 2

        }

        mul_term +=pre_of.clone().unwrap();
        mul_another += pre_of_another.clone().unwrap();

        let modulus = BigUint::from(1u64) << 128u32;
        of_another = Some((mul_another.clone() % modulus) >> 128u8);
        let fe_of_another =  some_biguint_to_fe::<E::Fr>(&of_another);
        let allc_num_another = AllocatedNum::alloc(cs, || Ok(*fe_of_another.get()?)).unwrap();
        let allocated_of_another = Num::Variable(allc_num_another);
        enforce_using_single_column_table_for_shifted_variable_optimized(cs, &allc_num_another, E::Fr::one(), 75);
        lc.add_assign_number_with_coeff(&allocated_of_another, two_words_shift.clone());

        let intermediate_of_witness_another = Some(!of_another.as_ref().unwrap().is_zero());

        let mut limbs_for_c_another= BigUint::zero();
        if intermediate_of_witness_another.unwrap() {
            let shift = BigUint::from(1u64) << 128u32;
            limbs_for_c_another = mul_another.clone() - of_another.as_ref().unwrap()*shift;
            c_in_limbs_another.push(Some(limbs_for_c_another.clone()));
        }
        else{
            limbs_for_c_another = mul_another.clone();
            c_in_limbs_another.push(Some(mul_another));
        }
        println!("test_1{:?}", c_in_limbs_another);
        // let fe_c_another =  some_biguint_to_fe::<E::Fr>(&Some(limbs_for_c_another));
        // let allc_num_another = AllocatedNum::alloc(cs, || Ok(*fe_c_another.get()?)).unwrap();
        // let allocated_c_another = Num::Variable(allc_num_another);
        // lc.add_assign_number_with_coeff(&allocated_c_another, minus_one.clone());
        // enforce_using_single_column_table_for_shifted_variable_optimized(cs, &allc_num_another, E::Fr::one(), 128);
        
        pre_of_another = of_another;
        input_carry_another = allocated_of_another;





        let modulus = BigUint::from(1u64) << 128u32;
        of = Some((mul_term.clone() % modulus) >> 128u8);
        let fe_of =  some_biguint_to_fe::<E::Fr>(&of);
        let allc_num = AllocatedNum::alloc(cs, || Ok(*fe_of.get()?)).unwrap();
        let allocated_of = Num::Variable(allc_num);
        enforce_using_single_column_table_for_shifted_variable_optimized(cs, &allc_num, E::Fr::one(), 75);
        lc.add_assign_number_with_coeff(&allocated_of, two_words_shift_right.clone());

        let intermediate_of_witness = Some(!of.as_ref().unwrap().is_zero());

        let mut limbs_for_c= BigUint::zero();
        if intermediate_of_witness.unwrap() {
            let shift = BigUint::from(1u64) << 128u32;
            limbs_for_c = mul_term.clone() - of.as_ref().unwrap()*shift;
            c_in_limbs.push(Some(limbs_for_c.clone()));
        }
        else{
            limbs_for_c = mul_term.clone();
            c_in_limbs.push(Some(mul_term));
        }
        println!("test_2{:?}", c_in_limbs);

        let fe_c =  some_biguint_to_fe::<E::Fr>(&Some(limbs_for_c));
        let allc_num = AllocatedNum::alloc(cs, || Ok(*fe_c.get()?)).unwrap();
        let allocated_c = Num::Variable(allc_num);
        lc.add_assign_number_with_coeff(&allocated_c, minus_one.clone());
        enforce_using_single_column_table_for_shifted_variable_optimized(cs, &allc_num, E::Fr::one(), 128);
        lc.enforce_zero(cs)?;
        
        pre_of = of.clone();
        input_carry = allocated_of;

        

    }


    Ok(result)

}
pub fn simple_div<E: Engine, CS: ConstraintSystem<E>>(cs: &mut CS, a: [Num<E>; 8], b:[Num<E>; 4] )->Result<Vec<Num<E>>, SynthesisError>{
    let mut big_big_biguint_a = BigUint::zero();
    let mut big_big_biguint_b = BigUint::zero();
    for i in 0..8{
        let mut v_a = BigUint::zero();
        match a[i] {
            Num::Constant(value) => {
                v_a = fe_to_biguint(&value);
            }

            Num::Variable(var) =>{
                enforce_using_single_column_table_for_shifted_variable_optimized(cs, &var, E::Fr::one(), 64);
                let mut w = var.get_value().unwrap();
                v_a = fe_to_biguint(&w);
            }
        }
        big_big_biguint_a += v_a * BigUint::from(1u64) << 64u32* (i as u32);
    }
    for i in 0..4{
        let mut v_b = BigUint::zero();
        match b[i] {
            Num::Constant(value) => {
                v_b = fe_to_biguint(&value);
            }

            Num::Variable(var) =>{
                enforce_using_single_column_table_for_shifted_variable_optimized(cs, &var, E::Fr::one(), 64);
                let mut w = var.get_value().unwrap();
                v_b = fe_to_biguint(&w);
            }
        }
        big_big_biguint_b += v_b * BigUint::from(1u64) << 64u32* (i as u32);
    }
    use num_integer::Integer;
    let (quotient, remainder) = big_big_biguint_a.div_rem(&big_big_biguint_b);

    let quotient_in_limbs = split_some_into_fixed_number_of_limbs(Some(quotient), 64, 8 );
    let mut quotient_in_limbs_num: Vec<Num<E>> = vec![];
    for i in 0..quotient_in_limbs.len(){
        let variable: Option<E::Fr>= some_biguint_to_fe(&quotient_in_limbs[i]);
        quotient_in_limbs_num.push(Num::Variable(AllocatedNum::alloc(cs, || Ok(*variable.get().unwrap())).unwrap()));

    }
    let divisor_in_limbs = split_some_into_fixed_number_of_limbs(Some(big_big_biguint_b), 64, 8 );
    let remainder = split_some_into_fixed_number_of_limbs(Some(remainder), 64, 4 );

    let shifts = compute_shifts::<E::Fr>();
    let mut minus_one = E::Fr::one();
    minus_one.negate();

    let word_shift = shifts[64].clone();
    let two_words_shift = shifts[128].clone();
    let two_words_shift_right = two_words_shift.inverse().unwrap();

    let mut c_in_limbs: Vec<Option<BigUint>> = vec![];
    let mut of = Some(BigUint::zero());
    let mut pre_of = Some(BigUint::zero());
    const NUM_LIMBS_IN_MULTIPLIERS : usize = 8;
    let mut input_carry = Num::<E>::zero();
    for k in 0..8{
        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&input_carry, E::Fr::one()); // pre_of 
        
        let mut mul_term = BigUint::zero();
        let mut mul_term_1 = BigUint::zero();
        let mut mul_term_1_num = Num::<E>::zero();
        let mut mul_term_2 = BigUint::zero();
        let mut mul_term_2_num = Num::<E>::zero();

        for i in 0..2*k + 1 {
            let j = 2*k - i;
            if (i < NUM_LIMBS_IN_MULTIPLIERS) && (j < NUM_LIMBS_IN_MULTIPLIERS) {

                let fe_a = some_biguint_to_fe::<E::Fr>(&quotient_in_limbs[i].clone());
                let allc_num_a = AllocatedNum::alloc(cs, || Ok(*fe_a.get()?)).unwrap();
                let chunk_a_num = Num::Variable(allc_num_a);

                let fe_b = some_biguint_to_fe::<E::Fr>(&divisor_in_limbs[j].clone());
                let allc_num_b = AllocatedNum::alloc(cs, || Ok(*fe_b.get()?)).unwrap();
                let chunk_b_num = Num::Variable(allc_num_b);

                mul_term_1_num = chunk_a_num.mul(cs, &chunk_b_num)?;
                lc.add_assign_number_with_coeff(&mul_term_1_num, E::Fr::one());

                mul_term_1 = quotient_in_limbs[i].clone().unwrap() * divisor_in_limbs[j].clone().unwrap();
                mul_term += mul_term_1.clone();
            }
        }
        for i in 0..(2*k+2) {
            let j = 2*k + 1 - i;
            if (i < NUM_LIMBS_IN_MULTIPLIERS) && (j < NUM_LIMBS_IN_MULTIPLIERS) {

                let fe_a = some_biguint_to_fe::<E::Fr>(&quotient_in_limbs[i].clone());
                let allc_num_a = AllocatedNum::alloc(cs, || Ok(*fe_a.get()?)).unwrap();
                let chunk_a_num = Num::Variable(allc_num_a);

                let fe_b = some_biguint_to_fe::<E::Fr>(&divisor_in_limbs[j].clone());
                let allc_num_b = AllocatedNum::alloc(cs, || Ok(*fe_b.get()?)).unwrap();
                let chunk_b_num = Num::Variable(allc_num_b);

                mul_term_2_num = chunk_a_num.mul(cs, &chunk_b_num)?;
                lc.add_assign_number_with_coeff(&mul_term_2_num, word_shift.clone());


                mul_term_2 = quotient_in_limbs[i].clone().unwrap() * divisor_in_limbs[j].clone().unwrap();
                mul_term += mul_term_2.clone() * (BigUint::from(1u64) << 64u32);
            }
        }

        if k < 4 {
            let fe_remainder = some_biguint_to_fe::<E::Fr>(&remainder[k].clone());
            let allc_num_remainder = AllocatedNum::alloc(cs, || Ok(*fe_remainder.get()?)).unwrap();
            let chunk_remainder_num = Num::Variable(allc_num_remainder);

            lc.add_assign_number_with_coeff(&chunk_remainder_num.clone(), E::Fr::one());
            mul_term +=pre_of.clone().unwrap() + remainder[k].clone().unwrap();
        }
        


        let modulus = BigUint::from(1u64) << 128u32;
        of = Some((mul_term.clone() % modulus) >> 128u8);
        let fe_of =  some_biguint_to_fe::<E::Fr>(&of);
        let allc_num = AllocatedNum::alloc(cs, || Ok(*fe_of.get()?)).unwrap();
        let allocated_of = Num::Variable(allc_num);
        enforce_using_single_column_table_for_shifted_variable_optimized(cs, &allc_num, E::Fr::one(), 75);
        lc.add_assign_number_with_coeff(&allocated_of, two_words_shift_right.clone());

        let intermediate_of_witness = Some(!of.as_ref().unwrap().is_zero());

        let mut limbs_for_c= BigUint::zero();
        if intermediate_of_witness.unwrap() {
            let shift = BigUint::from(1u64) << 128u32;
            limbs_for_c = mul_term.clone() - of.as_ref().unwrap()*shift;
            c_in_limbs.push(Some(limbs_for_c.clone()));
        }
        else{
            limbs_for_c = mul_term.clone();
            c_in_limbs.push(Some(mul_term));
        }
        let fe_c =  some_biguint_to_fe::<E::Fr>(&Some(limbs_for_c));
        let allc_num = AllocatedNum::alloc(cs, || Ok(*fe_c.get()?)).unwrap();
        let allocated_c = Num::Variable(allc_num);
        lc.add_assign_number_with_coeff(&allocated_c, minus_one.clone());
        enforce_using_single_column_table_for_shifted_variable_optimized(cs, &allc_num, E::Fr::one(), 128);


        lc.enforce_zero(cs)?;
        
        pre_of = of;
        input_carry = allocated_of;

    }

    Ok(quotient_in_limbs_num)

}

mod test {
    use super::*;
    use crate::plonk::circuit::*;
    use crate::bellman::pairing::bn256::{Bn256, Fq, Fr};
    #[test]
    fn test_mul_uint(){
        type E = crate::bellman::pairing::bn256::Bn256;
        type Fr = crate::bellman::pairing::bn256::Fr;
        type Fq = crate::bellman::pairing::bn256::Fq;

        use crate::bellman::plonk::better_better_cs::cs::*;

        let mut cs = TrivialAssembly::<
                Bn256,
                PlonkCsWidth4WithNextStepParams,
                Width4MainGateWithDNext,
            >::new();

        let over = vec![
            PolyIdentifier::VariablesPolynomial(0),
            PolyIdentifier::VariablesPolynomial(1),
            PolyIdentifier::VariablesPolynomial(2),
        ];
        let table = LookupTableApplication::<Bn256>::new_range_table_of_width_3(16, over).unwrap();

        cs.add_table(table).unwrap();

        use rand::{Rng, SeedableRng, XorShiftRng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        let a_f: Fr = rng.gen();
        let b_f: Fr = rng.gen();

        let a = [Num::alloc(&mut cs, Some(a_f)).unwrap(), Num::default(), Num::default(), Num::default()];
        let b = [Num::alloc(&mut cs, Some(b_f)).unwrap(), Num::default(), Num::default(), Num::default()];

        // let a = [Num::alloc(&mut cs, Some(Fr::from_str("12").unwrap())).unwrap(), Num::default(), Num::default(), Num::default()];
        // let b = [Num::alloc(&mut cs, Some(Fr::from_str("11").unwrap())).unwrap(), Num::default(), Num::default(), Num::default()];
        // println!("simple_mul{:?}", simple_mul(&mut cs, a, b));
        let result_1 = simple_mul(&mut cs, a, b).unwrap();
        // let result = more_simple_mul(&mut cs, a, b).unwrap();
        let base = cs.n();
        println!("Multiplication taken {} gates", base);

    }
    #[test]
    fn test_div_uint(){
        type E = crate::bellman::pairing::bn256::Bn256;
        type Fr = crate::bellman::pairing::bn256::Fr;
        type Fq = crate::bellman::pairing::bn256::Fq;

        use crate::bellman::plonk::better_better_cs::cs::*;

        let mut cs = TrivialAssembly::<
                Bn256,
                PlonkCsWidth4WithNextStepParams,
                Width4MainGateWithDNext,
            >::new();

        let over = vec![
            PolyIdentifier::VariablesPolynomial(0),
            PolyIdentifier::VariablesPolynomial(1),
            PolyIdentifier::VariablesPolynomial(2),
        ];
        let table = LookupTableApplication::<Bn256>::new_range_table_of_width_3(16, over).unwrap();

        cs.add_table(table).unwrap();

        use rand::{Rng, SeedableRng, XorShiftRng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        let a_f: Fr = rng.gen();
        let b_f: Fr = rng.gen();

        let a = [Num::alloc(&mut cs, Some(a_f)).unwrap(), Num::default(), Num::default(), Num::default(), Num::default(), Num::default(), Num::default(), Num::default()];
        let b = [Num::alloc(&mut cs, Some(b_f)).unwrap(), Num::default(), Num::default(), Num::default()];

        // let a = [Num::alloc(&mut cs, Some(Fr::from_str("132").unwrap())).unwrap(), Num::default(), Num::default(), Num::default(), Num::default(), Num::default(), Num::default(), Num::default()];
        // let b = [Num::alloc(&mut cs, Some(Fr::from_str("11").unwrap())).unwrap(), Num::default(), Num::default(), Num::default()];
        // println!("div{:?}", simple_div(&mut cs, a, b));

        let result = simple_div(&mut cs, a, b).unwrap();
        let base = cs.n();
        println!("Division taken {} gates", base);

    }
    #[test]
    fn test_add_uint(){
        type E = crate::bellman::pairing::bn256::Bn256;
        type Fr = crate::bellman::pairing::bn256::Fr;
        type Fq = crate::bellman::pairing::bn256::Fq;

        use crate::bellman::plonk::better_better_cs::cs::*;

        let mut cs = TrivialAssembly::<
                Bn256,
                PlonkCsWidth4WithNextStepParams,
                Width4MainGateWithDNext,
            >::new();

        let over = vec![
            PolyIdentifier::VariablesPolynomial(0),
            PolyIdentifier::VariablesPolynomial(1),
            PolyIdentifier::VariablesPolynomial(2),
        ];
        let table = LookupTableApplication::<Bn256>::new_range_table_of_width_3(16, over).unwrap();

        cs.add_table(table).unwrap();

        use rand::{Rng, SeedableRng, XorShiftRng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        let a_f: Fr = rng.gen();
        let b_f: Fr = rng.gen();

        let a = [Num::alloc(&mut cs, Some(a_f)).unwrap(), Num::default(), Num::default(), Num::default()];
        let b = [Num::alloc(&mut cs, Some(b_f)).unwrap(), Num::default(), Num::default(), Num::default()];
        let result = simple_add(&mut cs, a, b).unwrap();

        let base = cs.n();
        println!("Addition taken: {} gates", base);
    }

    #[test]
    fn test_sub_uint(){
        type E = crate::bellman::pairing::bn256::Bn256;
        type Fr = crate::bellman::pairing::bn256::Fr;
        type Fq = crate::bellman::pairing::bn256::Fq;

        use crate::bellman::plonk::better_better_cs::cs::*;

        let mut cs = TrivialAssembly::<
                Bn256,
                PlonkCsWidth4WithNextStepParams,
                Width4MainGateWithDNext,
            >::new();

        let over = vec![
            PolyIdentifier::VariablesPolynomial(0),
            PolyIdentifier::VariablesPolynomial(1),
            PolyIdentifier::VariablesPolynomial(2),
        ];
        let table = LookupTableApplication::<Bn256>::new_range_table_of_width_3(16, over).unwrap();

        cs.add_table(table).unwrap();

        use rand::{Rng, SeedableRng, XorShiftRng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        let a_f: Fr = rng.gen();
        let b_f: Fr = rng.gen();


        let a = [Num::alloc(&mut cs, Some(a_f)).unwrap(), Num::default(), Num::default(), Num::default()];
        let b = [Num::alloc(&mut cs, Some(b_f)).unwrap(), Num::default(), Num::default(), Num::default()];
        let result = simple_sub(&mut cs, a, b).unwrap();
        let base = cs.n();
        println!("Substraction taken {} gates", base);



    }



}
