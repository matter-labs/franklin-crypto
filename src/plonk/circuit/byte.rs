use crate::bellman::pairing::ff::*;
use crate::bellman::pairing::*;
use crate::bellman::SynthesisError;
use crate::plonk::circuit::bigint::{split_into_slices, split_some_into_slices};
use crate::plonk::circuit::bigint::constraint_num_bits;
use super::allocated_num::*;
use super::linear_combination::*;
use super::boolean::Boolean;
use super::utils::*;
use crate::circuit::Assignment;

use crate::bellman::plonk::better_better_cs::cs::{
    Variable, 
    ConstraintSystem,
    ArithmeticTerm,
    MainGateTerm
};

#[derive(Clone, Debug)]
pub struct Byte<E: Engine> {
    pub inner: Num<E>
}

impl<E: Engine> Copy for Byte<E> {}

impl<E: Engine> Byte<E> {
    pub fn empty() -> Self {
        Self {
            inner: Num::Constant(E::Fr::zero())
        }
    }

    pub fn into_num(&self) -> Num<E> {
        self.inner.clone()
    }

    pub fn get_value(&self) -> Option<E::Fr> {
        self.inner.get_value()
    }

    pub fn get_byte_value(&self) -> Option<u8> {
        if let Some(v) = self.get_value() {
            let repr = v.into_repr();
            let bits = repr.num_bits();
            assert!(bits <= 8);
            let byte = repr.as_ref()[0] as u8;

            Some(byte)
        } else {
            None
        }
    }
    
    pub fn from_u8_witness<CS: ConstraintSystem<E>>(cs: &mut CS, value: Option<u8>) -> Result<Self, SynthesisError> {
        let var = AllocatedNum::alloc(
            cs,
            || {
                let as_u8 = *value.get()?;
                let fe = u64_to_fe(as_u8 as u64);

                Ok(fe)
            }
        )?;
        let num = Num::Variable(var);
        constraint_num_bits(cs, &num, 8)?;

        Ok(
            Self {
                inner: num
            }
        )
    }

    pub fn from_num<CS: ConstraintSystem<E>>(cs: &mut CS, value: Num<E>) -> Result<Self, SynthesisError> {
        constraint_num_bits(cs, &value, 8)?;
        
        Ok(
            Self {
                inner: value
            }
        )
    }

    pub fn from_num_unconstrained<CS: ConstraintSystem<E>>(_cs: &mut CS, value: Num<E>) -> Self {
        Self {
            inner: value
        }
    }

    pub fn from_cnst<CS: ConstraintSystem<E>>(_cs: &mut CS, value: E::Fr) -> Self {
        let bits = value.into_repr().num_bits();
        if bits > 8 {
            panic!("Invalid bit length of Byte constant");
        }
        Self {
            inner : Num::Constant(value)
        }
    }

    pub fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        flag: &Boolean,
        a: &Self,
        b: &Self
    ) -> Result<Self, SynthesisError> {
        let new_inner = Num::conditionally_select(cs, flag, &a.inner, &b.inner)?;
        let new = Self {
            inner : new_inner
        };

        Ok(new)
    }
}

pub trait IntoBytes<E: Engine>: Send + Sync {
    fn into_le_bytes<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Vec<Byte<E>>, SynthesisError>;
    fn into_be_bytes<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Vec<Byte<E>>, SynthesisError>;
}

pub fn uniquely_encode_le_bytes_into_num<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    bytes: &[Byte<E>],
) -> Result<Num<E>, SynthesisError> {
    assert!(bytes.len() <= (E::Fr::CAPACITY / 8) as usize);
    let mut lc = LinearCombination::zero();
    let mut coeff = E::Fr::one();
    let shift = E::Fr::from_str("256").unwrap();
    // first byte goes into the lowest bits
    for b in bytes.iter() {
        lc.add_assign_number_with_coeff(&b.into_num(), coeff);
        coeff.mul_assign(&shift);
    }

    let result = lc.into_num(cs)?;

    Ok(result)
}

pub fn uniquely_encode_be_bytes_into_num<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    bytes: &[Byte<E>],
) -> Result<Num<E>, SynthesisError> {
    assert!(bytes.len() <= (E::Fr::CAPACITY / 8) as usize);
    let mut lc = LinearCombination::zero();
    let mut coeff = E::Fr::one();
    let shift = E::Fr::from_str("256").unwrap();
    // last byte goes into the lowest bits
    for b in bytes.iter().rev() {
        lc.add_assign_number_with_coeff(&b.into_num(), coeff);
        coeff.mul_assign(&shift);
    }

    let result = lc.into_num(cs)?;

    Ok(result)
}

pub fn uniquely_encode_be_bytes<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    bytes: &[Byte<E>],
) -> Result<Vec<Num<E>>, SynthesisError> {
    let max_chunk = (E::Fr::CAPACITY / 8) as usize;
    let shift = E::Fr::from_str("256").unwrap();

    let mut results = vec![];
    let mut tmp = bytes.to_vec();
    tmp.reverse();
    for chunk in tmp.chunks(max_chunk) {
        let mut coeff = E::Fr::one();
        let mut lc = LinearCombination::zero();
        // last byte goes into the lowest bits
        for b in chunk.iter() {
            lc.add_assign_number_with_coeff(&b.into_num(), coeff);
            coeff.mul_assign(&shift);
        }

        let result = lc.into_num(cs)?;

        results.push(result);
    }
    
    Ok(results)
}


pub fn uniquely_encode_be_bytes_to_field_elements<F: PrimeField>(
    bytes: &[u8],
) -> Vec<F> {
    let max_chunk = (F::CAPACITY / 8) as usize;
    let shift = F::from_str("256").unwrap();

    let mut results = vec![];
    let mut tmp = bytes.to_vec();
    tmp.reverse();
    for chunk in tmp.chunks(max_chunk) {
        let mut result = F::zero();
        let mut coeff = F::one();
        for &b in chunk.iter() {
            let mut b = u64_to_fe::<F>(b as u64);
            b.mul_assign(&coeff);
            result.add_assign(&b);

            coeff.mul_assign(&shift);
        }

        results.push(result);
    }
    
    results
}

impl<E: Engine> IntoBytes<E> for Num<E> {
    fn into_le_bytes<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Vec<Byte<E>>, SynthesisError> {
        let mut num_bytes = (E::Fr::NUM_BITS / 8) as usize;
        if E::Fr::NUM_BITS % 8 != 0 {
            num_bytes += 1;
        }

        let result = match self {
            Num::Variable(ref var) => {
                let mut minus_one = E::Fr::one();
                minus_one.negate();
                let factor = E::Fr::from_str("256").unwrap();
                let mut coeff = E::Fr::one();
                let mut result = Vec::with_capacity(num_bytes);
                let mut lc = LinearCombination::zero();
                lc.add_assign_number_with_coeff(&self, minus_one);
                let witness = split_some_into_slices(var.get_value(), 8, num_bytes);
                for w in witness.into_iter() {
                    let allocated = AllocatedNum::alloc(
                        cs,
                        || {
                            Ok(*w.get()?)
                        }
                    )?;
                    let num = Num::Variable(allocated);
                    let byte = Byte::from_num(cs, num.clone())?;
                    result.push(byte);

                    lc.add_assign_number_with_coeff(&num, coeff);
                    coeff.mul_assign(&factor);
                }

                lc.enforce_zero(cs)?;

                result
            },
            Num::Constant(constant) => {
                let mut result = Vec::with_capacity(num_bytes);
                let witness = split_into_slices(constant, 8, num_bytes);
                for w in witness.into_iter() {
                    let num = Num::Constant(w);
                    let byte = Byte::from_num(cs, num)?;
                    result.push(byte);
                }

                result
            }
        };
        
        Ok(result)
    }

    fn into_be_bytes<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Vec<Byte<E>>, SynthesisError> {
        let mut tmp = self.into_le_bytes(cs)?;
        tmp.reverse();

        Ok(tmp)
    }
}