use super::boolean::AllocatedBit;
use super::boolean::Boolean;
use super::num::AllocatedNum;
use super::num::Num;
use bellman::pairing::ff::PrimeFieldRepr;
use bellman::pairing::ff::{BitIterator, Field, PrimeField};
use bellman::pairing::Engine;
use bellman::{ConstraintSystem, LinearCombination, Namespace, SynthesisError};
use circuit::boolean;
use circuit::Assignment;
use std::ops::{Add, Sub};
use circuit::uint32::UInt32;
use circuit::sha256::sha256;
use circuit::expression::Expression;

const WIDTH: usize = 32;

pub struct Array<E: Engine> {
    values: Vec<Option<E::Fr>>,
}

fn tree_height(size: usize) -> usize {
    let mut height = 0;
    let mut n = size;
    while n > 1 {
        n /= 2;
        height += 1;
    }

    if size > (1 << height) {
        height += 1;
    }

    height
}

#[cfg(test)]
mod tests {
    use circuit::array::tree_height;

    #[test]
    fn test_tree_height() {
        let table: &[(usize, usize)] = &[(0, 0), (1, 0), (2, 1), (3, 2), (4, 2), (5, 3)];

        for (size, height) in table.iter() {
            assert_eq!(tree_height(*size), *height, "tree_height({})", size);
        }
    }
}

impl<E: Engine> Array<E> {
    pub fn new(values: &[Option<E::Fr>]) -> Self {
        assert_ne!(values.len(), 0, "empty array");
        Self { values: values.to_vec() }
    }

    pub fn get_by_index<CS: ConstraintSystem<E>>(&self, mut cs: CS, index: Option<E::Fr>)
        -> Result<Option<E::Fr>, SynthesisError> {

        let height = tree_height(self.values.len());

        let index_num = AllocatedNum::alloc(cs.namespace(|| "index"), || Ok(index.unwrap()))?;
        let bits = index_num.into_bits_le_fixed(cs.namespace(|| "index bits"), height)?;



        Self::recursive_select(
            cs.namespace(|| "recursive select"),
            self.values.as_slice(),
            bits.as_slice()
        )
    }

    fn recursive_select<CS: ConstraintSystem<E>>(mut cs: CS, array: &[Option<E::Fr>], index_bits_le: &[Boolean])
        -> Result<Option<E::Fr>, SynthesisError> {

        if array.len() == 1 {
            return Ok(array[0]);
        }

        assert_ne!(index_bits_le.len(), 0, "not enough index bits");

        let new_len = (array.len() + 1) / 2;
        let mut new_array: Vec<Option<E::Fr>> = Vec::new();

        for i in 0..new_len {
            if i * 2 + 1 == array.len() {
                break;
            }

            let left = AllocatedNum::alloc(cs.namespace(|| "left num"), || Ok(array[i * 2].unwrap()))?;
            let right = AllocatedNum::alloc(cs.namespace(|| "right num"), || Ok(array[i * 2 + 1].unwrap()))?;

            let num = AllocatedNum::conditionally_select(
                cs.namespace(|| "select"),
                &right, &left,
                index_bits_le.first().unwrap()
            )?;

            new_array.push(num.get_value());
        }

        Self::recursive_select(cs.namespace(|| "recursive select"), new_array.as_slice(), &index_bits_le[1..])
    }

    pub fn get_by_constant_index<CS: ConstraintSystem<E>>(&self, index: usize) -> Option<E::Fr> {
        self.values[index]
    }

    pub fn get_commitment<CS: ConstraintSystem<E>>(&self, mut cs: CS)
        -> Result<Option<E::Fr>, SynthesisError> {

        let mut array_bits: Vec<Boolean> = Vec::new();
        for value in self.values.iter() {
            let num = AllocatedNum::alloc(cs.namespace(|| "array element"), || Ok(value.unwrap()))?;
            let mut bits = num.into_bits_le_fixed(cs.namespace(|| "element bits"), WIDTH)?;
            array_bits.append(bits.as_mut());
        }

        let hash = sha256(cs.namespace(|| "array hash"), array_bits.as_slice())?;
        let commitment = Expression::le_bits::<CS>(hash.as_slice());

        Ok(commitment.get_value())
    }
}
