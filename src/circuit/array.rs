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
                new_array.push(*array.last().unwrap());
                break;
            }

            let left = AllocatedNum::alloc(
                cs.namespace(|| format!("left num {}", i)),
                || Ok(array[i * 2].unwrap()))?;

            let right = AllocatedNum::alloc(
                cs.namespace(|| format!("right num {}", i)),
                || Ok(array[i * 2 + 1].unwrap()))?;

            let num = AllocatedNum::conditionally_select(
                cs.namespace(|| format!("selected num {}", i)),
                &right, &left,
                index_bits_le.first().unwrap()
            )?;

            new_array.push(num.get_value());
        }

        Self::recursive_select(cs.namespace(|| "recursive select"), new_array.as_slice(), &index_bits_le[1..])
    }

    pub fn get_by_constant_index(&self, index: usize) -> Option<E::Fr> {
        self.values[index]
    }

    /// Returns `bits` bits of commitment (sha256).
    ///
    /// Array is encoded into little endian representation.
    ///
    /// Note that you will have to reverse bits in bytes
    /// if you want to calculate hash outside of this method.
    ///
    /// For example, 160 bits commitment of array with hash:
    ///
    ///     f05e166cf4ba4d102ad6454fe9775813ebc51213efbc515a082a1d2807f5bf14
    ///
    /// would yield next result:
    ///
    ///     Fr('0x00000000000000000000000000000000ebc51213efbc515a082a1d2807f5bf14')
    pub fn get_commitment<CS: ConstraintSystem<E>>(&self, mut cs: CS, bits: usize)
        -> Result<Option<E::Fr>, SynthesisError> {

        let mut array_bits: Vec<Boolean> = Vec::new();
        for (i, value) in self.values.iter().enumerate() {
            let num = AllocatedNum::alloc(
                cs.namespace(|| format!("array element {}", i)),
                || Ok(value.unwrap()))?;

            let mut bits = num.into_bits_le_fixed(
                cs.namespace(|| format!("element bits {}", i)), WIDTH)?;

            array_bits.append(bits.as_mut());
        }

        let mut hash = sha256(cs.namespace(|| "array hash"), array_bits.as_slice())?;
        hash.reverse();
        let commitment = Expression::le_bits::<CS>(&hash[0..bits]);

        Ok(commitment.get_value())
    }
}


#[cfg(test)]
mod test {
    use super::*;
    use circuit::test::TestConstraintSystem;
    use bellman::pairing::bn256::{Bn256, Fr};

    #[test]
    fn test_constant_index() {
        let mut cs = TestConstraintSystem::<Bn256>::new();

        let values: Vec<Option<Fr>> = [0, 1, 4, 9, 16, 25, 36, 49]
            .iter()
            .map(|x| Fr::from_str(&x.to_string()))
            .collect();

        let array = Array::<Bn256>::new(values.as_slice());

        for (i, v) in values.iter().enumerate() {
            let r = array.get_by_constant_index(i);
            assert_eq!(r, values[i], "failed to get element by constant index");
        }
    }

    #[test]
    fn test_variable_index() {
        let mut cs = TestConstraintSystem::<Bn256>::new();

        let values: Vec<Option<Fr>> = [0, 1, 4, 9, 16, 25, 36, 49]
            .iter()
            .map(|x| Fr::from_str(&x.to_string()))
            .collect();

        let array = Array::<Bn256>::new(values.as_slice());

        for (i, v) in values.iter().enumerate() {
            let index = Expression::u64::<TestConstraintSystem<Bn256>>(i as u64);
            let value = array.get_by_index(
                cs.namespace(|| format!("array index {}", i)), index.get_value()
            );

            assert!(value.is_ok(), "synthesis error");

            assert_eq!(value.unwrap(), values[i], "failed to get element by variable index {}", i);
        }
    }

    #[test]
    fn test_commitment() {
        let mut cs = TestConstraintSystem::<Bn256>::new();

        let values: Vec<Option<Fr>> = [0, 1, 4, 9, 16, 25, 36, 49]
            .iter()
            .map(|x| Fr::from_str(&x.to_string()))
            .collect();

        let array = Array::<Bn256>::new(values.as_slice());

        let expected = Fr::from_hex("0xe9775813ebc51213efbc515a082a1d2807f5bf14").unwrap();
        let actual = array.get_commitment(cs, 160);
        assert!(actual.is_ok(), "commitment must be Ok");
        assert_eq!(actual.unwrap(), Some(expected), "hash doesn't match");
    }

    #[test]
    fn test_tree_height() {
        let table: &[(usize, usize)] = &[(1, 0), (2, 1), (3, 2), (4, 2), (5, 3)];

        for (size, height) in table.iter() {
            assert_eq!(tree_height(*size), *height, "tree_height({}) == {}", size, height);
        }
    }
}
