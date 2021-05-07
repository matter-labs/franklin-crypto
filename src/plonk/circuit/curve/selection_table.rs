use crate::bellman::pairing::{
    Engine,
    GenericCurveAffine,
    GenericCurveProjective
};

use crate::bellman::pairing::ff::{
    Field,
    PrimeField,
    PrimeFieldRepr,
    BitIterator,
    ScalarEngine
};

use crate::bellman::{
    SynthesisError,
};

use crate::bellman::plonk::better_better_cs::cs::{
    Variable, 
    ConstraintSystem,
    ArithmeticTerm,
    MainGateTerm,
    Width4MainGateWithDNext,
    MainGate,
    GateInternal,
    Gate,
    LinearCombinationOfTerms,
    PolynomialMultiplicativeTerm,
    PolynomialInConstraint,
    TimeDilation,
    Coefficient,
    PlonkConstraintSystemParams,
    TrivialAssembly,
    PlonkCsWidth4WithNextStepParams,
};

use super::super::allocated_num::{AllocatedNum, Num};
use super::super::linear_combination::LinearCombination;
use super::super::simple_term::Term;
use super::super::boolean::{Boolean, AllocatedBit};

use num_bigint::BigUint;
use num_integer::Integer;

use super::super::bigint::field::*;
use super::super::bigint::bigint::*;

use super::sw_affine::*;

// later on (when Rust matures) we will be able to constraint as Table<Item = X, Width = Y>
pub trait Table: Sized + Clone {
    // const WIDTH: usize;
    type Item: Clone;

    fn width(&self) -> usize;
    fn select<E: Engine, CS: ConstraintSystem<E>>(&self, cs: &mut CS, bits: &[Boolean]) -> Result<Self::Item, SynthesisError>;
}

pub trait TableSelectable<E: Engine>: Sized + Clone {
    fn add<CS: ConstraintSystem<E>>(cs: &mut CS, first: Self, second: Self) -> Result<Self, SynthesisError>;
    fn add_many<CS: ConstraintSystem<E>>(cs: &mut CS, items: &[Self]) -> Result<Self, SynthesisError>;
    fn negate<CS: ConstraintSystem<E>>(cs: &mut CS, first: Self) -> Result<Self, SynthesisError>;
    fn select<CS: ConstraintSystem<E>>(cs: &mut CS, flag: &Boolean, first: Self, second: Self) -> Result<Self, SynthesisError>;
    fn fma<CS: ConstraintSystem<E>>(cs: &mut CS, mul_a: Self, mul_b: Self, add_c: Self) -> Result<Self, SynthesisError>;
    fn from_bit(bit: &Boolean) -> Self;
}


impl<E: Engine> TableSelectable<E> for Term<E> {
    fn add<CS: ConstraintSystem<E>>(cs: &mut CS, first: Self, second: Self) -> Result<Self, SynthesisError> {
        let result = first.add(cs, &second)?;

        Ok(result)
    }
    fn add_many<CS: ConstraintSystem<E>>(cs: &mut CS, items: &[Self]) -> Result<Self, SynthesisError> {
        let (first, other) = items.split_first().expect("must be at least one item");

        let result = first.add_multiple(cs, other)?;

        Ok(result)
    }
    fn negate<CS: ConstraintSystem<E>>(_cs: &mut CS, first: Self) -> Result<Self, SynthesisError> {
        let mut new = first;
        new.negate();

        Ok(new)
    }

    fn select<CS: ConstraintSystem<E>>(cs: &mut CS, flag: &Boolean, first: Self, second: Self) -> Result<Self, SynthesisError> {
        let result = Term::<E>::select(cs, flag, &first, &second)?;

        Ok(result)
    }

    fn fma<CS: ConstraintSystem<E>>(cs: &mut CS, mul_a: Self, mul_b: Self, add_c: Self) -> Result<Self, SynthesisError> {
        let result = Term::<E>::fma(cs, &mul_a, &mul_b, &add_c)?;

        Ok(result)
    }
    fn from_bit(bit: &Boolean) -> Self {
        Term::<E>::from_boolean(bit)
    }
}

// impl<'a, E: Engine, F: PrimeField> TableSelectable<E> for FieldElement<'a, E, F> {
//     fn add<CS: ConstraintSystem<E>>(cs: &mut CS, first: Self, second: Self) -> Result<Self, SynthesisError> {
//         assert!(first.needs_reduction() == false);
//         assert!(second.needs_reduction() == false);
//         let (result, _) = first.add(cs, second)?;

//         Ok(result)
//     }
//     fn add_many<CS: ConstraintSystem<E>>(cs: &mut CS, items: &[Self]) -> Result<Self, SynthesisError> {
//         let (first, other) = items.split_first().expect("must be at least one item");
//         let mut first = first.clone();
//         assert!(first.needs_reduction() == false);
//         for o in other.iter() {
//             assert!(o.needs_reduction() == false);
//             let (t, _) = first.add(cs, o.clone())?;
//             first = t;
//         }

//         Ok(first)
//     }

//     fn negate<CS: ConstraintSystem<E>>(cs: &mut CS, first: Self) -> Result<Self, SynthesisError> {
//         assert!(first.needs_reduction() == false);
//         let (negated, _) = first.negated(cs)?;

//         Ok(negated)
//     }

//     fn select<CS: ConstraintSystem<E>>(cs: &mut CS, flag: &Boolean, first: Self, second: Self) -> Result<Self, SynthesisError> {
//         assert!(first.needs_reduction() == false);
//         assert!(second.needs_reduction() == false);
//         let (result, (first, second)) = FieldElement::<E, F>::select(cs, flag, first, second)?;

//         Ok(result)
//     }

//     fn fma<CS: ConstraintSystem<E>>(cs: &mut CS, mul_a: Self, mul_b: Self, add_c: Self) -> Result<Self, SynthesisError> {
//         assert!(mul_a.needs_reduction() == false);
//         assert!(mul_b.needs_reduction() == false);
//         assert!(add_c.needs_reduction() == false);
//         let (result, _) = mul_a.fma_with_addition_chain(cs, mul_b, vec![add_c])?;

//         Ok(result)
//     }
// }

#[derive(Clone, Debug)]
pub struct SelectorTable<E: Engine, T: TableSelectable<E>> {
    entries: Vec<T>,
    _marker: std::marker::PhantomData<E>
}

impl<E: Engine, T: TableSelectable<E>> SelectorTable<E, T> {
    pub fn new_from_entries<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        entries: &[T]
    ) -> Result<Self, SynthesisError> {
        match entries.len() {
            0 => {
                panic!("empty table!");
            }
            2 => {
                let new = Self::new_one_bit_table(entries);

                Ok(new)
            },
            4 => {
                let new = Self::new_two_bit_table(cs, entries)?;

                Ok(new)
            },
            8 => {
                let new = Self::new_three_bit_table(cs, entries)?;

                Ok(new)
            },
            l @ _ => {
                unimplemented!("large table length is not supported, or length {} is invalid", l);
            }
        }
    }

    fn new_one_bit_table(entries: &[T]) -> Self {
        Self {
            entries: entries.to_vec(),
            _marker: std::marker::PhantomData
        }
    }

    fn new_two_bit_table<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        entries: &[T]
    ) -> Result<Self, SynthesisError> {
        assert_eq!(entries.len(), 4);
        // make a table of linear combinations

        let t0 = entries[0].clone();
        let t1 = entries[1].clone();
        let t2 = entries[2].clone();
        let t3 = entries[3].clone();

        let t0_negated = T::negate(cs, t0.clone())?;
        let t1_negated = T::negate(cs, t1.clone())?;
        let t2_negated = T::negate(cs, t2.clone())?;

        let entry_0 = t0.clone();
        let entry_1 = T::add_many(cs, &[t1, t0_negated.clone()])?;
        let entry_2 = T::add_many(cs, &[t2, t0_negated])?;
        let entry_3 = T::add_many(cs, &[t3, t2_negated, t1_negated, t0])?;

        let new = Self {
            entries: vec![entry_0, entry_1, entry_2, entry_3],
            _marker: std::marker::PhantomData
        };

        Ok(new)
    }

    fn new_three_bit_table<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        entries: &[T]
    ) -> Result<Self, SynthesisError> {
        assert_eq!(entries.len(), 8);
        // make a table of linear combinations

        let t0 = entries[0].clone();
        let t1 = entries[1].clone();
        let t2 = entries[2].clone();
        let t3 = entries[3].clone();
        let t4 = entries[4].clone();
        let t5 = entries[5].clone();
        let t6 = entries[6].clone();
        let t7 = entries[7].clone();

        let t0_negated = T::negate(cs, t0.clone())?;
        let t1_negated = T::negate(cs, t1.clone())?;
        let t2_negated = T::negate(cs, t2.clone())?;
        let t3_negated = T::negate(cs, t3.clone())?;
        let t4_negated = T::negate(cs, t4.clone())?;
        let t5_negated = T::negate(cs, t5.clone())?;
        let t6_negated = T::negate(cs, t6.clone())?;

        let entry_0 = t0.clone();
        let entry_1 = T::add_many(cs, &[t1.clone(), t0_negated.clone()])?;
        let entry_2 = T::add_many(cs, &[t2.clone(), t0_negated.clone()])?;
        let entry_3 = T::add_many(cs, &[t4.clone(), t0_negated.clone()])?;
        let entry_4 = T::add_many(cs, &[t3, t2_negated.clone(), t1_negated.clone(), t0.clone()])?;
        let entry_5 = T::add_many(cs, &[t5, t4_negated.clone(), t1_negated, t0.clone()])?;
        let entry_6 = T::add_many(cs, &[t6, t4_negated, t2_negated, t0])?;
        let entry_7 = T::add_many(cs, &[t7, t6_negated, t5_negated, t4, t3_negated, t2, t1, t0_negated])?;

        let new = Self {
            entries: vec![entry_0, entry_1, entry_2, entry_3, entry_4, entry_5, entry_6, entry_7],
            _marker: std::marker::PhantomData
        };

        Ok(new)
    }

    pub fn select<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        bits: &[Boolean]
    ) -> Result<T, SynthesisError> {
        match bits.len() {
            0 => {
                panic!("empty table!");
            }
            1 => {
                let result = self.select_one_bit(cs, bits)?;

                Ok(result)
            },
            2 => {
                let result = self.select_two_bits(cs, bits)?;

                Ok(result)
            },
            3 => {
                let result = self.select_three_bits(cs, bits)?;

                Ok(result)
            },
            _ => {
                unimplemented!("large table length is not supported");
            }
        }
    }

    fn select_one_bit<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        bits: &[Boolean]
    ) -> Result<T, SynthesisError> {
        assert_eq!(bits.len(), 1);
        assert_eq!(self.entries.len(), 2);

        let result = T::select(cs, &bits[0], self.entries[1].clone(), self.entries[0].clone())?;

        Ok(result)
    }

    fn select_two_bits<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        bits: &[Boolean]
    ) -> Result<T, SynthesisError> {
        assert_eq!(bits.len(), 2);
        assert_eq!(self.entries.len(), 4);

        // we expect bits from high to low
        let b0_as_t = T::from_bit(&bits[1]);
        let b1_as_t = T::from_bit(&bits[0]);

        let s0 = T::fma(cs, b1_as_t.clone(), self.entries[3].clone(), self.entries[1].clone())?;
        let s1 = T::fma(cs, b0_as_t, s0, self.entries[0].clone())?;
        let s2 = T::fma(cs, b1_as_t, self.entries[2].clone(), s1)?;

        // simple sanity check for b0 = 1, b1 = 1
        // s0 = t3 - t2 - t1 + t0 + t1 - t0 = t3 - t2
        // s1 = t3 - t2 + t0
        // s2 = t2 - t0 + t3 - t2 + t0 = t3

        // simple sanity check for b0 = 0, b1 = 1
        // s0 = t3 - t2 - t1 + t0 + t1 - t0 = t3 - t2
        // s1 = t0
        // s2 = t2 - t0 + t0 = t2

        Ok(s2)
    }

    fn select_three_bits<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        bits: &[Boolean]
    ) -> Result<T, SynthesisError> {
        assert_eq!(bits.len(), 3);
        assert_eq!(self.entries.len(), 8);

        // we expect bits from high to low
        let b0_as_t = T::from_bit(&bits[2]);
        let b1_as_t = T::from_bit(&bits[1]);
        let b2_as_t = T::from_bit(&bits[0]);

        let s0 = T::fma(cs, b0_as_t.clone(), self.entries[7].clone(), self.entries[6].clone())?;
        let s1 = T::fma(cs, b1_as_t.clone(), s0, self.entries[3].clone())?;
        let s2 = T::fma(cs, b2_as_t.clone(), s1, self.entries[0].clone())?;
        let s3 = T::fma(cs, b0_as_t.clone(), self.entries[4].clone(), self.entries[2].clone())?;
        let s4 = T::fma(cs, b1_as_t, s3, s2)?;
        let s5 = T::fma(cs, b2_as_t, self.entries[5].clone(), self.entries[1].clone())?;
        let s6 = T::fma(cs, b0_as_t, s5, s4)?;

        Ok(s6)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::bellman::pairing::bn256::{Fq, Bn256, Fr, G1Affine};

    #[test]
    fn test_one_bit_table(){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for _i in 0..10 {
            let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

            let input: Vec<Fr> = (0..2).map(|_| rng.gen()).collect();

            let mut terms = vec![];
            for i in input.iter() {
                let n = AllocatedNum::alloc(
                    &mut cs,
                    || {
                        Ok(*i)
                    }
                ).unwrap();
                let t = Term::<Bn256>::from_allocated_num(n);
                terms.push(t);
            }

            let table = SelectorTable::new_from_entries(&mut cs, &terms).unwrap();

            for &b0 in [false, true].iter() {
                let expected_idx = b0 as usize;
                let expeted = &terms[expected_idx];
                let b0 = Boolean::from(AllocatedBit::alloc(&mut cs, Some(b0)).unwrap());
                let selected = table.select_one_bit(&mut cs, &[b0]).unwrap();

                assert_eq!(selected.get_value().unwrap(), expeted.get_value().unwrap(), "invalid for index {}", expected_idx);
            }
        }
    }

    #[test]
    fn test_two_bit_table(){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for _i in 0..10 {
            let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

            let input: Vec<Fr> = (0..4).map(|_| rng.gen()).collect();

            let mut terms = vec![];
            for i in input.iter() {
                let n = AllocatedNum::alloc(
                    &mut cs,
                    || {
                        Ok(*i)
                    }
                ).unwrap();
                let t = Term::<Bn256>::from_allocated_num(n);
                terms.push(t);
            }

            let t0 = input[0];

            let mut t1 = input[1];
            t1.sub_assign(&input[0]);

            let mut t2 = input[2];
            t2.sub_assign(&input[0]);

            let mut t3 = input[3];
            t3.sub_assign(&input[2]);
            t3.sub_assign(&input[1]);
            t3.add_assign(&input[0]);

            let table = SelectorTable::new_from_entries(&mut cs, &terms).unwrap();

            assert_eq!(table.entries[0].get_value().unwrap(), t0);
            assert_eq!(table.entries[1].get_value().unwrap(), t1);
            assert_eq!(table.entries[2].get_value().unwrap(), t2);
            assert_eq!(table.entries[3].get_value().unwrap(), t3);

            for &b0 in [false, true].iter() {
                for &b1 in [false, true].iter() {
                    let expected_idx = (b1 as usize) * 2 + (b0 as usize);
                    let expeted = &terms[expected_idx];
                    let b0 = Boolean::from(AllocatedBit::alloc(&mut cs, Some(b0)).unwrap());
                    let b1 = Boolean::from(AllocatedBit::alloc(&mut cs, Some(b1)).unwrap());

                    let selected = table.select_two_bits(&mut cs, &[b1, b0]).unwrap();

                    assert_eq!(selected.get_value().unwrap(), expeted.get_value().unwrap(), "invalid for index {}", expected_idx);
                }
            }
        }
    }

    #[test]
    fn test_three_bit_table(){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for _i in 0..10 {
            let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

            let input: Vec<Fr> = (0..8).map(|_| rng.gen()).collect();

            let mut terms = vec![];
            for i in input.iter() {
                let n = AllocatedNum::alloc(
                    &mut cs,
                    || {
                        Ok(*i)
                    }
                ).unwrap();
                let t = Term::<Bn256>::from_allocated_num(n);
                terms.push(t);
            }

            let table = SelectorTable::new_from_entries(&mut cs, &terms).unwrap();

            for &b0 in [false, true].iter() {
                for &b1 in [false, true].iter() {
                    for &b2 in [false, true].iter() {
                        let expected_idx = (b2 as usize) * 4 + (b1 as usize) * 2 + (b0 as usize);
                        let expeted = &terms[expected_idx];
                        let b0 = Boolean::from(AllocatedBit::alloc(&mut cs, Some(b0)).unwrap());
                        let b1 = Boolean::from(AllocatedBit::alloc(&mut cs, Some(b1)).unwrap());
                        let b2 = Boolean::from(AllocatedBit::alloc(&mut cs, Some(b2)).unwrap());

                        let selected = table.select_three_bits(&mut cs, &[b2, b1, b0]).unwrap();

                        assert_eq!(selected.get_value().unwrap(), expeted.get_value().unwrap(), "invalid for index {}", expected_idx);
                    }
                }
            }
        }
    }
}