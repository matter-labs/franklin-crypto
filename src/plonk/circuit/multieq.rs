use crate::bellman::pairing::{
    Engine,
};

use crate::bellman::pairing::ff::{
    Field,
    PrimeField,
    PrimeFieldRepr,
    BitIterator
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
};


use crate::plonk::circuit::Assignment;

use super::allocated_num::{
    AllocatedNum
};

use super::linear_combination::{
    LinearCombination
};

pub struct MultiEq<'a, E: Engine, CS: ConstraintSystem<E> + 'a>{
    cs: &'a mut CS,
    ops: usize,
    bits_used: usize,
    lhs: LinearCombination<E>,
    rhs: LinearCombination<E>,
}

impl<'a, E: Engine, CS: ConstraintSystem<E> + 'a> MultiEq<'a, E, CS> {
    pub fn new(cs: &'a mut CS) -> Self {
        MultiEq {
            cs: cs,
            ops: 0,
            bits_used: 0,
            lhs: LinearCombination::<E>::zero(),
            rhs: LinearCombination::<E>::zero()
        }
    }

    pub fn as_cs(&mut self) -> &mut CS {
        &mut self.cs
    }

    fn accumulate(&mut self)
    {
        let mut lhs = self.lhs.clone();
        let mut rhs = self.rhs.clone();
        let mut minus_one = E::Fr::one();
        minus_one.negate();
        rhs.scale(&minus_one);

        lhs.add_assign(&rhs);

        lhs.enforce_zero(self.cs).expect("must enforce");

        self.lhs = LinearCombination::<E>::zero();
        self.rhs = LinearCombination::<E>::zero();
        self.bits_used = 0;
        self.ops += 1;
    }

    pub fn enforce_equal(
        &mut self,
        num_bits: usize,
        lhs: &LinearCombination<E>,
        rhs: &LinearCombination<E>
    )
    {
        // Check if we will exceed the capacity
        if (E::Fr::CAPACITY as usize) <= (self.bits_used + num_bits) {
            self.accumulate();
        }

        assert!((E::Fr::CAPACITY as usize) > (self.bits_used + num_bits));

        let coeff = E::Fr::from_str("2").unwrap().pow(&[self.bits_used as u64]);
        let mut scaled_lhs = lhs.clone();
        scaled_lhs.scale(&coeff);

        let mut scaled_rhs = rhs.clone();
        scaled_rhs.scale(&coeff);

        self.lhs.add_assign(&scaled_lhs);
        self.rhs.add_assign(&scaled_rhs);

        self.bits_used += num_bits;
    }
}

impl<'a, E: Engine, CS: ConstraintSystem<E> + 'a> Drop for MultiEq<'a, E, CS> {
    fn drop(&mut self) {
        if self.bits_used > 0 {
           self.accumulate();
        }
    }
}

pub fn bytes_to_bits(bytes: &[u8]) -> Vec<bool>
{
    bytes.iter()
         .flat_map(|&v| (0..8).rev().map(move |i| (v >> i) & 1 == 1))
         .collect()
}

pub fn bytes_to_bits_le(bytes: &[u8]) -> Vec<bool>
{
    bytes.iter()
         .flat_map(|&v| (0..8).map(move |i| (v >> i) & 1 == 1))
         .collect()
}

pub fn compute_multipacking<E: Engine>(
    bits: &[bool]
) -> Vec<E::Fr>
{
    let mut result = vec![];

    for bits in bits.chunks(E::Fr::CAPACITY as usize)
    {
        let mut cur = E::Fr::zero();
        let mut coeff = E::Fr::one();

        for bit in bits {
            if *bit {
                cur.add_assign(&coeff);
            }

            coeff.double();
        }

        result.push(cur);
    }

    result
}