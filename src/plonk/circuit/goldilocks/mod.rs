use num_traits::ops::overflowing;

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

use plonk::circuit::boolean::Boolean;

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
    PlonkCsWidth4WithNextStepParams,
    TrivialAssembly
};

use crate::plonk::circuit::Assignment;
use super::*;
use super::bigint::*;

use crate::plonk::circuit::allocated_num::{AllocatedNum, Num};
use crate::plonk::circuit::simple_term::{Term};
use crate::plonk::circuit::linear_combination::LinearCombination;

use plonk::circuit::bigint_new::{
    enforce_range_check_using_naive_approach,
    enforce_range_check_using_bitop_table,
    BITWISE_LOGICAL_OPS_TABLE_NAME
};

use boojum::field::{
    goldilocks::GoldilocksField as GL,
    U64Representable,
    PrimeField as PF,
    goldilocks::GoldilocksExt2,
    ExtensionField
};

use std::result;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};
use derivative::*;
use std::hash::{Hash, Hasher};

pub mod prime_field_like;

#[derive(Derivative)]
#[derivative(Clone, Copy, Copy, Default, Debug(bound = ""))]
pub struct GoldilocksField<E: Engine> {
    inner: Num<E>,
}

impl<E: Engine> Hash for GoldilocksField<E> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let value: Option<u64> = (*self).into_u64();
        value.hash(state);
    }
}

fn range_check_for_num_bits<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    num: &Num<E>,
    num_bits: usize
) -> Result<(), SynthesisError> {
    assert!(num_bits % 16 == 0);

    if let Num::Constant(value) = num {
        for el in value.into_repr().as_ref().iter().skip(1) {
            assert_eq!(0, *el)
        }
    } else {
        // Name of the table should be checked
        if let Ok(table) = cs.get_table(BITWISE_LOGICAL_OPS_TABLE_NAME) {
            enforce_range_check_using_bitop_table(cs, &num.get_variable(), num_bits, table, true)?;
        } else {
            enforce_range_check_using_naive_approach(cs, &num.get_variable(), num_bits)?;
        }
    }

    Ok(())
}

impl<E: Engine> GoldilocksField<E> {
    pub const ORDER: u64 = 0xFFFFFFFF00000001;
    pub const ORDER_BITS: usize = 64;
    pub const REMAINDER: u64 = 0xFFFFFFFF; // ORDER + REMAINDER = 2^ORDER_BITS

    pub fn zero() -> Self {
        Self::constant(0)
    }

    pub fn one() -> Self {
        Self::constant(1)
    }

    pub fn minus_one() -> Self {
        Self::constant(Self::ORDER - 1)
    }

    pub fn constant_from_field(value: GL) -> Self {
        Self::constant(value.as_u64_reduced())
    }

    pub fn constant(value: u64) -> Self {
        assert!(value < Self::ORDER);
        Self {
            inner: Num::Constant(E::Fr::from_repr(value.into()).unwrap()),
        }
    }

    pub fn into_u64(self) -> Option<u64> {
        if let Some(value) = self.inner.get_value() {
            let value_buffer = value.into_repr();
            for el in value_buffer.as_ref().iter().skip(1) {
                assert_eq!(0, *el)
            }
            Some(value_buffer.as_ref()[0])
        } else {
            None
        }
    }

    pub fn into_field(self) -> Option<GL> {
        self.into_u64().map(|value| GL::from_u64_unchecked(value))
    }
    
    pub fn is_constant(&self) -> bool {
        self.inner.is_constant()
    }

    pub fn alloc<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        witness: Option<E::Fr>
    ) -> Result<Self, SynthesisError> {
        let num = Num::alloc(cs, witness)?;
        Self::from_num(cs, num)
    }

    pub fn alloc_from_u64<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        witness: Option<u64>
    ) -> Result<Self, SynthesisError> {
        let witness = witness.map(|value| E::Fr::from_repr(value.into()).unwrap());
        Self::alloc(cs, witness)
    }

    pub fn alloc_from_field<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        witness: Option<GL>
    ) -> Result<Self, SynthesisError> {
        let witness = witness.map(|value| value.as_u64_reduced());
        Self::alloc_from_u64(cs, witness)
    }

    pub unsafe fn from_num_unchecked(num: Num<E>) -> Result<Self, SynthesisError> {
        Ok(Self {
            inner: num,
        })
    }

    pub fn from_num<CS: ConstraintSystem<E>>(cs: &mut CS, num: Num<E>) -> Result<Self, SynthesisError> {
        let remainder = Num::Constant(E::Fr::from_repr(Self::REMAINDER.into()).unwrap());
        range_check_for_num_bits(cs, &num, 64)?;

        let check = num.add(cs, &remainder)?;
        range_check_for_num_bits(cs, &check, 64)?;

        Ok(Self {
            inner: num,
        })
    }

    pub fn into_num(&self) -> Num<E> {
        self.inner
    }

    /// This function is used in SNARK-wrapper to get Goldilocks challenges
    /// from random Bn256 scalar field element. Usually, we use N = 3.
    /// Note: we lose some information during this conversion, but it's OK.
    /// We only care about good output distribution.
    pub fn from_num_to_multiple_with_reduction<CS: ConstraintSystem<E>, const N: usize>(
        cs: &mut CS,
        num: Num<E>,
    ) -> Result<[Self; N], SynthesisError> {
        assert_eq!(Self::ORDER_BITS, 64, "Only this case is supported for now");
        assert!(
            N * Self::ORDER_BITS <= E::Fr::CAPACITY as usize,
            "Scalar field capacity is too small"
        );
        let mut result = [Self::constant(0); N];

        if let Num::Constant(value) = num {
            let repr = value.into_repr();

            for (i, el) in repr.as_ref()[..N].iter().enumerate() {
                result[i] = Self::constant(el % Self::ORDER);
            }
        } else {
            let mut u64_chunks = vec![];
            let mut overflowing = [None; N];
            if let Some(value) = num.get_value() {
                let repr = value.into_repr();

                for (i, el) in repr.as_ref()[..N].iter().enumerate() {
                    overflowing[i] = Some(*el >= Self::ORDER);
                }
                u64_chunks = repr.as_ref().iter().map(|el| Some(*el)).collect();
            } else {
                let repr = <E::Fr as PrimeField>::Repr::default();
                u64_chunks = vec![None; repr.as_ref().len()];
            }

            // Firstly we check that chunks sum is correct
            let mut allocated_chunks = vec![];

            let mut coeff = E::Fr::one();
            let mut shift_repr = E::Fr::one().into_repr();
            shift_repr.shl(Self::ORDER_BITS as u32);
            let shift = E::Fr::from_repr(shift_repr).unwrap();

            let mut minus_one = E::Fr::one();
            minus_one.negate();

            let mut lc = LinearCombination::<E>::zero();
            for chunk in u64_chunks {
                let witness = chunk.map(|value| E::Fr::from_repr(value.into()).unwrap());
                let allocated_chunk = Num::alloc(cs, witness)?;
                range_check_for_num_bits(cs, &allocated_chunk, 64)?;
                lc.add_assign_number_with_coeff(&allocated_chunk, coeff);
                coeff.mul_assign(&shift);
                allocated_chunks.push(allocated_chunk)
            }
            lc.add_assign_number_with_coeff(&num, minus_one);
            lc.enforce_zero(cs)?;

            // Now we check that there is no overflow
            assert_eq!(
                allocated_chunks.len(),
                4,
                "Only this case is supported for now"
            );

            let mut first_u128_chunk: LinearCombination<E> = allocated_chunks[0].into();
            first_u128_chunk.add_assign_number_with_coeff(&allocated_chunks[1], shift);
            let first_u128_chunk = first_u128_chunk.into_num(cs)?;

            let mut second_u128_chunk: LinearCombination<E> = allocated_chunks[2].into();
            second_u128_chunk.add_assign_number_with_coeff(&allocated_chunks[3], shift);
            let second_u128_chunk = second_u128_chunk.into_num(cs)?;

            let max_field_element = minus_one;
            let (first_max_element_chunk, second_max_element_chunk) = {
                let fe_repr: Vec<_> = max_field_element
                    .into_repr()
                    .as_ref()
                    .iter()
                    .map(|value| E::Fr::from_repr((*value).into()).unwrap())
                    .collect();

                let mut first_chunk = fe_repr[1];
                first_chunk.mul_assign(&shift);
                first_chunk.add_assign(&fe_repr[0]);

                let mut second_chunk = fe_repr[3];
                second_chunk.mul_assign(&shift);
                second_chunk.add_assign(&fe_repr[2]);

                (Num::Constant(first_chunk), Num::Constant(second_chunk))
            };

            let check = second_max_element_chunk.sub(cs, &second_u128_chunk)?;
            range_check_for_num_bits(cs, &check, 128)?;
            let flag = check.is_zero(cs)?.not();

            let mut double_shift_repr = E::Fr::one().into_repr();
            double_shift_repr.shl(2 * Self::ORDER_BITS as u32);
            let double_shift = E::Fr::from_repr(double_shift_repr).unwrap();

            let mut check_2: LinearCombination<E> = first_max_element_chunk.into();
            check_2.add_assign_number_with_coeff(&first_u128_chunk, minus_one);
            check_2.add_assign_boolean_with_coeff(&flag, double_shift);
            let check_2 = check_2.into_num(cs)?;
            range_check_for_num_bits(cs, &check_2, 144)?;

            // Now we can get Goldilocks elements from N u64 chunks
            let mut neg_modulus = E::Fr::from_repr(Self::ORDER.into()).unwrap();
            neg_modulus.negate();
            for i in 0..N {
                let mut result_element: LinearCombination<E> = allocated_chunks[i].into();
                let overflow_flag = Boolean::alloc(cs, overflowing[i])?;
                result_element.add_assign_boolean_with_coeff(&overflow_flag, neg_modulus);
                let result_num = result_element.into_num(cs)?;

                result[i] = Self::from_num(cs, result_num)?;
            }
        }

        Ok(result)
    }

    pub fn negate<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<Self, SynthesisError> {
        let order = Num::Constant(E::Fr::from_repr(Self::ORDER.into()).unwrap());
        let negate = order.sub(cs, &self.inner)?;
        Ok(Self { inner: negate })
    }

    pub fn add<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        other: &Self,
    ) -> Result<Self, SynthesisError> {
        if let (Num::Constant(a), Num::Constant(b)) = (&self.inner, &other.inner) {
            let a = a.into_repr().as_ref()[0] as u128;
            let b = b.into_repr().as_ref()[0] as u128;

            let sum = (a + b) % Self::ORDER as u128;

            return Ok(Self::constant(sum as u64));
        }

        let mut order = E::Fr::from_repr(Self::ORDER.into()).unwrap();
        order.negate();
        let minus_order = Num::Constant(order);

        let overflow = if let (Some(a), Some(b)) = (self.inner.get_value(), other.inner.get_value()) {
            let a = a.into_repr().as_ref()[0] as u128;
            let b = b.into_repr().as_ref()[0] as u128;

            if a + b > Self::ORDER as u128 {
                Some(true)
            } else {
                Some(false)
            }
        } else {
            None
        };

        let overflow = Boolean::alloc(cs, overflow)?;

        let tmp = minus_order.mul(cs, &overflow.into())?;
        let result = self.inner.add_two(cs, &other.inner, &tmp)?;

        Self::from_num(cs, result)
    }
    
    pub fn inverse<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<Self, SynthesisError> {
        let mut inverse_witness = self.into_field();
        inverse_witness = inverse_witness.map(|el| el.inverse().expect("should be invertible"));
        let inverse = Self::alloc_from_field(cs, inverse_witness)?;

        let check = self.mul(cs, &inverse)?;
        check.enforce_equal(cs, &Self::one())?;

        Ok(inverse)
    }

    pub fn mul<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        other: &Self,
    ) -> Result<Self, SynthesisError> {
        let zero = Self::constant(0);

        self.mul_add(cs, other, &zero)
    }

    /// self * other + third
    pub fn mul_add<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        other: &Self,
        third: &Self,
    ) -> Result<Self, SynthesisError> {
        if let (Num::Constant(a), Num::Constant(b), Num::Constant(c)) = (&self.inner, &other.inner, &third.inner) {
            let a = a.into_repr().as_ref()[0] as u128;
            let b = b.into_repr().as_ref()[0] as u128;
            let c = c.into_repr().as_ref()[0] as u128;

            let result = (a * b + c) % Self::ORDER as u128;

            return Ok(Self::constant(result as u64));
        }

        let mut order = E::Fr::from_repr(Self::ORDER.into()).unwrap();
        order.negate();
        let minus_order = Num::Constant(order);

        let overflow = if let (Some(a), Some(b), Some(c)) = (self.inner.get_value(), other.inner.get_value(), third.inner.get_value()) {
            let a = a.into_repr().as_ref()[0] as u128;
            let b = b.into_repr().as_ref()[0] as u128;
            let c = c.into_repr().as_ref()[0] as u128;

            let res = (a * b + c) / Self::ORDER as u128;

            Some(E::Fr::from_repr((res as u64).into()).unwrap())
        } else {
            None
        };

        let overflow = Num::alloc(cs, overflow)?;
        range_check_for_num_bits(cs, &overflow, 64)?;

        let tmp = minus_order.mul(cs, &overflow)?;
        let mut result = self.inner.mul(cs, &other.inner)?;
        result = result.add_two(cs, &third.inner, &tmp)?;

        Self::from_num(cs, result)
    }

    pub fn equals<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        this: &Self,
        other: &Self,
    ) -> Result<Boolean, SynthesisError> {
        Num::equals(cs, &this.inner,&other.inner)
    }

    pub fn enforce_equal<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        other: &Self,
    ) -> Result<(), SynthesisError> {
        self.inner.enforce_equal(cs, &other.inner)
    }

    pub fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        bit: Boolean,
        first: &Self,
        second: &Self
    ) -> Result<Self, SynthesisError> {
        let result = Num::conditionally_select(cs, &bit, &first.inner, &second.inner)?;

        Ok(Self { inner: result} )
    }

    pub fn spread_into_bits<CS: ConstraintSystem<E>, const LIMIT: usize>(
        &self,
        cs: &mut CS,
    ) -> Result<[Boolean; LIMIT], SynthesisError> {
        let witness = match self.inner.get_value() {
            Some(value) => {
                let repr = value.into_repr();
                // this is MSB iterator
                let bit_iterator = BitIterator::new(&repr);

                let mut result = vec![];
                for el in bit_iterator {
                    result.push(el);
                }
                // now it's LSB based
                result.reverse();

                Some(result)
            }
            None => None,
        };

        let mut result = [Boolean::constant(false); LIMIT];
        for (i, dst) in result.iter_mut().enumerate() {
            let wit = witness.as_ref().map(|el| el[i]);
            let boolean = Boolean::alloc(cs, wit)?;
            *dst = boolean
        }

        let mut offset = E::Fr::one();
        let mut lc = LinearCombination::zero();
        for bit in result.iter() {
            lc.add_assign_boolean_with_coeff(&bit, offset);
            offset.double();
        }
        let mut minus_one = E::Fr::one();
        minus_one.negate();
        lc.add_assign_number_with_coeff(&self.inner, minus_one);
        lc.enforce_zero(cs)?;

        Ok(result)
    }
}

pub type GLExt = ExtensionField::<GL, 2, GoldilocksExt2>;

/// Extension with poly x^2 - 7
#[derive(Derivative)]
#[derivative(Clone, Copy, Copy, Default, Debug(bound = ""), Hash(bound = ""))]
pub struct GoldilocksFieldExt<E: Engine> {
    inner: [GoldilocksField<E>; 2],
}

impl<E: Engine> GoldilocksFieldExt<E> {
    const NON_RESIDUE: u64 = 7;
    const EXTENSION_DEGREE: usize = 2;

    pub fn zero() -> Self {
        Self::from_coords([GoldilocksField::zero(); 2])
    }

    pub fn one() -> Self {
        Self::from_coords([GoldilocksField::one(), GoldilocksField::zero()])
    }

    pub fn minus_one() -> Self {
        Self::from_coords([GoldilocksField::minus_one(), GoldilocksField::zero()])
    }

    pub fn from_coords(inner: [GoldilocksField<E>; 2]) -> Self {
        Self { inner }
    }

    pub fn into_field_ext(self) -> Option<GLExt> {
        if let (Some(x), Some(y)) = (self.inner[0].into_field(), self.inner[1].into_field()) {
            Some(GLExt {
                coeffs: [x, y],
                _marker: std::marker::PhantomData,
            })
        } else {
            None
        }
    }

    pub fn alloc_from_field_ext<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        witness: Option<GLExt>
    ) -> Result<Self, SynthesisError> {
        let (x_witness, y_witness);
        if let Some(witness) = witness {
            x_witness = Some(witness.coeffs[0]);
            y_witness = Some(witness.coeffs[1]);
        } else {
            x_witness = None;
            y_witness = None;
        };

        Ok(Self {
            inner: [
                GoldilocksField::alloc_from_field(cs, x_witness)?,
                GoldilocksField::alloc_from_field(cs, y_witness)?,
            ]
        })
    }

    pub fn constant_from_field(value: GL) -> Self {
        Self::from_coords([GoldilocksField::constant_from_field(value), GoldilocksField::zero()])
    }

    pub fn from_num_coords<CS: ConstraintSystem<E>>(
        cs: &mut CS, 
        inner: [Num<E>; 2]
    ) -> Result<Self, SynthesisError> {
        Ok(Self { 
            inner: [
            GoldilocksField::from_num(cs, inner[0])?,
            GoldilocksField::from_num(cs, inner[1])?,
            ] 
        })
    }

    pub fn constant(value: [u64; 2]) -> Self {
        let order = GoldilocksField::<E>::ORDER;
        assert!(value[0] < order && value[1] < order);
        Self {
            inner: [
                GoldilocksField::constant(value[0]),
                GoldilocksField::constant(value[1]),
            ],
        }
    }

    pub fn is_constant(&self) -> bool {
        self.inner[0].is_constant() && self.inner[1].is_constant()
    }

    pub fn negate<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<Self, SynthesisError> {
        let x = self.inner[0].negate(cs)?;
        let y = self.inner[1].negate(cs)?;
        
        Ok(GoldilocksFieldExt::from_coords([x, y]).into())
    }

    pub fn add<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        other: &Self,
    ) -> Result<Self, SynthesisError> {
        let mut result = [GoldilocksField::zero(); 2];
        for i in 0..Self::EXTENSION_DEGREE {
            result[i] = self.inner[i].add(cs, &other.inner[i])?;
        }

        Ok(Self::from_coords(result))
    }

    pub fn inverse<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<Self, SynthesisError> {
        let mut field_ext = self.into_field_ext();
        field_ext = field_ext.map(|x| x.inverse().expect("should be non-zero"));
        let inversed = Self::alloc_from_field_ext(cs, field_ext)?;

        // check inverse
        let one = Self::one();
        let check = self.mul(cs, &inversed)?;
        check.enforce_equal(cs, &one)?;

        Ok(inversed)
    }

    /// self * other + third
    pub fn mul_add<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        other: &Self,
        third: &Self,
    ) -> Result<Self, SynthesisError> {
        let mut res_witness = [None; 2];
        let mut divs = [None; 2];
        if let (
            Some(a_x), Some(a_y),
            Some(b_x), Some(b_y),
            Some(c_x), Some(c_y),
        ) = (
            &self.inner[0].inner.get_value(),  &self.inner[1].inner.get_value(), 
            &other.inner[0].inner.get_value(), &other.inner[1].inner.get_value(),
            &third.inner[0].inner.get_value(), &third.inner[1].inner.get_value(),
        ) {
            let a_x = a_x.into_repr().as_ref()[0] as u128;
            let a_y = a_y.into_repr().as_ref()[0] as u128;
            let b_x = b_x.into_repr().as_ref()[0] as u128;
            let b_y = b_y.into_repr().as_ref()[0] as u128;
            let c_x = c_x.into_repr().as_ref()[0] as u128;
            let c_y = c_y.into_repr().as_ref()[0] as u128;

            // first coordinate
            let mut res_x_part = a_y * b_y;
            let mut div_x = (res_x_part / GoldilocksField::<E>::ORDER as u128) * Self::NON_RESIDUE as u128;
            res_x_part %= GoldilocksField::<E>::ORDER as u128;

            let mut res_x = a_x * b_x;
            div_x += res_x / GoldilocksField::<E>::ORDER as u128;
            res_x %= GoldilocksField::<E>::ORDER as u128;

            res_x += c_x + res_x_part * Self::NON_RESIDUE as u128;
            div_x += res_x / GoldilocksField::<E>::ORDER as u128;
            res_x %= GoldilocksField::<E>::ORDER as u128;

            res_witness[0] = Some(res_x as u64);

            // second coordinate
            let mut res_y_part = a_y * b_x;
            let mut div_y = res_y_part / GoldilocksField::<E>::ORDER as u128;
            res_y_part %= GoldilocksField::<E>::ORDER as u128;

            let mut res_y = a_x * b_y + res_y_part + c_y;
            div_y += res_y / GoldilocksField::<E>::ORDER as u128;
            res_y %= GoldilocksField::<E>::ORDER as u128;

            res_witness[1] = Some(res_y as u64);

            // divs
            divs[0] = Some(E::Fr::from_str(&div_x.to_string()).unwrap());
            divs[1] = Some(E::Fr::from_str(&div_y.to_string()).unwrap());
        }

        if self.is_constant() && other.is_constant() && third.is_constant() {
            return Ok(
                Self::constant(
                    [res_witness[0].unwrap(), res_witness[1].unwrap()]
                )
            );
        }

        let result = [
            GoldilocksField::alloc_from_u64(cs, res_witness[0])?,
            GoldilocksField::alloc_from_u64(cs, res_witness[1])?,
        ];

        let divs = [
            Num::alloc(cs, divs[0])?,
            Num::alloc(cs, divs[1])?
        ];
        range_check_for_num_bits(cs, &divs[0], 80)?;
        range_check_for_num_bits(cs, &divs[1], 80)?;

        // check multiplication
        let mut minus_one = E::Fr::one();
        minus_one.negate();
        let non_residue = E::Fr::from_repr(Self::NON_RESIDUE.into()).unwrap();

        let order = GoldilocksField::<E>::ORDER;
        let mut minus_order = E::Fr::from_repr(order.into()).unwrap();
        minus_order.negate();


        // check first coordinate
        let v_0 = self.inner[0].inner.mul(cs, &other.inner[0].inner)?;
        let v_1 = self.inner[1].inner.mul(cs, &other.inner[1].inner)?;

        let mut lc = LinearCombination::<E>::zero();
        lc.add_assign_number_with_coeff(&v_0, E::Fr::one());
        lc.add_assign_number_with_coeff(&v_1, non_residue);
        lc.add_assign_number_with_coeff(&third.inner[0].inner, E::Fr::one());
        lc.add_assign_number_with_coeff(&result[0].inner, minus_one);
        lc.add_assign_number_with_coeff(&divs[0], minus_order);
        lc.enforce_zero(cs)?;


        // check second coordinate
        let v_0 = self.inner[0].inner.mul(cs, &other.inner[1].inner)?;
        let v_1 = self.inner[1].inner.mul(cs, &other.inner[0].inner)?;

        let mut lc = LinearCombination::<E>::zero();
        lc.add_assign_number_with_coeff(&v_0, E::Fr::one());
        lc.add_assign_number_with_coeff(&v_1, E::Fr::one());
        lc.add_assign_number_with_coeff(&third.inner[1].inner, E::Fr::one());
        lc.add_assign_number_with_coeff(&result[1].inner, minus_one);
        lc.add_assign_number_with_coeff(&divs[1], minus_order);
        lc.enforce_zero(cs)?;


        Ok(Self::from_coords(result))
    }

    pub fn mul<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        other: &Self,
    ) -> Result<Self, SynthesisError> {
        self.mul_add(cs, other, &Self::zero())
    }

    pub fn mul_by_base_field<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        other: &GoldilocksField<E>,
    ) -> Result<Self, SynthesisError> {
        let mut result = [GoldilocksField::zero(); 2];
        for i in 0..Self::EXTENSION_DEGREE {
            result[i] = self.inner[i].mul(cs, &other)?;
        }

        Ok(Self::from_coords(result))
    }

    fn enforce_equal<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        other: &Self,
    ) -> Result<(), SynthesisError> {
        self.inner[0].enforce_equal(cs, &other.inner[0])?;
        self.inner[1].enforce_equal(cs, &other.inner[1])?;
        Ok(())
    }

    pub fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        bit: Boolean,
        first: &Self,
        second: &Self
    ) -> Result<Self, SynthesisError> {
        let mut result = [GoldilocksField::zero(); 2];
        for i in 0..Self::EXTENSION_DEGREE {
            result[i] = GoldilocksField::conditionally_select(
                cs,
                bit.clone(),
                &first.inner[i],
                &second.inner[i]
            )?;
        }

        Ok(Self::from_coords(result))
    }

    pub fn evaluate_poly<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        point: &Self,
        poly: &[Self],
    ) -> Result<Self, SynthesisError> {
        if poly.len() == 0 {
            return Ok(Self::zero());
        }
        let mut result = poly.last().unwrap().clone();

        for coeff in poly.iter().rev().skip(1) {
            result = result.mul_add(cs, point, coeff)?;
        }

        Ok(result)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::bellman::plonk::better_better_cs::cs::*;
    extern crate boojum;
    
    use crate::bellman::pairing::bn256::{Bn256, Fr};
    use rand::Rng;
    use boojum::field::U64Representable;
    use boojum::field::SmallField;
    use boojum::field::Field;

    #[test]
    fn test_goldilocks_field() {
        let mut assembly = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();
        let _before = assembly.n();

        let mut rng = rand::thread_rng();
        let buffer_u64 = [0; 10].map(|_| rng.gen_range(0, GL::CHAR));
        let buffer_gl = buffer_u64.map(|x| GL::from_u64_unchecked(x));

        let buffer_circuit = buffer_u64.map(|x| 
            GoldilocksField::alloc_from_u64(&mut assembly, Some(x)).unwrap()
        );
        // let buffer_circuit = buffer_u64.map(|x| 
        //     GoldilocksField::constant(x)
        // );

        let circuit_sum = buffer_circuit[0].add(&mut assembly, &buffer_circuit[1]).unwrap();
        let mut gl_sum = buffer_gl[0];
        gl_sum.add_assign(&buffer_gl[1]);

        assert_eq!(Some(gl_sum.as_u64_reduced()), circuit_sum.into_u64());

        // add table for range check
        let columns3 = vec![
            PolyIdentifier::VariablesPolynomial(0),
            PolyIdentifier::VariablesPolynomial(1),
            PolyIdentifier::VariablesPolynomial(2),
        ];


        let name = BITWISE_LOGICAL_OPS_TABLE_NAME;
        let bitwise_logic_table = LookupTableApplication::new(
            name,
            TwoKeysOneValueBinopTable::<Bn256, XorBinop>::new(8, name),
            columns3.clone(),
            None,
            true,
        );
        assembly.add_table(bitwise_logic_table).unwrap();


        let circuit_fma = buffer_circuit[2].mul_add(
            &mut assembly, 
            &buffer_circuit[3], 
            &buffer_circuit[4]
        ).unwrap();

        let mut gl_fma = buffer_gl[2];
        gl_fma.mul_assign(&buffer_gl[3]);
        gl_fma.add_assign(&buffer_gl[4]);

        assert_eq!(Some(gl_fma.as_u64_reduced()), circuit_fma.into_u64());

        let mut repr = Fr::default().into_repr();
        repr.as_mut()[..3].copy_from_slice(&buffer_u64[5..8]);
        let combined = Num::alloc(
            &mut assembly,
            Some(Fr::from_repr(repr).unwrap())
        ).unwrap();

        let parts = GoldilocksField::from_num_to_multiple_with_reduction::<_, 3>(&mut assembly, combined).unwrap();

        for (i, part) in parts.into_iter().enumerate() {
            assert_eq!(Some(buffer_u64[5 + i]), (*part).into_u64());
        }

        assert!(assembly.is_satisfied());
    }

    #[test]
    fn test_goldilocks_field_extension() {
        let mut assembly = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();
        let _before = assembly.n();

        let mut rng = rand::thread_rng();
        let buffer_u64 = [0; 10].map(|_| rng.gen_range(0, GL::CHAR));

        let buffer_circuit = buffer_u64.map(|x| 
            GoldilocksField::alloc_from_u64(&mut assembly, Some(x)).unwrap()
        );
        // let buffer_circuit = buffer_u64.map(|x| 
        //     GoldilocksField::constant(x)
        // );

        // add table for range check
        let columns3 = vec![
            PolyIdentifier::VariablesPolynomial(0),
            PolyIdentifier::VariablesPolynomial(1),
            PolyIdentifier::VariablesPolynomial(2),
        ];

        let name = BITWISE_LOGICAL_OPS_TABLE_NAME;
        let bitwise_logic_table = LookupTableApplication::new(
            name,
            TwoKeysOneValueBinopTable::<Bn256, XorBinop>::new(8, name),
            columns3.clone(),
            None,
            true,
        );
        assembly.add_table(bitwise_logic_table).unwrap();

        let a = GoldilocksFieldExt::<Bn256>::from_coords([buffer_circuit[0], buffer_circuit[1]]);
        let b = GoldilocksFieldExt::<Bn256>::from_coords([buffer_circuit[2], buffer_circuit[3]]);
        let c = GoldilocksFieldExt::<Bn256>::from_coords([buffer_circuit[4], buffer_circuit[5]]);

        let fma_actual = a.mul_add(&mut assembly, &b, &c).unwrap();

        // calculating expected value
        let mut x_coord = a.inner[0].mul(&mut assembly, &b.inner[0]).unwrap();
        let mut part = a.inner[1].mul(&mut assembly, &b.inner[1]).unwrap();
        let non_residue = GoldilocksField::constant(GoldilocksFieldExt::<Bn256>::NON_RESIDUE);
        part = part.mul(&mut assembly, &non_residue).unwrap();
        x_coord = x_coord.add(&mut assembly, &part).unwrap();
        x_coord = x_coord.add(&mut assembly, &c.inner[0]).unwrap();

        let mut y_coord = a.inner[0].mul(&mut assembly, &b.inner[1]).unwrap();
        part = a.inner[1].mul(&mut assembly, &b.inner[0]).unwrap();
        y_coord = y_coord.add(&mut assembly, &part).unwrap();
        y_coord = y_coord.add(&mut assembly, &c.inner[1]).unwrap();

        let fma_expected = GoldilocksFieldExt::<Bn256>::from_coords([x_coord, y_coord]);

        fma_actual.enforce_equal(&mut assembly, &fma_expected).unwrap();

        let inversed = fma_actual.inverse(&mut assembly).unwrap();

        assert!(assembly.is_satisfied());
    }

}