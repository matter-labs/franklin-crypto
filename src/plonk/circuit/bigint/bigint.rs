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
    Width4MainGateWithDNextEquation,
    MainGateEquation,
    GateEquationInternal,
    GateEquation,
    LinearCombinationOfTerms,
    PolynomialMultiplicativeTerm,
    PolynomialInConstraint,
    TimeDilation,
    Coefficient,
    PlonkConstraintSystemParams
};

use num_bigint::BigUint;

use super::super::allocated_num::{AllocatedNum, Num};
use super::super::linear_combination::LinearCombination;

use super::{U16RangeConstraintinSystem, constraint_num_bits};

#[derive(Clone, Debug)]
pub struct Uint16<E: Engine>{
    var: AllocatedNum<E>,
    value: Option<u16>
}

fn two_in_16<F: PrimeField>() -> F {
    let mut repr = F::Repr::default();
    repr.as_mut()[0] = 1u64 << 16;

    F::from_repr(repr).unwrap()
}

impl<E: Engine> Uint16<E> {
    pub fn new_from_u16<CS: U16RangeConstraintinSystem<E>>(
        cs: &mut CS,
        value: Option<u16>
    ) -> Result<Self, SynthesisError> {
        
        let var = AllocatedNum::alloc(
            cs,
            || {
                let v = value.ok_or(SynthesisError::AssignmentMissing)?;
                let value_as_fr = E::Fr::from_str(&v.to_string()).unwrap();
                Ok(value_as_fr)
        })?;

        cs.constraint_u16(var.get_variable())?;

        Ok(Self {
            var,
            value
        })
    }

    pub fn add<CS: U16RangeConstraintinSystem<E>>(
        &self,
        cs: &mut CS,
        other: &Self,
    ) -> Result<(Self, Self), SynthesisError> {
        // first allocate the results
        let (new_value, carry_value) = match (self.value, other.value) {
            (Some(this_value), Some(other_value)) => {
                let result = (this_value as u32) + (other_value as u32);

                let new_value = result as u16;
                let carry_value = (result >> 16) as u16;

                (Some(new_value), Some(carry_value))
            },
            _ => {
                (None, None)
            }
        };

        let result = Self::new_from_u16(
            cs, 
            new_value
        )?;

        let carry = Self::new_from_u16(
            cs, 
            carry_value
        )?;

        // let mut lc = LinearCombination::<E>::zero();

        // first allocate result and carry
        let mut term = MainGateTerm::<E>::new();
        term.add_assign(ArithmeticTerm::from_variable(self.var.get_variable()));
        term.add_assign(ArithmeticTerm::from_variable(other.var.get_variable()));

        term.sub_assign(ArithmeticTerm::from_variable(result.var.get_variable()));
        term.sub_assign(ArithmeticTerm::from_variable_and_coeff(carry.var.get_variable(), two_in_16::<E::Fr>()));

        cs.allocate_main_gate(term)?;

        Ok((result, carry))
    }
 
    pub fn mul<CS: U16RangeConstraintinSystem<E>>(&self,
        cs: &mut CS,
        other: &Self,
    ) -> Result<(Self, Self), SynthesisError> {
        // first allocate the results
        let (new_value, carry_value) = match (self.value, other.value) {
            (Some(this_value), Some(other_value)) => {
                let result = (this_value as u32) * (other_value as u32);

                let new_value = result as u16;
                let carry_value = (result >> 16) as u16;

                (Some(new_value), Some(carry_value))
            },
            _ => {
                (None, None)
            }
        };

        let result = Self::new_from_u16(
            cs, 
            new_value
        )?;

        let carry = Self::new_from_u16(
            cs, 
            carry_value
        )?;

        // let mut lc = LinearCombination::<E>::zero();

        // first allocate result and carry
        let mut term = MainGateTerm::<E>::new();
        let mul_term = ArithmeticTerm::from_variable(self.var.get_variable()).mul_by_variable(other.var.get_variable());
        term.add_assign(mul_term);

        term.sub_assign(ArithmeticTerm::from_variable(result.var.get_variable()));
        term.sub_assign(ArithmeticTerm::from_variable_and_coeff(carry.var.get_variable(), two_in_16::<E::Fr>()));

        cs.allocate_main_gate(term)?;

        Ok((result, carry))
    }

    pub fn sub<CS: U16RangeConstraintinSystem<E>>(
        &self,
        cs: &mut CS,
        other: &Self,
    ) -> Result<(Self, Self), SynthesisError> {

        // a - b + borrow = c 

        // first allocate the results
        let (new_value, borrow_value) = match (self.value, other.value) {
            (Some(this_value), Some(other_value)) => {
                let result = 1u32 << 16 + (this_value as u32) - (other_value as u32);

                let new_value = result as u16;
                let borrow_value = if result >> 16 > 0 { 1u16 } else { 0u16 };

                (Some(new_value), Some(borrow_value))
            },
            _ => {
                (None, None)
            }
        };

        let result = Self::new_from_u16(
            cs, 
            new_value
        )?;

        let borrow_value = Self::new_from_u16(
            cs, 
            borrow_value
        )?;

        // let mut lc = LinearCombination::<E>::zero();

        // first allocate result and carry
        let mut term = MainGateTerm::<E>::new();
        term.add_assign(ArithmeticTerm::from_variable(self.var.get_variable()));
        term.add_assign(ArithmeticTerm::from_variable_and_coeff(borrow_value.var.get_variable(), two_in_16::<E::Fr>()));

        term.sub_assign(ArithmeticTerm::from_variable(result.var.get_variable()));
        term.sub_assign(ArithmeticTerm::from_variable(other.var.get_variable()));

        cs.allocate_main_gate(term)?;

        Ok((result, borrow_value))
    }
}

// in principle this is valid for both cases:
// when we represent some (field) element as a set of limbs
// that are power of two, or if it's a single element as in RNS

#[derive(Clone, Debug)]
pub struct LimbedRepresentationParameters<E: Engine> {
    pub limb_size_bits: usize,
    pub limb_max_value: BigUint,
    pub limb_max_intermediate_value: BigUint,
    pub limb_intermediate_value_capacity: usize,
    pub shift_left_by_limb_constant: E::Fr,
    pub shift_right_by_limb_constant: E::Fr,
    pub mul_two_constant: E::Fr,
    pub div_two_constant: E::Fr
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
            limb_max_intermediate_value: (BigUint::from(1u64) << intermediate_value_capacity) - BigUint::from(1u64),
            limb_intermediate_value_capacity: intermediate_value_capacity,
            shift_left_by_limb_constant,
            shift_right_by_limb_constant,
            mul_two_constant: two,
            div_two_constant,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum LimbType<E: Engine> {
    Constant(E::Fr),
    Variable(AllocatedLimb<E>)
}


// there is no equivalent yet in other parts of the gadget library,
// so we create an entity that carries a form a*X + b where
// X is either constant or variable, and `a` and `b` are constants
#[derive(Clone, Debug)]
pub struct Limb<E: Engine> {
    pub limb_type: LimbType<E>,
    pub max_value: BigUint,
    pub max_bits: usize,
    pub coeff: E::Fr,
    pub constant_term: E::Fr
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
    pub fn new_from_type(
        limb_type: LimbType<E>,
        max_value: BigUint,
        max_bits: usize,
    ) -> Self {
        Self {
            limb_type,
            max_value,
            max_bits,
            coeff: E::Fr::one(),
            constant_term: E::Fr::zero()
        }
    }

    pub fn scale(&mut self, factor: &E::Fr) {
        let coeff_bits = get_num_bits(factor);
        let coeff_as_bigint = fe_to_biguint(factor);

        self.max_value *= coeff_as_bigint;
        self.max_bits += coeff_bits;
        self.coeff.mul_assign(&factor);
        self.constant_term.mul_assign(&factor);
    } 

    pub fn unsafe_negate(&mut self) {
        self.max_value = BigUint::from(0u64);
        self.max_bits = 0;
        self.coeff.negate();
        self.constant_term.negate();
    } 

    pub fn add_assign_constant(&mut self, constant: &E::Fr) {
        self.constant_term.add_assign(&constant);
        self.max_bits += 1;
        self.max_value += fe_to_biguint(constant);
    }

    pub fn get_value(&self) -> BigUint {
        let mut v = match &self.limb_type {
            LimbType::Constant(v) => {
                fe_to_biguint(v)
            },
            LimbType::Variable(v) => {
                fe_to_biguint(&v.value)
            }
        };

        v *= fe_to_biguint(&self.coeff);
        v += fe_to_biguint(&self.constant_term);

        v
    }

    pub fn max_value(&self) -> BigUint {
        self.max_value.clone()
    }

    pub fn max_bits(&self) -> usize {
        self.max_bits
    }

    pub fn get_field_value(&self) -> E::Fr {
        debug_assert!(self.get_value() < repr_to_biguint::<E::Fr>(&E::Fr::char()), "self value = {}, char = {}", self.get_value().to_str_radix(16), E::Fr::char());

        let v = self.get_value();

        biguint_to_fe::<E::Fr>(v)
    }

    pub fn is_constant(&self) -> bool {
        match &self.limb_type {
            LimbType::Constant(..) => {
                true
            },
            LimbType::Variable(..) => {
                false
            }
        }
    }

    pub fn collapse_into_constant(&self) -> E::Fr {
        match &self.limb_type {
            LimbType::Constant(v) => {
                let mut value = *v;
                value.mul_assign(&self.coeff);
                value.add_assign(&self.constant_term);

                return value;
            },
            LimbType::Variable(..) => {
                panic!("tried to collapse on variable")
            }
        }
    }

    pub fn collapse_into_num<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS
    ) -> Result<Num<E>, SynthesisError> {
        match &self.limb_type {
            LimbType::Constant(v) => {
                let mut value = *v;
                value.mul_assign(&self.coeff);
                value.add_assign(&self.constant_term);

                return Ok(Num::Constant(value));
            },
            LimbType::Variable(var) => {
                let new_var_value = self.get_field_value();

                let allocated = AllocatedNum::alloc(
                    cs, 
                    ||{
                        Ok(new_var_value)
                    }
                )?;

                let mut term = MainGateTerm::<E>::new();
                let t0 = ArithmeticTerm::from_variable_and_coeff(self.get_variable(), self.coeff);
                let t1 = ArithmeticTerm::from_variable(allocated.get_variable());
                let c = ArithmeticTerm::constant(self.constant_term);

                term.add_assign(t0);
                term.sub_assign(t1);
                term.add_assign(c);

                cs.allocate_main_gate(term)?;

                return Ok(Num::Variable(allocated));
            }
        }
    }

    pub fn get_variable(&self) -> Variable {
        match &self.limb_type {
            LimbType::Constant(v) => {
                panic!("tried to get variable on constant")
            },
            LimbType::Variable(v) => {
                return v.variable;
            }
        }
    }

}

#[derive(Clone, Copy, Debug)]
pub struct AllocatedLimb<E: Engine> {
    pub(crate) variable: Variable,
    pub(crate) value: E::Fr
}

impl<E: Engine> AllocatedLimb<E> {
    pub fn alloc<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        value: E::Fr
    ) -> Result<Self, SynthesisError> {
        let var = cs.alloc(
            || {
                Ok(value)
            }
        )?;

        Ok(Self {
            variable: var,
            value
        })
    }   

    pub fn alloc_with_bit_limit<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        value: BigUint,
        num_bits: usize
    ) -> Result<Self, SynthesisError> {
        assert!(value.bits() <= num_bits);
        let val_as_fe = biguint_to_fe(value);
        let var = cs.alloc(
            || {
                Ok(val_as_fe)
            }
        )?;

        constraint_num_bits(cs, var, num_bits)?;

        Ok(Self {
            variable: var,
            value: val_as_fe
        })
    }   
}

pub(crate) fn repr_to_biguint<F: PrimeField>(repr: &F::Repr) -> BigUint {
    let mut b = BigUint::from(0u64);
    for &limb in repr.as_ref().iter().rev() {
        b <<= 64;
        b += BigUint::from(limb)
    }

    b
}

pub(crate) fn biguint_to_fe<F: PrimeField>(value: BigUint) -> F {
    F::from_str(&value.to_str_radix(10)).unwrap()
}

pub(crate) fn fe_to_biguint<F: PrimeField>(el: &F) -> BigUint {
    let repr = el.into_repr();

    repr_to_biguint::<F>(&repr)
}

pub(crate) fn fe_to_raw_biguint<F: PrimeField>(el: &F) -> BigUint {
    let repr = el.into_raw_repr();

    repr_to_biguint::<F>(&repr)
}

// pub(crate) fn fe_to_mont_limbs<F: PrimeField>(el: &F, bits_per_limb: usize) -> Vec<BigUint> {
//     let repr = el.into_raw_repr();

//     let fe = repr_to_biguint::<F>(&repr);

//     split_into_fixed_width_limbs(fe, bits_per_limb)
// }   

pub fn split_into_fixed_width_limbs(mut fe: BigUint, bits_per_limb: usize) -> Vec<BigUint> {
    let mut num_limbs = fe.bits() / bits_per_limb;
    if fe.bits() % bits_per_limb != 0 {
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


pub fn split_into_fixed_number_of_limbs(mut fe: BigUint, bits_per_limb: usize, num_limbs: usize) -> Vec<BigUint> {
    let mut limbs = Vec::with_capacity(num_limbs);

    let modulus = BigUint::from(1u64) << bits_per_limb;

    for _ in 0..num_limbs {
        let limb = fe.clone() % &modulus;
        limbs.push(limb);
        fe >>= bits_per_limb;
    }

    limbs
}

pub struct LimbedBigUint<'a, E: Engine> {
    pub(crate) params: &'a LimbedRepresentationParameters<E>,
    pub(crate) num_limbs: usize,
    pub(crate) limbs: Vec<Limb<E>>,
    pub(crate) is_constant: bool
}

impl<'a, E: Engine> LimbedBigUint<'a, E> {
    pub fn get_value(&self) -> BigUint {
        let shift = self.params.limb_size_bits;

        let mut result = BigUint::from(0u64);

        for l in self.limbs.iter().rev() {
            result <<= shift;
            result += l.get_value();
        }

        result
    }

    // pub fn reduce_if_necessary<CS: ConstraintSystem<E>>(
    //     &mut self,
    //     cs: &mut CS
    // ) -> Result<(), SynthesisError> {
    //     if self.is_constant {

    //     }
    // }
}



