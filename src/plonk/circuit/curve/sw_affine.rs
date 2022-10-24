use crate::bellman::pairing::{
    Engine,
    GenericCurveAffine,
    GenericCurveProjective,
};

use crate::bellman::plonk::better_better_cs::cs::*;

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
use super::super::bigint_new::range_checks::*;

use crate::plonk::circuit::{Assignment, boolean};

use super::super::allocated_num::{AllocatedNum, Num};
use super::super::linear_combination::LinearCombination;
use super::super::simple_term::Term;
use super::super::boolean::{Boolean, AllocatedBit};
use plonk::circuit::curve::endomorphism::EndomorphismParameters;

use num_bigint::BigUint;
use num_integer::Integer;

use super::super::bigint::field::*;
use super::super::bigint::bigint::*;
use plonk::circuit::curve::point_ram::*;

use plonk::circuit::bigint_new::BITWISE_LOGICAL_OPS_TABLE_NAME;
use plonk::circuit::hashes_with_tables::get_or_create_table;
use plonk::circuit::curve::table_for_mul::*;
use std::sync::Arc;

/// Returns a boolean of the sign of the number
pub fn sign_i64(i64: i64)-> Boolean{

    let a = i64::abs(i64);
    let diff = i64 - a;
    if diff == 0{
        Boolean::Constant(false)
    } else{
        Boolean::Constant(true)
    }
}
pub fn vec_bool_for_skew(number: usize, window: usize) -> (Vec<Option<bool>>, i64){
    let bits_str: &str = &format!("{number:b}");
    let char3: Vec<char> = bits_str.chars().collect::<Vec<_>>();

    let zero_count = window - bits_str.len();
    let mut vec_bool = vec![Some(false); zero_count];

    for i in char3.iter(){
        let bool = match i {
            '0' => false, 
            '1' => true,
            _ => panic!()
        };
        vec_bool.push(Some(bool));
        
    };

    let mut constanta: i64 = 0;
    for i in 0..vec_bool.len(){
        constanta *= 2;
        let high_bit = vec_bool[i].unwrap();
        let high_contribution = if high_bit {
            1
        } else{
            -1
        };

        constanta += high_contribution ;
    }

    (vec_bool, constanta)
}
/// Convert the number into skew form without the last element
/// Example: 7 -> 111 -> -1-1-1 -> -7
/// NoTe: depends on the width of the window specified in the input
/// because the program will fill the constant with zeros to convert to skew
pub fn vec_of_bit(number: usize, window: usize) -> (Vec<Option<bool>>, i64){
    // assert!(window != 1);
    let bits_str: &str = &format!("{number:b}");
    let char3: Vec<char> = bits_str.chars().collect::<Vec<_>>();

    let zero_count = window - bits_str.len();
    let mut vec_bool = vec![Some(false); zero_count];

    for i in char3.iter(){
        let bool = match i {
            '0' => false, 
            '1' => true,
            _ => panic!()
        };
        vec_bool.push(Some(bool));
        
    };

    let mut constanta: i64 = 0;
    for i in 0..vec_bool.len(){
        constanta *= 2;
        let high_bit = vec_bool[i].unwrap();
        let high_contribution = if high_bit {
            -1
        } else{
            1
        };

        constanta += high_contribution ;
    }

    (vec_bool, constanta)
    
}
pub fn vec_boolean_to_usize(boolean: Vec<Boolean>)-> usize{
    let mut number = 0;
    for boo in boolean.iter(){
        number *=2;
        if boo.get_value().unwrap()== true{
            number += 1 as usize;
        }
        
    }
    number
}

#[derive(Clone, Debug)]
pub struct AffinePoint<'a, E: Engine, G: GenericCurveAffine> where <G as GenericCurveAffine>::Base: PrimeField {
    pub x: FieldElement<'a, E, G::Base>,
    pub y: FieldElement<'a, E, G::Base>,
    pub value: Option<G>,
}

impl<'a, E: Engine, G: GenericCurveAffine> AffinePoint<'a, E, G> where <G as GenericCurveAffine>::Base: PrimeField {
    pub fn get_x(&self) -> FieldElement<'a, E, G::Base> {
        self.x.clone()
    }

    pub fn get_y(&self) -> FieldElement<'a, E, G::Base> {
        self.y.clone()
    }

    pub fn alloc<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        value: Option<G>,
        params: &'a RnsParameters<E, G::Base>
    ) -> Result<Self, SynthesisError> {
        let (x, y) = match value {
            Some(v) => {
                assert!(!v.is_zero());
                let (x, y) = v.into_xy_unchecked();

                (Some(x), Some(y))
            },
            None => {
                (None, None)
            }
        };

        let x = FieldElement::new_allocated_in_field(
            cs, 
            x, 
            params
        )?;

        let y = FieldElement::new_allocated_in_field(
            cs, 
            y, 
            params
        )?;

        // let x = FieldElement::new_allocated(
        //     cs, 
        //     x, 
        //     params
        // )?;

        // let y = FieldElement::new_allocated(
        //     cs, 
        //     y, 
        //     params
        // )?;

        let new = Self {
            x,
            y,
            value
        };

        Ok(new)
    }

    /// Get the last bit of the field element
    /// It's a witness y for point compression
    pub fn make_witness_y_odd<F: PrimeField>( value: Option<F>)->Option<bool>{
        let values = match value {
            Some(ref value) => {
                let last_bit = value.into_repr().as_ref()[0] % 2;

                match last_bit {
                    0 => Some(false),
                    1 => Some(true),
                    _ => unreachable!(),
                }
                
            }
            None => None
        };
        values
    }

    /// compression of a point for the most optimal number of gates using the xor table
    #[track_caller]
    pub fn point_compression<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(Boolean, RangeCheckDecomposition<E>), SynthesisError>{

        let table =  cs.get_table(BITWISE_LOGICAL_OPS_TABLE_NAME)?;
        let dummy = CS::get_dummy_variable();
        let range_of_linear_terms = CS::MainGate::range_of_linear_terms();
        
        let mut two = E::Fr::one();
        two.double();
        let two_inv = two.inverse().unwrap();

        let mut minus_one = E::Fr::one();
        minus_one.negate();
        let mut minus_two = two.clone();
        minus_two.negate(); 

        let y = self.y;
        let y_limbs = FieldElement::into_limbs(y.clone());
        let num_bits = y.representation_params.binary_limbs_bit_widths[0];
        // decomposition by field
        let rcd = constraint_bit_length_ext(cs,  &y_limbs[0].num.get_variable(), num_bits)?;

        let a = rcd.get_vars()[0];

        let y_odd_witness = Self::make_witness_y_odd(a.value);
        let y_is_odd = AllocatedBit::alloc(cs, y_odd_witness)?;
        let b = AllocatedNum::alloc(cs, || {
            let mut tmp = a.get_value().grab()?;
            tmp.sub_assign(&y_is_odd.get_value_as_field_element::<E>().grab()?);
            tmp.mul_assign(&two_inv);
            Ok(tmp)
        })?;
        let a_xor_b = match (a.get_value(), b.get_value()) {
            (Some(a_val), Some(b_val)) => {
                let res = table.query(&[a_val, b_val])?;
                AllocatedNum::alloc(cs, || Ok(res[0]))?
            },  
            (_, _) => AllocatedNum::alloc(cs, || Err(SynthesisError::AssignmentMissing))?
        };

        let y_is_odd_var = y_is_odd.get_variable();
        let vars = [
            a.get_variable(), b.get_variable(), a_xor_b.get_variable(), y_is_odd_var
        ];
        let coeffs = [E::Fr::one(), minus_two.clone(), E::Fr::zero(), E::Fr::one()];
        cs.begin_gates_batch_for_step()?;
        cs.apply_single_lookup_gate(&vars[..table.width()], table.clone())?;
        
        let gate_term = MainGateTerm::new();
        let (_, mut gate_coefs) = CS::MainGate::format_term(gate_term, dummy)?;
        for (idx, coef) in range_of_linear_terms.clone().zip(coeffs.iter()) {
            gate_coefs[idx] = *coef;
        }

        let mg = CS::MainGate::default();
        cs.new_gate_in_batch(&mg, &gate_coefs, &vars, &[])?;
        cs.end_gates_batch_for_step()?;

        let odd_bit = Boolean::from(y_is_odd);
        Ok((odd_bit, rcd))


    }

    // pub fn point_decompression<CS: ConstraintSystem<E>>(odd_bit: Boolean, cs: &mut CS, y_decomposition: RangeCheckDecomposition<E>)->Result<RangeCheckDecomposition<E>, SynthesisError>{
    //     let mut two = E::Fr::one();
    //     two.double();
    //     let two_inv = two.inverse().unwrap();
    //     let mut minus_two = two.clone();
    //     minus_two.negate(); 
    //     let table =  cs.get_table(BITWISE_LOGICAL_OPS_TABLE_NAME)?;
    //     let range_of_linear_terms = CS::MainGate::range_of_linear_terms();
    //     let dummy = CS::get_dummy_variable();
    //     let a = y_decomposition.get_vars()[0];
    //     let b = AllocatedNum::alloc(cs, || {
    //         let mut tmp = a.get_value().grab()?;
    //         tmp.sub_assign(&odd_bit.get_value_in_field::<E>().grab()?);
    //         tmp.mul_assign(&two_inv);
    //         Ok(tmp)
    //     })?;

    //     let a_xor_b = match (a.get_value(), b.get_value()) {
    //         (Some(a_val), Some(b_val)) => {
    //             let res = table.query(&[a_val, b_val])?;
    //             AllocatedNum::alloc(cs, || Ok(res[0]))?
    //         },  
    //         (_, _) => AllocatedNum::alloc(cs, || Err(SynthesisError::AssignmentMissing))?
    //     };

    //     let y_is_odd_var = odd_bit.get_variable().unwrap().get_variable();
    //     let vars = [
    //         a.get_variable(), b.get_variable(), a_xor_b.get_variable(), y_is_odd_var
    //     ];
    //     let coeffs = [E::Fr::one(), minus_two.clone(), E::Fr::zero(), E::Fr::one()];
    
    //     cs.begin_gates_batch_for_step()?;
    //     cs.apply_single_lookup_gate(&vars[..table.width()], table.clone())?;
        
    //     let gate_term = MainGateTerm::new();
    //     let (_, mut gate_coefs) = CS::MainGate::format_term(gate_term, dummy)?;
    //     for (idx, coef) in range_of_linear_terms.clone().zip(coeffs.iter()) {
    //         gate_coefs[idx] = *coef;
    //     }
    //     let mg = CS::MainGate::default();
    //     cs.new_gate_in_batch(&mg, &gate_coefs, &vars, &[])?;
    //     cs.end_gates_batch_for_step()?;
    
    //     Ok(y_decomposition)
    // }

    pub fn from_xy_unchecked(
        x: FieldElement<'a, E, G::Base>,
        y: FieldElement<'a, E, G::Base>,
    ) -> Self {
        let value = match (x.get_field_value(), y.get_field_value()) {
            (Some(x), Some(y)) => {
                Some(G::from_xy_unchecked(x, y))
            },
            _ => {
                None
            }
        };

        let new = Self {
            x,
            y,
            value
        };

        new
    }

    pub fn constant(
        value: G,
        params: &'a RnsParameters<E, G::Base>
    ) -> Self {
        assert!(!value.is_zero());
        let (x, y) = value.into_xy_unchecked();

        let x = FieldElement::new_constant(
            x,
            params
        );

        let y = FieldElement::new_constant(
            y,
            params
        );

        let new = Self {
            x,
            y,
            value: Some(value)
        };

        new
    }

    pub fn zero(
        params: &'a RnsParameters<E, G::Base>
    ) -> Self
    {
        let x = FieldElement::zero(params);
        let y = FieldElement::zero(params);

        let new = Self {
            x,
            y,
            value: Some(G::zero())
        };

        new
    }

    pub fn is_constant(&self) -> bool {
        self.x.is_constant() & self.y.is_constant()
    }

    pub fn get_value(&self) -> Option<G> {
        self.value
    }

    fn normalize_coordinates<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS
    ) -> Result<Self, SynthesisError> {
        let this_value = self.value;

        let this_x = self.x.force_reduce_close_to_modulus(cs)?;
        let this_y = self.y.force_reduce_close_to_modulus(cs)?;

        let this = Self {
            x: this_x,
            y: this_y,
            value: this_value
        };

        Ok(this)
    }

    pub fn equals<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        this: Self,
        other: Self,
    ) -> Result<(Boolean, (Self, Self)), SynthesisError> 
    {
        let this = this.normalize_coordinates(cs)?;
        let other = other.normalize_coordinates(cs)?;

        let this_x = this.x.clone();
        let this_y = this.y.clone();

        let other_x = other.x.clone();
        let other_y = other.y.clone();

        let x_check = FieldElement::equals_assuming_reduced(cs, this_x, other_x)?;
        let y_check = FieldElement::equals_assuming_reduced(cs, this_y, other_y)?;
        let equals = Boolean::and(cs, &x_check, &y_check)?;

        Ok((equals, (this, other)))
    }

    pub fn negate<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
    ) -> Result<(Self, Self), SynthesisError> {
        let this_value = self.get_value();

        let this_x = self.x;
        let this_y = self.y;

        let (this_y_negated, this_y) = this_y.negated(cs)?;
       
        let new_value = match this_value {
            Some(this) => {
                let mut tmp = this;
                tmp.negate();

                Some(tmp)
            },
            _ => None
        };
   
        let new = Self {
            x: this_x.clone(),
            y: this_y_negated,
            value: new_value
        };

        let this = Self {
            x: this_x,
            y: this_y,
            value: this_value
        };

        Ok((new, this))
    }

    pub fn conditionally_negate<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
        flag: &Boolean
    ) -> Result<(Self, (Self, Self)), SynthesisError> {
        let this_value = self.get_value();
        let this_value_nagated = this_value.map(|el| {
            let mut tmp = el;
            tmp.negate();

            tmp
        });
        let new_value = match (flag.get_value(), self.get_value()) {
            (Some(flag), Some(value)) => {
                let mut value = value;
                if flag {
                    value.negate();
                }

                Some(value)
            },
            _ => None
        };

        let this_x = self.x;
        let this_y = self.y;

        let (this_y_negated, this_y) = this_y.negated(cs)?;

        let (selected_y, (this_y_negated, this_y)) = FieldElement::select(cs, flag, this_y_negated, this_y)?;
       
        let new = Self {
            x: this_x.clone(),
            y: selected_y,
            value: new_value
        };

        let this = Self {
            x: this_x.clone(),
            y: this_y,
            value: this_value
        };

        let this_negated = Self {
            x: this_x,
            y: this_y_negated,
            value: this_value_nagated
        };

        Ok((new, (this, this_negated)))
    }

    #[track_caller]
    pub fn add_unequal<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
        other: Self
    ) -> Result<(Self, (Self, Self)), SynthesisError> {
        match (self.get_value(), other.get_value()) {
            (Some(first), Some(second)) => {
                assert!(first != second, "points are actually equal with value {}", first);
            },
            _ => {}
        }

        // only check that x - x' != 0 and go into the unchecked routine

        let this_x = self.x.clone();
        let other_x = other.x.clone();

        // don't divide by 0
        let (this_x, other_x) = FieldElement::enforce_not_equal(cs, this_x, other_x)?;

        let mut this = self;
        this.x = this_x;

        let mut other = other;
        other.x = other_x;

        this.add_unequal_unchecked(cs, other)
    }


    #[track_caller]
    pub fn add_unequal_unchecked<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
        other: Self
    ) -> Result<(Self, (Self, Self)), SynthesisError> {
        match (self.get_value(), other.get_value()) {
            (Some(first), Some(second)) => {
                assert!(first != second, "points are actually equal with value {}", first);
            },
            _ => {}
        }
        // since we are in a circuit we don't use projective coodinates cause inversions are
        // "cheap" in terms of constraints 

        // we also do not want to have branching here,
        // so this function implicitly requires that 
        // points are not equal

        // we need to calculate lambda = (y' - y)/(x' - x). We don't care about a particular
        // value of y' - y, so we don't add them explicitly and just use in inversion witness

        let this_value = self.get_value();
        let other_value = other.get_value();

        let this_x = self.x;
        let this_y = self.y;

        let other_x = other.x;
        let other_y = other.y;

        let (this_y_negated, this_y) = this_y.negated(cs)?;
        let (this_x_negated, this_x) = this_x.negated(cs)?;

        let (other_x_minus_this_x, (other_x, this_x_negated)) = other_x.add(cs, this_x_negated)?;

        let (other_x_negated, other_x) = other_x.negated(cs)?;

        let (lambda, (mut tmp, _)) = FieldElement::div_from_addition_chain(cs, vec![other_y, this_y_negated], other_x_minus_this_x)?;

        let this_y_negated = tmp.pop().unwrap();
        let other_y = tmp.pop().unwrap();

        // lambda^2 + (-x' - x)
        let (new_x, (lambda, _)) = lambda.clone().square_with_addition_chain(cs, vec![other_x_negated, this_x_negated])?;

        // lambda * (x - new_x) + (- y)

        let (this_x_minus_new_x, (this_x, new_x)) = this_x.sub(cs, new_x)?;
        let (new_y, _) = lambda.fma_with_addition_chain(cs, this_x_minus_new_x, vec![this_y_negated])?;

        let new_value = match (this_value, other_value) {
            (Some(this), Some(other)) => {
                assert!(this != other);
                let mut tmp = this.into_projective();
                tmp.add_assign_mixed(&other);

                Some(tmp.into_affine())
            },
            _ => None
        };
   
        let new = Self {
            x: new_x,
            y: new_y,
            value: new_value
        };

        let this = Self {
            x: this_x,
            y: this_y,
            value: this_value
        };

        let other = Self {
            x: other_x,
            y: other_y,
            value: other_value
        };

        Ok((new, (this, other)))
    }

    #[track_caller]
    pub fn sub_unequal<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
        other: Self
    ) -> Result<(Self, (Self, Self)), SynthesisError> {
        match (self.get_value(), other.get_value()) {
            (Some(first), Some(second)) => {
                assert!(first != second, "points are actually equal with value {}", first);
            },
            _ => {}
        }
        // since we are in a circuit we don't use projective coodinates cause inversions are
        // "cheap" in terms of constraints 

        // we also do not want to have branching here,
        // so this function implicitly requires that 
        // points are not equal

        // we need to calculate lambda = (y' - y)/(x' - x). We don't care about a particular
        // value of y' - y, so we don't add them explicitly and just use in inversion witness

        let this_value = self.get_value();
        let other_value = other.get_value();

        let this_x = self.x;
        let this_y = self.y;

        let other_x = other.x;
        let other_y = other.y;

        let (this_x, other_x) = FieldElement::enforce_not_equal(cs, this_x, other_x)?;

        let (this_y_negated, this_y) = this_y.negated(cs)?;
        let (this_x_negated, this_x) = this_x.negated(cs)?;

        let (other_x_minus_this_x, (other_x, this_x_negated)) = other_x.add(cs, this_x_negated)?;

        let (other_x_negated, other_x) = other_x.negated(cs)?;

        let (lambda, (mut tmp, _)) = FieldElement::div_from_addition_chain(cs, vec![other_y, this_y], other_x_minus_this_x)?;

        let this_y = tmp.pop().unwrap();
        let other_y = tmp.pop().unwrap();

        // lambda^2 + (-x' - x)
        let (new_x, (lambda, _)) = lambda.clone().square_with_addition_chain(cs, vec![other_x_negated, this_x_negated])?;

        // lambda * -(x - new_x) + (- y)

        let (new_x_minus_this_x, (new_x, this_x)) = new_x.sub(cs, this_x)?;
        
        let (new_y, _) = lambda.fma_with_addition_chain(cs, new_x_minus_this_x, vec![this_y_negated])?;

        let new_value = match (this_value, other_value) {
            (Some(this), Some(other)) => {
                assert!(this != other);
                let mut tmp = this.into_projective();
                let mut t0 = other;
                t0.negate();
                tmp.add_assign_mixed(&t0);

                Some(tmp.into_affine())
            },
            _ => None
        };
   
        let new = Self {
            x: new_x,
            y: new_y,
            value: new_value
        };

        let this = Self {
            x: this_x,
            y: this_y,
            value: this_value
        };

        let other = Self {
            x: other_x,
            y: other_y,
            value: other_value
        };


        Ok((new, (this, other)))
    }

    #[track_caller]
    pub fn double<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
    ) -> Result<(Self, Self), SynthesisError> {
        // since we are in a circuit we don't use projective coodinates cause inversions are
        // "cheap" in terms of constraints 

        // we also do not want to have branching here,
        // so this function implicitly requires that 
        // points are not equal

        // we need to calculate lambda = (y' - y)/(x' - x). We don't care about a particular
        // value of y' - y, so we don't add them explicitly and just use in inversion witness

        let this_value = self.get_value();

        let x = self.x;
        let y = self.y;

        let (x_squared, x) = x.square(cs)?;
        let (two_x_squared, x_squared) = x_squared.double(cs)?;
        let (three_x_squared, _) = two_x_squared.add(cs, x_squared)?;

        // Assume A == 0 for now

        let (two_y, y) = y.double(cs)?;

        let (lambda, _) = three_x_squared.div(cs, two_y)?;

        let (minus_x, x) = x.negated(cs)?;
        let (minus_y, y) = y.negated(cs)?;

        let (minus_two_x, _) = minus_x.double(cs)?;

        let (new_x, (lambda, _)) = lambda.square_with_addition_chain(cs, vec![minus_two_x])?;

        let (x_minus_new_x, (x, new_x)) = x.sub(cs, new_x)?;
        let (new_y, _) = lambda.fma_with_addition_chain(cs, x_minus_new_x, vec![minus_y])?;

        let new_value = match this_value {
            Some(this) => {
                let mut tmp = this.into_projective();
                tmp.double();

                Some(tmp.into_affine())
            },
            _ => None
        };
   
        let new = Self {
            x: new_x,
            y: new_y,
            value: new_value
        };

        let this = Self {
            x: x,
            y: y,
            value: this_value
        };


        Ok((new, this))
    }

    #[track_caller]
    pub fn double_and_add<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
        other: Self
    ) -> Result<(Self, (Self, Self)), SynthesisError> {
        // doubles self and adds other

        // even though https://www.researchgate.net/publication/283556724_New_Fast_Algorithms_for_Elliptic_Curve_Arithmetic_in_Affine_Coordinates exists
        // inversions are cheap, so Montgomery ladder is better

        // we can also try https://eprint.iacr.org/2015/1060.pdf

        // only check that x - x' != 0 and go into the unchecked routine

        let this_x = self.x.clone();
        let other_x = other.x.clone();

        let (this_x, other_x) = FieldElement::enforce_not_equal(cs, this_x, other_x)?;

        let mut this = self;
        this.x = this_x;
        let mut other = other;
        other.x = other_x;

        this.double_and_add_unchecked(cs, other)
    }


    #[track_caller]
    pub fn double_and_add_unchecked<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
        other: Self
    ) -> Result<(Self, (Self, Self)), SynthesisError> {
        // doubles self and adds other

        // even though https://www.researchgate.net/publication/283556724_New_Fast_Algorithms_for_Elliptic_Curve_Arithmetic_in_Affine_Coordinates exists
        // inversions are cheap, so Montgomery ladder is better

        // we can also try https://eprint.iacr.org/2015/1060.pdf

        let this_value = self.get_value();
        let other_value = other.get_value();

        let this_x = self.x;
        let this_y = self.y;

        let other_x = other.x;
        let other_y = other.y;

        let (this_y_negated, this_y) = this_y.negated(cs)?;
        let (this_x_negated, this_x) = this_x.negated(cs)?;

        let (other_x_minus_this_x, (other_x, this_x_negated)) = other_x.add(cs, this_x_negated)?;

        let (other_x_negated, other_x) = other_x.negated(cs)?;

        let (lambda, (mut tmp, _)) = FieldElement::div_from_addition_chain(cs, vec![other_y, this_y_negated], other_x_minus_this_x)?;

        let this_y_negated = tmp.pop().unwrap();
        let other_y = tmp.pop().unwrap();

        // lambda^2 + (-x' - x)
        let (new_x, (lambda, mut tmp)) = lambda.square_with_addition_chain(cs, vec![other_x_negated, this_x_negated])?;

        let this_x_negated = tmp.pop().unwrap();

        let (new_x_minus_this_x, (new_x, this_x)) = new_x.sub(cs, this_x)?;

        let (two_y, this_y) = this_y.double(cs)?;

        let (t0, _) = two_y.div(cs, new_x_minus_this_x)?;

        let (t1, (_, _)) = lambda.add(cs, t0)?;

        let (new_x_negated, _) = new_x.negated(cs)?;

        let (new_x, (t1, mut tmp)) = t1.square_with_addition_chain(cs, vec![this_x_negated, new_x_negated])?;

        let _ = tmp.pop().unwrap();
        let this_x_negated = tmp.pop().unwrap();

        let (new_x_minus_x, (new_x, _)) = new_x.add(cs, this_x_negated)?;

        let (new_y, _) = t1.fma_with_addition_chain(cs, new_x_minus_x, vec![this_y_negated])?;

        let new_value = match (this_value, other_value) {
            (Some(this), Some(other)) => {
                assert!(this != other);
                let mut tmp = this.into_projective();
                tmp.double();
                tmp.add_assign_mixed(&other);

                Some(tmp.into_affine())
            },
            _ => None
        };
   
        let new = Self {
            x: new_x,
            y: new_y,
            value: new_value
        };

        let this = Self {
            x: this_x,
            y: this_y,
            value: this_value
        };

        let other = Self {
            x: other_x,
            y: other_y,
            value: other_value
        };

        Ok((new, (this, other)))
    }
    #[track_caller]
    pub fn mul_by_fixed_point<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        window: usize,
        params: &'a RnsParameters<E, G::Base>,
        scalar: &Num<E>,
        bit_limit: Option<usize>
    )-> Result<Self, SynthesisError> {

        let columns3 = vec![
            PolyIdentifier::VariablesPolynomial(0), 
            PolyIdentifier::VariablesPolynomial(1), 
            PolyIdentifier::VariablesPolynomial(2)
        ];
        let name : &'static str = "table for affine point";
        let affine_point_coord_table = get_or_create_table(
            cs,
            name,
            || {
                LookupTableApplication::new(
                    name,
                    ScalarPointTable::new::<_, G>(window, name, params),
                    columns3.clone(),
                    None,
                    true
                )
            } 
        ).unwrap();
        let v = scalar.get_variable();

        let entries = decompose_allocated_num_into_skewed_table(cs, &v, bit_limit)?;


        let offset_generator = crate::constants::make_random_points_with_unknown_discrete_log_generic_proj::<G::Projective>(
            &crate::constants::MULTIEXP_DST[..], 
            1
        )[0];

        let generator = Self::constant(offset_generator, params);

        let entries_without_first_and_last = &entries[1..(entries.len() - 1)];
        let d = (bit_limit.unwrap()-1)/window; 
        let d_last_block = bit_limit.unwrap()-1 - d*window;
        // Break the scalar into chunks the size of the window width
        let chunks: Vec<Vec<Boolean>> = entries_without_first_and_last.chunks(window).map(|s| s.into()).collect();

        let mut num_doubles = 0;
        let mut pre_point = generator.clone();
        for i in 0..d{
            let scalar = chunks[i].clone();
            let point = AffinePoint::take_affine_point(cs, scalar, &affine_point_coord_table, params)?;
            let (acc, _)  = pre_point.clone().double_and_add(cs, point)?;
            num_doubles += 1;
            pre_point = acc;

        }

        let name : &'static str = "table for latest scalar";
        let affine_point_coord_table_last = get_or_create_table(
            cs,
            name,
            || {
                LookupTableApplication::new(
                    name,
                    ScalarPointTable::new::<_, G>(d_last_block, name, params),
                    columns3.clone(),
                    None,
                    true
                )
            } 
        ).unwrap();

        let scalar = chunks.last().unwrap();
        let point = AffinePoint::take_affine_point(cs, scalar.clone(), &affine_point_coord_table_last, params)?;
        let (acc, _)  = pre_point.clone().double_and_add(cs, point)?;
        num_doubles += 1;



        let (with_skew, _ ) = acc.clone().sub_unequal(cs, generator.clone())?;

        let last_entry = entries.last().unwrap();

        let with_skew_value = with_skew.get_value();
        let with_skew_x = with_skew.x;
        let with_skew_y = with_skew.y;

        let acc_value = acc.get_value();
        let acc_x = acc.x;
        let acc_y = acc.y;

        let final_value = match (with_skew_value, acc_value, last_entry.get_value()) {
            (Some(s_value), Some(a_value), Some(b)) => {
                if b {
                    Some(s_value)
                } else {
                    Some(a_value)
                }
            },
            _ => None
        };

        let (final_acc_x, _) = FieldElement::select(cs, last_entry, with_skew_x, acc_x)?;
        let (final_acc_y, _) = FieldElement::select(cs, last_entry, with_skew_y, acc_y)?;

        let shift = BigUint::from(1u64) << num_doubles;
        let as_scalar_repr = biguint_to_repr::<G::Scalar>(shift);
        let offset_value = offset_generator.mul(as_scalar_repr).into_affine();
        let offset = Self::constant(offset_value, params);

        let result = Self {
            x: final_acc_x,
            y: final_acc_y,
            value: final_value
        };

        let (result, _) = result.sub_unequal(cs, offset)?;

        Ok(result)

    }
    #[track_caller]
    pub fn take_affine_point<CS: ConstraintSystem<E>>(
        cs: &mut CS, 
        scalar: Vec<Boolean>, 
        table: &Arc<LookupTableApplication<E>>, 
        params: &'a RnsParameters<E, G::Base>
    )-> Result<Self, SynthesisError>{

        let key = vec_boolean_to_usize(scalar);

        let flag_low_f = Boolean::Constant(false);
        let flag_low_t = Boolean::Constant(true);

        let flag_high_f = Boolean::Constant(false);
        let flag_high_t = Boolean::Constant(true);

        let key = E::Fr::from_str(&format!("{}", (key))).unwrap();

        let low_limbs_x = Self::take_limb_of_point_from_table(cs, key, &flag_high_f, &flag_low_f, &table)?;
        let high_limbs_x = Self::take_limb_of_point_from_table(cs, key, &flag_high_f, &flag_low_t, &table)?;
        let low_limbs_y = Self::take_limb_of_point_from_table(cs, key, &flag_high_t, &flag_low_f, &table)?;
        let high_limbs_y = Self::take_limb_of_point_from_table(cs, key, &flag_high_t, &flag_low_t, &table)?;

        let limbs_x = [
            Num::Variable(low_limbs_x[0].clone()),
            Num::Variable(low_limbs_x[1].clone()),
            Num::Variable(high_limbs_x[0].clone()),
            Num::Variable(high_limbs_x[1].clone()),
        ];
        let limbs_y = [
            Num::Variable(low_limbs_y[0].clone()),
            Num::Variable(low_limbs_y[1].clone()),
            Num::Variable(high_limbs_y[0].clone()),
            Num::Variable(high_limbs_y[1].clone()),
        ];

        let x = FieldElement::from_single_limb_witnesses_unchecked(cs, &limbs_x, params)?;
        let y = FieldElement::from_single_limb_witnesses_unchecked(cs, &limbs_y, params)?;

        let g_value = match (x.get_field_value(), y.get_field_value()) {
            (Some(x), Some(y)) => {
                Some(G::from_xy_unchecked(x, y))
            },
            _ => {
                None
            }
        };

        let point = Self {
            x: x,
            y: y,
            value: g_value
        };

        Ok(point)

    }
    #[track_caller]
    pub fn take_affine_point_with_endo<CS: ConstraintSystem<E>>(
        cs: &mut CS, 
        scalar_for_flags: Vec<Boolean>, 
        scalar_2: Vec<Boolean>,
        table: &Arc<LookupTableApplication<E>>, 
        params: &'a RnsParameters<E, G::Base>
    )-> Result<Self, SynthesisError>{

        let scalar_1 = vec_boolean_to_usize(scalar_for_flags);
        let scalar_2 = vec_boolean_to_usize(scalar_2);
        let flag_f = Boolean::Constant(false);
        let flag_t = Boolean::Constant(true);

        let key_1 = E::Fr::from_str(&format!("{}", (scalar_1))).unwrap();
        let key_2 = E::Fr::from_str(&format!("{}", (scalar_2))).unwrap();
        // scalar || 000
        let low_limbs_x_0 = Self::take_limb_of_point_from_endotable(cs, key_1, key_2, &flag_f, &flag_f, &flag_f, &table)?;
        // scalar || 001
        let low_limbs_x_1 = Self::take_limb_of_point_from_endotable(cs, key_1, key_2, &flag_f, &flag_f, &flag_t, &table)?;
        // scalar || 010
        let high_limbs_x_0 = Self::take_limb_of_point_from_endotable(cs, key_1, key_2, &flag_f, &flag_t, &flag_f, &table)?;
        // scalar || 011
        let high_limbs_x_1 = Self::take_limb_of_point_from_endotable(cs, key_1, key_2, &flag_f, &flag_t, &flag_t, &table)?;
        // scalar || 100 
        let low_limbs_y_0 = Self::take_limb_of_point_from_endotable(cs, key_1, key_2, &flag_t, &flag_f, &flag_f, &table)?;
        // scalar || 101
        let low_limbs_y_1 = Self::take_limb_of_point_from_endotable(cs, key_1, key_2, &flag_t, &flag_f, &flag_t, &table)?;
        // scalar || 110
        let high_limbs_y_0 = Self::take_limb_of_point_from_endotable(cs, key_1, key_2, &flag_t, &flag_t, &flag_f, &table)?;
        // scalar || 111
        let high_limbs_y_1 = Self::take_limb_of_point_from_endotable(cs, key_1, key_2, &flag_t, &flag_t, &flag_t, &table)?;

        let limbs_x = [
            Num::Variable(low_limbs_x_0),
            Num::Variable(low_limbs_x_1),
            Num::Variable(high_limbs_x_0),
            Num::Variable(high_limbs_x_1),
        ];
        let limbs_y = [
            Num::Variable(low_limbs_y_0),
            Num::Variable(low_limbs_y_1),
            Num::Variable(high_limbs_y_0),
            Num::Variable(high_limbs_y_1),
        ];

        let x = FieldElement::from_single_limb_witnesses_unchecked(cs, &limbs_x, params)?;
        let y = FieldElement::from_single_limb_witnesses_unchecked(cs, &limbs_y, params)?;

        let g_value = match (x.get_field_value(), y.get_field_value()) {
            (Some(x), Some(y)) => {
                Some(G::from_xy_unchecked(x, y))
            },
            _ => {
                None
            }
        };

        let point = Self {
            x: x,
            y: y,
            value: g_value
        };

        Ok(point)

    }
    #[track_caller]
    pub fn take_limb_of_point_from_table<CS: ConstraintSystem<E>>(cs: &mut CS, key: E::Fr, flag_high: &Boolean, flag_low: &Boolean, table: &Arc<LookupTableApplication<E>>)-> Result< [AllocatedNum<E>; 2], SynthesisError>{
        let mut two = E::Fr::one();
        two.double();
        let mut minus_one = E::Fr::one();
        minus_one.negate();
        let mut minus_two = two.clone();
        minus_two.negate(); 

        let dummy = CS::get_dummy_variable();
        let range_of_linear_terms = CS::MainGate::range_of_linear_terms();


        let scalar_alloc = Num::alloc(cs, Some(key))?;
        // expr = 4*n + 2*flag_high + flag_low
        let mut expr_val = None;
        if let Some(scalar_alloc) = scalar_alloc.get_value() {
            let mut val = scalar_alloc;
            val.double();
            val.double();
            let mut flag = flag_high.get_value_in_field::<E>().grab()?;
            flag.double();
            val.add_assign(&flag);
            val.add_assign(&flag_low.get_value_in_field::<E>().grab()?);
            expr_val = Some(val);
        }

        let expr = Num::alloc(cs, expr_val)?;
        let res = table.query(&[expr_val.unwrap()])?;

        let chunk_low_0 = AllocatedNum::alloc(cs, || Ok(res[0]))?;
        let chunk_low_1 =  AllocatedNum::alloc(cs, || Ok(res[1]))?;
        let vars = [
            expr.get_variable().get_variable(), chunk_low_0.get_variable(), chunk_low_1.get_variable(), scalar_alloc.get_variable().get_variable()
        ];
        let coeffs = [E::Fr::one(),  E::Fr::zero(), E::Fr::zero(), minus_two.clone()];
        cs.begin_gates_batch_for_step()?;
        cs.apply_single_lookup_gate(&vars[..table.width()], table.clone())?;

        let gate_term = MainGateTerm::new();
        let (_, mut gate_coefs) = CS::MainGate::format_term(gate_term, dummy)?;
        for (idx, coef) in range_of_linear_terms.clone().zip(coeffs.iter()) {
            gate_coefs[idx] = *coef;
        }
        let index = CS::MainGate::index_for_constant_term();

        let mut minus_flag = flag_high.get_value_in_field::<E>().grab()?; 
        let mut val = minus_flag;
        val.double();
        val.add_assign(&flag_low.get_value_in_field::<E>().grab()?);
        minus_flag = val;


        minus_flag.negate();
        gate_coefs[index] = minus_flag;

        let mg = CS::MainGate::default();
        cs.new_gate_in_batch(&mg, &gate_coefs, &vars, &[])?;
        cs.end_gates_batch_for_step()?;



        Ok([chunk_low_0, chunk_low_1])
    }
    #[track_caller]
    pub fn take_limb_of_point_from_endotable<CS: ConstraintSystem<E>>(
        cs: &mut CS, 
        scalar_1: E::Fr, 
        scalar_2: E::Fr, 
        flag_1: &Boolean, 
        flag_2: &Boolean,
        flag_3: &Boolean, 
        table: &Arc<LookupTableApplication<E>>
    ) -> Result<AllocatedNum<E>, SynthesisError>{
        let mut two = E::Fr::one();
        two.double();
        let mut minus_one = E::Fr::one();
        minus_one.negate();
        let mut minus_two = two.clone();
        minus_two.negate(); 

        let dummy = CS::get_dummy_variable();
        let range_of_linear_terms = CS::MainGate::range_of_linear_terms();


        let scalar_alloc = Num::alloc(cs, Some(scalar_1))?;
        // expr = 8*n + 4*flag_1 + 2*flag_2 + flag_3
        let mut expr_val = None;
        if let Some(scalar_alloc) = scalar_alloc.get_value() {
            let mut val = scalar_alloc;
            val.double();
            val.double();
            val.double();
            let mut flag = flag_1.get_value_in_field::<E>().grab()?;
            flag.double();
            flag.double();
            val.add_assign(&flag);
            let mut flag_2 = flag_2.get_value_in_field::<E>().grab()?;
            flag_2.double();
            val.add_assign(&flag_2);
            val.add_assign(&flag_3.get_value_in_field::<E>().grab()?);
            expr_val = Some(val);
        }
        let expr = Num::alloc(cs, expr_val)?;
        let res = table.query(&[expr_val.unwrap(), scalar_2])?;

        let chunk = AllocatedNum::alloc(cs, || Ok(res[0]))?;
        let scalar_2 = AllocatedNum::alloc(cs, || Ok(scalar_2))?;
        let vars = [
            expr.get_variable().get_variable(), scalar_2.get_variable(), chunk.get_variable(), scalar_alloc.get_variable().get_variable()
        ];
        let coeffs = [E::Fr::one(),  E::Fr::zero(), E::Fr::zero(), minus_two.clone()];
        cs.begin_gates_batch_for_step()?;
        cs.apply_single_lookup_gate(&vars[..table.width()], table.clone())?;

        let gate_term = MainGateTerm::new();
        let (_, mut gate_coefs) = CS::MainGate::format_term(gate_term, dummy)?;
        for (idx, coef) in range_of_linear_terms.clone().zip(coeffs.iter()) {
            gate_coefs[idx] = *coef;
        }
        let index = CS::MainGate::index_for_constant_term();

        let mut minus_flag = flag_1.get_value_in_field::<E>().grab()?; 
        let mut val = minus_flag;
        val.double();
        val.double();
        let mut flag_2 = flag_2.get_value_in_field::<E>().grab()?;
        flag_2.double();
        val.add_assign(&flag_2);
        val.add_assign(&flag_3.get_value_in_field::<E>().grab()?);
        minus_flag = val;


        minus_flag.negate();
        gate_coefs[index] = minus_flag;

        let mg = CS::MainGate::default();
        cs.new_gate_in_batch(&mg, &gate_coefs, &vars, &[])?;
        cs.end_gates_batch_for_step()?;



        Ok(chunk)
    }


    pub fn mul_by_fixed_scalar<CS: ConstraintSystem<E>>(
        self,
        _cs: &mut CS,
        _scalar: &G::Scalar
    ) -> Result<(Self, Self), SynthesisError> {
        unimplemented!()
    }

    pub fn select<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        flag: &Boolean,
        first: Self,
        second: Self
    ) -> Result<(Self, (Self, Self)), SynthesisError> {

        let first_value = first.get_value();
        let second_value = second.get_value();
        let (x, (first_x, second_x)) = FieldElement::select(cs, flag, first.x, second.x)?;
        let (y, (first_y, second_y)) = FieldElement::select(cs, flag, first.y, second.y)?;

        let value = match (flag.get_value(), first_value, second_value) {
            (Some(true), Some(p), _) => Some(p),
            (Some(false), _, Some(p)) => Some(p),
            (_, _, _) => None
        };

        let selected = AffinePoint { 
            x : x, 
            y : y, 
            value 
        };

        let first = Self {
            x: first_x,
            y: first_y,
            value: first_value
        };

        let second = Self {
            x: second_x,
            y: second_y,
            value: second_value
        };

        Ok((selected, (first, second)))
    }

    #[track_caller]
    pub fn is_on_curve_for_zero_a<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
        curve_b: G::Base
    ) -> Result<(Boolean, Self), SynthesisError> {
        let params = self.x.representation_params;
        assert_eq!(curve_b, G::b_coeff());
        let b = FieldElement::new_constant(curve_b, params);

        let x = self.x;
        let y = self.y;
        let value = self.value;

        let (lhs, y) = y.square(cs)?;
        let (x_squared, x) = x.square(cs)?;
        let (x_cubed, (_, x)) = x_squared.mul(cs, x)?;

        let (rhs, _) = x_cubed.add(cs, b)?;

        // account for lazy addition
        let rhs = rhs.force_reduce_close_to_modulus(cs)?;
        let lhs = lhs.force_reduce_close_to_modulus(cs)?;

        let is_on_curve = FieldElement::equals_assuming_reduced(cs, lhs, rhs)?;

        // let is_on_curve = lhs.equals(cs, &rhs)?;
        // dbg!(lhs.get_field_value());
        // dbg!(rhs.get_field_value());

        let p = Self {
            x,
            y,
            value
        };

        Ok((is_on_curve, p))
    }

    pub fn mul_by_skewed_scalar_decomposition<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
        entries: &[Boolean],
        offset_generator: G,
    ) -> Result<(Self, Self), SynthesisError> {
        let params = self.x.representation_params;
        let this_value = self.get_value();
        let this_copy = self.clone();

        // offset generator allows us to be safe

        let generator = Self::constant(offset_generator, params);

        let (mut acc, (this, _)) = self.add_unequal(cs, generator)?;

        let mut x = this.x;
        let y = this.y;

        let entries_without_first_and_last = &entries[1..(entries.len() - 1)];

        let mut num_doubles = 0;

        let (minus_y, y) = y.negated(cs)?;

        for e in entries_without_first_and_last.iter() {
            let (selected_y, _) = FieldElement::select(cs, e, minus_y.clone(), y.clone())?;  
  
            let t_value = match (this_value, e.get_value()) {
                (Some(val), Some(bit)) => {
                    let mut val = val;
                    if bit {
                        val.negate();
                    }

                    Some(val)
                },
                _ => None
            };

            let t = Self {
                x: x,
                y: selected_y,
                value: t_value
            };

            let (new_acc, (_, t)) = acc.double_and_add(cs, t)?;

            num_doubles += 1;
            acc = new_acc;
            x = t.x;
        }

        let (with_skew, (acc, this)) = acc.sub_unequal(cs, this_copy)?;

        let last_entry = entries.last().unwrap();

        let with_skew_value = with_skew.get_value();
        let with_skew_x = with_skew.x;
        let with_skew_y = with_skew.y;

        let acc_value = acc.get_value();
        let acc_x = acc.x;
        let acc_y = acc.y;

        let final_value = match (with_skew_value, acc_value, last_entry.get_value()) {
            (Some(s_value), Some(a_value), Some(b)) => {
                if b {
                    Some(s_value)
                } else {
                    Some(a_value)
                }
            },
            _ => None
        };

        let (final_acc_x, _) = FieldElement::select(cs, last_entry, with_skew_x, acc_x)?;
        let (final_acc_y, _) = FieldElement::select(cs, last_entry, with_skew_y, acc_y)?;

        let mut scaled_offset = offset_generator.into_projective();
        for _ in 0..num_doubles {
            scaled_offset.double();
        }
        let offset = Self::constant(scaled_offset.into_affine(), params);

        let result = Self {
            x: final_acc_x,
            y: final_acc_y,
            value: final_value
        };

        let (result, _) = result.sub_unequal(cs, offset)?;

        Ok((result, this))
    }
}

impl<'a, E: Engine> AffinePoint<'a, E, E::G1Affine> {
    
    #[track_caller]
    pub fn mul_by_fixed_point_with_endo<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        window: usize,
        params: &'a RnsParameters<E, E::Fq>,
        scalar: &Num<E>,
        bit_limit: Option<usize>, 
        endomorphism_params: EndomorphismParameters<E>
    )-> Result<Self, SynthesisError> {

        let columns3 = vec![
            PolyIdentifier::VariablesPolynomial(0), 
            PolyIdentifier::VariablesPolynomial(1), 
            PolyIdentifier::VariablesPolynomial(2)
        ];
        let name : &'static str = "table for affine point with endomorphism";
        let affine_point_coord_table = get_or_create_table(
            cs,
            name,
            || {
                LookupTableApplication::new(
                    name,
                    ScalarPointEndoTable::<E>::new(window, name, params, endomorphism_params.clone()),
                    columns3.clone(),
                    None,
                    true
                )
            } 
        ).unwrap();
        let mut minus_one = E::Fr::one();
        minus_one.negate();
        let (k1, k2) = endomorphism_params.calculate_decomposition_num(cs, *scalar);

        // k = k1 - lambda * k2
        // lambda * k2 + k - k1 = 0
        let mut decomposition_lc = LinearCombination::zero();
        decomposition_lc.add_assign_number_with_coeff(&k2, endomorphism_params.lambda);
        decomposition_lc.add_assign_number_with_coeff(&scalar, E::Fr::one());
        decomposition_lc.add_assign_number_with_coeff(&k1, minus_one);
        decomposition_lc.enforce_zero(cs)?;

        let v_1 = k1.get_variable();
        let v_2 = k2.get_variable();

        let entries_1 = Self::decompose_into_binary_for_skew(cs, &v_1, bit_limit)?;
        let entries_2 = Self::decompose_into_binary_for_skew(cs, &v_2, bit_limit)?;

        let offset_generator = crate::constants::make_random_points_with_unknown_discrete_log_generic_proj::<E::G1>(
            &crate::constants::MULTIEXP_DST[..], 
            1
        )[0];

        let generator = Self::constant(offset_generator, params);

        let entries_1_without_first_and_last = &entries_1[1..(entries_1.len() - 1)];
        let entries_2_without_first_and_last = &entries_2[1..(entries_2.len() - 1)];
        let d = (bit_limit.unwrap()-1)/window; 
        let d_last_block = bit_limit.unwrap()-1 - d*window;
        // Break the scalar into chunks the size of the window width
        let chunks_1: Vec<Vec<Boolean>> = entries_1_without_first_and_last.chunks(window).map(|s| s.into()).collect();
        let chunks_2: Vec<Vec<Boolean>> = entries_2_without_first_and_last.chunks(window).map(|s| s.into()).collect();

        let mut num_doubles = 0;
        let mut pre_point = generator.clone();
        for i in 0..d{
            let scalar_for_flags = chunks_1[i].clone();
            let scalar_2 = chunks_2[i].clone();
            let point = AffinePoint::take_affine_point_with_endo(cs, scalar_for_flags, scalar_2, &affine_point_coord_table, params)?;
            let (acc, _)  = pre_point.clone().double_and_add(cs, point)?;
            num_doubles += 1;
            pre_point = acc;

        }
        let name : &'static str = "table for latest scalar with endo";
        let affine_point_coord_table_last = get_or_create_table(
            cs,
            name,
            || {
                LookupTableApplication::new(
                    name,
                    ScalarPointEndoTable::<E>::new(d_last_block, name, params, endomorphism_params),
                    columns3.clone(),
                    None,
                    true
                )
            } 
        ).unwrap();

        let scalar_for_flags = chunks_1.last().unwrap();
        let scalar_2 = chunks_2.last().unwrap();
        let point = AffinePoint::take_affine_point_with_endo(cs, scalar_for_flags.clone(), scalar_2.clone(), &affine_point_coord_table_last, params)?;
        let (acc, _)  = pre_point.clone().double_and_add(cs, point)?;
        num_doubles += 1;



        let (with_skew, _ ) = acc.clone().sub_unequal(cs, generator.clone())?;
        let last_entry_1 = entries_1.last().unwrap();
        let last_entry_2 = entries_2.last().unwrap();

        let with_skew_value = with_skew.get_value();
        let with_skew_x = with_skew.x;
        let with_skew_y = with_skew.y;

        let acc_value = acc.get_value();
        let acc_x = acc.x;
        let acc_y = acc.y;
        let last_entry = last_entry_1.get_value().unwrap() && last_entry_2.get_value().unwrap();
        let final_value = match (with_skew_value, acc_value, last_entry) {
            (Some(s_value), Some(a_value), b) => {
                if b {
                    Some(s_value)
                } else {
                    Some(a_value)
                }
            }
            _ => None,
        };

        let last_entry = Boolean::and(cs, last_entry_1, last_entry_2)?;
        let (final_acc_x, _) = FieldElement::select(cs, &last_entry, with_skew_x, acc_x)?;
        let (final_acc_y, _) = FieldElement::select(cs, &last_entry, with_skew_y, acc_y)?;

        let shift = BigUint::from(1u64) << num_doubles;
        let as_scalar_repr = biguint_to_repr::<E::Fr>(shift);
        let offset_value = offset_generator.mul(as_scalar_repr).into_affine();
        let offset = Self::constant(offset_value, params);

        let result = Self {
            x: final_acc_x,
            y: final_acc_y,
            value: final_value,
        };

        let (result, _) = result.sub_unequal(cs, offset)?;

        Ok(result)

    }

    fn decompose_into_binary_for_skew<CS: ConstraintSystem<E>>(    
        cs: &mut CS,
        num: &AllocatedNum<E>,
        bit_limit: Option<usize>
    )-> Result<Vec<Boolean>, SynthesisError> {
        let value = num.get_value();
        let bit_limit = if let Some(limit) = bit_limit {
            limit
            } else {
                E::Fr::NUM_BITS as usize
            };
        
        assert!(bit_limit > 0);
        
        
        // if value.is_none() {
        //     return vec![None; bit_limit+1];
        // }

        let mut bits = vec![None; bit_limit+1];
        let inner_bits = &mut bits[1..bit_limit];
        let value_repr = value.unwrap().into_repr();

        for (i, bit) in inner_bits.iter_mut().rev().enumerate() {
            let b = get_bit(&value_repr, i+1);
            if b {
                *bit = Some(true);
            } else {
                *bit = Some(false);
            }
        }
        
        // x = [y_-1, x_{n-1}, ..., x_0, y_n] where y_-1 = 0 always
        // and y_n = x_n * -1 always into dec repr
        bits[0] = Some(false);

        if *value_repr.as_ref().last().unwrap() == 0{
            *bits.last_mut().unwrap() = Some(false);
        } else{
            *bits.last_mut().unwrap() = Some(true);
        };

        let mut bits_boolean = Vec::with_capacity(bits.len());
        for b in bits {
            let a = Boolean::from(AllocatedBit::alloc(
                cs,
                b
            )?);
            bits_boolean.push(a);
        }
        Ok(bits_boolean)

    }
    
}

impl<'a, E: Engine> AffinePoint<'a, E, E::G1Affine> {

    /// Multiplication of a point by a scalar using endomorphism. The method uses a tree as a precomputation
    pub fn mul_split_scalar<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
        scalar: &Num<E>,
        endomorphism_params: EndomorphismParameters<E>,
        window: usize
    ) -> Result<(Self, Self), SynthesisError> {

        let params = self.x.representation_params;
        let (k1, k2, q_endo, bit_limit) = self.clone().endo_decomposition_scalar(cs, scalar, endomorphism_params)?;

        let v_1 = k1.get_variable();
        let v_2 = k2.get_variable();

        let entries_1 = decompose_allocated_num_into_skewed_table(cs, &v_1, bit_limit)?;
        let entries_2 = decompose_allocated_num_into_skewed_table(cs, &v_2, bit_limit)?;

        let offset_generator = crate::constants::make_random_points_with_unknown_discrete_log_proj::<E>(
            &crate::constants::MULTIEXP_DST[..], 
            1
        )[0];

        let generator = Self::constant(offset_generator, params);

        let (acc_1, (_, _)) = self.clone().add_unequal(cs, generator.clone())?;
        let (mut acc, (_, _)) = acc_1.add_unequal(cs, q_endo.clone())?;
        let entries_1_without_first_and_last = &entries_1[1..(entries_1.len() - 1)];
        let entries_1_without_first_and_last_vec: Vec<_> = entries_1_without_first_and_last.iter().collect(); 
        let entries_2_without_first_and_last = &entries_2[1..(entries_2.len() - 1)];
        let entries_2_without_first_and_last_vec: Vec<_> = entries_2_without_first_and_last.into_iter().collect(); 

        let mut num_doubles = 0;
        //precompute 
        let mut table =  self.clone().precomputation_for_tree_of_select(cs, &q_endo, window )?;
        let table_copy = table.clone();

        //We break the length of the scalar into window-sized blocks without the first and last bit
        let d = (bit_limit.unwrap()-2)/window; 
        let mut count =0;
        let mut flag = vec![];

        // Example:   010 000 101           window = 3
        //            110 001 010
        // flags contain [ 010110 000001 010010 ]
        // it's easier that way
        for _ in 0..d{
            for i in 0..window{
                flag.push(entries_2_without_first_and_last_vec[i + count])
            }
            for i in 0..window{
                flag.push(entries_1_without_first_and_last_vec[i + count])
            }
            count += window;
        }
        let d_last_block = bit_limit.unwrap()-2 - d*window ;
        let mut generated_table = vec![];

        let mut step = 0;
        for _ in 0..d{
            table = table_copy.clone();
            for j in 0..window*2{
                for i in (0..table.len()-1).step_by(2){
                    let (a, _) = AffinePoint::select(cs, flag[j+ step], table[i+1].clone(), table[i].clone())?;
                    generated_table.push(a);

                }
                table = generated_table.clone();
                generated_table = vec![];
            }


            let (new_acc, _) = acc.clone().double_and_add(cs, table[0].clone())?;

            num_doubles += 1;
            acc = new_acc;
            step += window*2;
        }


        let mut x = self.x.clone();
        let y = self.y.clone();
        let this_value = self.get_value();

        let (minus_y, y) = y.negated(cs)?;

        let x2 = q_endo.x.clone();
        let y2 = q_endo.y.clone();
        let this_value2 = q_endo.get_value();

        let (minus_y2, y2) = y2.negated(cs)?;

        // remember that we split the scalar into whole blocks with
        // the size of the window width. Therefore, we may have a tail left, 
        // which also needs to be counted
        let skip_len = entries_1_without_first_and_last_vec.len() - d_last_block;
        for (e1, e2) in entries_1_without_first_and_last_vec[skip_len..].into_iter().zip(entries_2_without_first_and_last_vec[skip_len..].into_iter()) {
            let (selected_y, _) = FieldElement::select(cs, e1, minus_y.clone(), y.clone())?;  
            let (selected_y2, _) = FieldElement::select(cs, e2, minus_y2.clone(), y2.clone())?;  
  
            let t_value = match (this_value, e1.get_value()) {
                (Some(val), Some(bit)) => {
                    let mut val = val;
                    if bit {
                        val.negate();
                    }

                    Some(val)
                },
                _ => None
            };
            let t_value2 = match (this_value2, e2.get_value()) {
                (Some(val), Some(bit)) => {
                    let mut val = val;
                    if bit {
                        val.negate();
                    }

                    Some(val)
                },
                _ => None
            };

            let t = Self {
                x: x,
                y: selected_y,
                value: t_value
            };
            let t2 = Self {
                x: x2.clone(),
                y: selected_y2,
                value: t_value2
            };

            let (p_q, _) = t.add_unequal(cs, t2)?;
            let (new_acc, (_, t)) = acc.double_and_add(cs, p_q)?;

            num_doubles += 1;
            acc = new_acc;
            x = t.x;
        }
        let (_with_skew, (acc, _this)) = acc.sub_unequal(cs, self.clone())?;
        let (with_skew, (acc, this)) = acc.sub_unequal(cs, q_endo.clone())?;
        let last_entry_1 = entries_1.last().unwrap();
        let last_entry_2 = entries_2.last().unwrap();

        let with_skew_value = with_skew.get_value();
        let with_skew_x = with_skew.x;
        let with_skew_y = with_skew.y;

        let acc_value = acc.get_value();
        let acc_x = acc.x;
        let acc_y = acc.y;
        let last_entry = last_entry_1.get_value().unwrap() && last_entry_2.get_value().unwrap();
        let final_value = match (with_skew_value, acc_value, last_entry) {
            (Some(s_value), Some(a_value), b) => {
                if b {
                    Some(s_value)
                } else {
                    Some(a_value)
                }
            }
            _ => None,
        };

        let last_entry = Boolean::and(cs, last_entry_1, last_entry_2)?;
        let (final_acc_x, _) = FieldElement::select(cs, &last_entry, with_skew_x, acc_x)?;
        let (final_acc_y, _) = FieldElement::select(cs, &last_entry, with_skew_y, acc_y)?;

        let shift = BigUint::from(1u64) << num_doubles;
        let as_scalar_repr = biguint_to_repr::<E::Fr>(shift);
        let offset_value = offset_generator.mul(as_scalar_repr).into_affine();
        let offset = Self::constant(offset_value, params);

        let result = Self {
            x: final_acc_x,
            y: final_acc_y,
            value: final_value,
        };

        let (result, _) = result.sub_unequal(cs, offset)?;

        Ok((result, this))

    }

    pub fn endo_decomposition_scalar<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
        scalar: &Num<E>,
        endomorphism_params: EndomorphismParameters<E> 
    )->Result<(Num<E>, Num<E>, Self, Option<usize>), SynthesisError>{
        let params = self.x.representation_params;
        let beta = FieldElement::new_constant(endomorphism_params.beta_g1, params);

        let endo_value = self.value.map(|el| endomorphism_params.apply_to_g1_point(el));

        let x = self.x.clone();
        let y = self.y.clone();

        let (x_beta, (_, _)) = x.mul(cs, beta.clone())?;
        let (y_negated, _) = y.negated(cs)?;

        let q_endo = AffinePoint {
            x: x_beta,
            y: y_negated,
            value: endo_value,
        };

        let bit_limit = Some(127 as usize);


        let mut minus_one = E::Fr::one();
        minus_one.negate();
        let (k1, k2) = endomorphism_params.calculate_decomposition_num(cs, *scalar);

        // k = k1 - lambda * k2
        // lambda * k2 + k - k1 = 0
        let mut decomposition_lc = LinearCombination::zero();
        decomposition_lc.add_assign_number_with_coeff(&k2, endomorphism_params.lambda);
        decomposition_lc.add_assign_number_with_coeff(&scalar, E::Fr::one());
        decomposition_lc.add_assign_number_with_coeff(&k1, minus_one);
        decomposition_lc.enforce_zero(cs)?;
        
        Ok((k1, k2, q_endo, bit_limit))
    }

    pub fn precomputation_for_tree_of_select<CS: ConstraintSystem<E>>(self,  cs: &mut CS, other: &Self, window: usize)-> Result<Vec<AffinePoint<'a, E, <E as Engine>::G1Affine>>, SynthesisError>{
        use plonk::circuit::hashes_with_tables::utils::u64_to_ff;
        let mut table  = vec![];
        let bit_window = (2 as u64).pow(window as u32);
        for i in 0..bit_window{
            let (_, number) = vec_of_bit(i as usize, window);
            let is_ne_flag = sign_i64(number);
            let unsign_nuber = i64::abs(number);
            let q_point = self.clone();
            let mut r_point :AffinePoint<E, <E as Engine>::G1Affine>;
            if unsign_nuber == 1 {
                r_point = q_point.clone();

            } else{
                (r_point, _) = q_point.clone().double(cs)?;

                for i in 0..unsign_nuber-2{

                    (r_point, _) = r_point.double_and_add(cs, q_point.clone())?;
                }
            }
        
            let y = r_point.y.clone();
            let (minus_y, y) = y.negated(cs)?;
            let (selected_y, _) = FieldElement::select(cs, &is_ne_flag, minus_y.clone(), y.clone())?;  
  
            let r_value = match (r_point.get_value(), is_ne_flag.get_value()) {
                (Some(val), Some(bit)) => {
                    let mut val = val;
                    if bit {
                        val.negate();
                    }

                    Some(val)
                },
                _ => None
            };

            let r = Self {
                x: r_point.x,
                y: selected_y,
                value: r_value
            };

            for j in 0..bit_window{
                let (_, number) = vec_of_bit(j as usize, window);
                let is_ne_flag = sign_i64(number);
                let unsign_nuber = i64::abs(number);
                let q_point = other.clone();
                let mut endo_point :AffinePoint<E, <E as Engine>::G1Affine>;

                if unsign_nuber == 1 {
                    endo_point = q_point.clone();
    
                } else{
                    (endo_point, _) = q_point.clone().double(cs)?;
    
                    for _ in 0..unsign_nuber-2{
    
                        (endo_point, _) = endo_point.double_and_add(cs, q_point.clone())?;
                    }
                }

                let y = endo_point.y.clone();
                let (minus_y, y) = y.negated(cs)?;
                let (selected_y, _) = FieldElement::select(cs, &is_ne_flag, minus_y.clone(), y.clone())?;  
      
                let endo_value = match (endo_point.get_value(), is_ne_flag.get_value()) {
                    (Some(val), Some(bit)) => {
                        let mut val = val;
                        if bit {
                            val.negate();
                        }
    
                        Some(val)
                    },
                    _ => None
                };
    
                let endo = Self {
                    x: endo_point.x,
                    y: selected_y,
                    value: endo_value
                };

                let (c, (_, _)) = r.clone().add_unequal(cs, endo )?;
                table.push(c);

            }
        }
        Ok(table.to_vec())
    }

    pub fn precomputation_for_ram<CS: ConstraintSystem<E>>(self,  cs: &mut CS, other: &Self, window: usize, memory: &mut Memory<'a, E, <E as Engine>::G1Affine>)-> Result<(), SynthesisError>{
        use plonk::circuit::hashes_with_tables::utils::u64_to_ff;
        let bit_window = (2 as u64).pow(window as u32);
        let mut count = 0 as u64;
        for i in 0..bit_window{
            let (_, number) = vec_of_bit(i as usize, window);
            let is_ne_flag = sign_i64(number);
            let unsign_nuber = i64::abs(number);
            let q_point = self.clone();
            let mut r_point :AffinePoint<E, <E as Engine>::G1Affine>;
            if unsign_nuber == 1 {
                r_point = q_point.clone();

            } else{
                (r_point, _) = q_point.clone().double(cs)?;

                for _ in 0..unsign_nuber-2{

                    (r_point, _) = r_point.double_and_add(cs, q_point.clone())?;
                }
            }

            let y = r_point.y.clone();
            let (minus_y, y) = y.negated(cs)?;
            let (selected_y, _) = FieldElement::select(cs, &is_ne_flag, minus_y.clone(), y.clone())?;  
  
            let r_value = match (r_point.get_value(), is_ne_flag.get_value()) {
                (Some(val), Some(bit)) => {
                    let mut val = val;
                    if bit {
                        val.negate();
                    }

                    Some(val)
                },
                _ => None
            };

            let r = Self {
                x: r_point.x,
                y: selected_y,
                value: r_value
            };

            for j in 0..bit_window{
                let (_, number) = vec_of_bit(j as usize, window);
                let is_ne_flag = sign_i64(number);
                let unsign_nuber = i64::abs(number);
                let q_point = other.clone();
                let mut endo_point :AffinePoint<E, <E as Engine>::G1Affine>;

                if unsign_nuber == 1 {
                    endo_point = q_point.clone();
    
                } else{
                    (endo_point, _) = q_point.clone().double(cs)?;
    
                    for _ in 0..unsign_nuber-2{
    
                        (endo_point, _) = endo_point.double_and_add(cs, q_point.clone())?;
                    }
                }

                let y = endo_point.y.clone();
                let (minus_y, y) = y.negated(cs)?;
                let (selected_y, _) = FieldElement::select(cs, &is_ne_flag, minus_y.clone(), y.clone())?;  
      
                let endo_value = match (endo_point.get_value(), is_ne_flag.get_value()) {
                    (Some(val), Some(bit)) => {
                        let mut val = val;
                        if bit {
                            val.negate();
                        }
    
                        Some(val)
                    },
                    _ => None
                };
    
                let endo = Self {
                    x: endo_point.x,
                    y: selected_y,
                    value: endo_value
                };

                let (c, (_, _)) = r.clone().add_unequal(cs, endo )?;

                let number: E::Fr = u64_to_ff(count);
                let address = Num::Variable(AllocatedNum::alloc(cs, || Ok(number))?);
                memory.block.push((address, c.clone()));
                memory.insert_witness(address, c);
                count+=1;
            }
        }
        Ok(())
    }
    #[track_caller]
    pub fn mul_split_scalar_2<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
        scalar: &Num<E>,
        endomorphism_params: EndomorphismParameters<E>,
        window: usize
    ) -> Result<(Self, Self), SynthesisError> {
        let params = self.x.representation_params;
        let (k1, k2, q_endo, bit_limit) = self.clone().endo_decomposition_scalar(cs, scalar, endomorphism_params)?;

        let v_1 = k1.get_variable();
        let v_2 = k2.get_variable();

        let entries_1 = decompose_allocated_num_into_skewed_table(cs, &v_1, bit_limit)?;
        let entries_2 = decompose_allocated_num_into_skewed_table(cs, &v_2, bit_limit)?;

        let offset_generator = crate::constants::make_random_points_with_unknown_discrete_log_proj::<E>(
            &crate::constants::MULTIEXP_DST[..], 
            1
        )[0];

        let generator = Self::constant(offset_generator, params);

        let (acc_1, (_, _)) = self.clone().add_unequal(cs, generator.clone())?;

        let entries_1_without_first_and_last = &entries_1[1..(entries_1.len() - 1)];
        let entries_1_without_first_and_last_vec: Vec<_> = entries_1_without_first_and_last.iter().collect(); 
        let entries_2_without_first_and_last = &entries_2[1..(entries_2.len() - 1)];
        let entries_2_without_first_and_last_vec: Vec<_> = entries_2_without_first_and_last.into_iter().collect(); 

        let mut num_doubles = 0;

        let (mut acc, (_, _)) = acc_1.add_unequal(cs, q_endo.clone())?;

        //precompute 
        let mut memory =  Memory::new();
 
        self.clone().precomputation_for_ram(cs, &q_endo, window, &mut memory)?;

        //We break the length of the scalar into window-sized blocks without the first and last bit
        let d = (bit_limit.unwrap()-2)/window; 
        use plonk::circuit::bigint_new::compute_shifts;
        let shifts = compute_shifts::<E::Fr>();
        let mut step = 0;
        // We create addresses according to the following scheme: 
        // First, there is a simple numbering addres = 0 + 1, 0+2, 0+3 ... 0+n where n is bits of the window.
        // Then the following happens. Just as a new cycle begins, we add n and add to the current number.
        // This is done to prevent address overlap. For example: 2 P + 3 Q addrx will be 5 and 3 P + 2 Q addrx will also be 5.
        // According to our trick, when n = 4, the address will be 11 in the first case, and 14 in the second.
        let mut minus_one = E::Fr::one();
        minus_one.negate();
        for l in 0..d{
            let mut lc = LinearCombination::zero();
            let mut i = window;
            for m in 0..window{
                i-= 1;
                lc.add_assign_boolean_with_coeff(entries_1_without_first_and_last_vec[m+step], shifts[window+i]);
                lc.add_assign_boolean_with_coeff(entries_2_without_first_and_last_vec[m+step], shifts[i]);

            }
            let addres = lc.into_num(cs)?;

            let point = unsafe { memory.read_and_alloc(cs, addres, params)? };
            let (new_acc, (_, t)) = acc.clone().double_and_add(cs, point)?;

            num_doubles += 1;
            acc = new_acc;
            step += window;
        };


        let mut x = self.x.clone();
        let y = self.y.clone();
        let this_value = self.get_value();

        let (minus_y, y) = y.negated(cs)?;

        let x2 = q_endo.x.clone();
        let y2 = q_endo.y.clone();
        let this_value2 = q_endo.get_value();

        let (minus_y2, y2) = y2.negated(cs)?;

        // remember that we split the scalar into whole blocks with
        // the size of the window width. Therefore, we may have a tail left, 
        // which also needs to be counted
        let d_last_block = bit_limit.unwrap()-2 - d*window ;
        let skip_len = entries_1_without_first_and_last_vec.len() - d_last_block;
        for (e1, e2) in entries_1_without_first_and_last_vec[skip_len..].into_iter().zip(entries_2_without_first_and_last_vec[skip_len..].into_iter()) {
            let (selected_y, _) = FieldElement::select(cs, e1, minus_y.clone(), y.clone())?;  
            let (selected_y2, _) = FieldElement::select(cs, e2, minus_y2.clone(), y2.clone())?;  
  
            let t_value = match (this_value, e1.get_value()) {
                (Some(val), Some(bit)) => {
                    let mut val = val;
                    if bit {
                        val.negate();
                    }

                    Some(val)
                },
                _ => None
            };
            let t_value2 = match (this_value2, e2.get_value()) {
                (Some(val), Some(bit)) => {
                    let mut val = val;
                    if bit {
                        val.negate();
                    }

                    Some(val)
                },
                _ => None
            };

            let t = Self {
                x: x,
                y: selected_y,
                value: t_value
            };
            let t2 = Self {
                x: x2.clone(),
                y: selected_y2,
                value: t_value2
            };

            let (p_q, _) = t.add_unequal(cs, t2)?;
            let (new_acc, (_, t)) = acc.double_and_add(cs, p_q)?;

            num_doubles += 1;
            acc = new_acc;
            x = t.x;
        }

        let (_with_skew, (acc, _this)) = acc.sub_unequal(cs, self.clone())?;
        let (with_skew, (acc, this)) = acc.sub_unequal(cs, q_endo.clone())?;
        let last_entry_1 = entries_1.last().unwrap();
        let last_entry_2 = entries_2.last().unwrap();

        let with_skew_value = with_skew.get_value();
        let with_skew_x = with_skew.x;
        let with_skew_y = with_skew.y;

        let acc_value = acc.get_value();
        let acc_x = acc.x;
        let acc_y = acc.y;
        let last_entry = last_entry_1.get_value().unwrap() && last_entry_2.get_value().unwrap();
        let final_value = match (with_skew_value, acc_value, last_entry) {
            (Some(s_value), Some(a_value), b) => {
                if b {
                    Some(s_value)
                } else {
                    Some(a_value)
                }
            }
            _ => None,
        };

        let last_entry = Boolean::and(cs, last_entry_1, last_entry_2)?;
        let (final_acc_x, _) = FieldElement::select(cs, &last_entry, with_skew_x, acc_x)?;
        let (final_acc_y, _) = FieldElement::select(cs, &last_entry, with_skew_y, acc_y)?;

        let shift = BigUint::from(1u64) << num_doubles;
        let as_scalar_repr = biguint_to_repr::<E::Fr>(shift);
        let offset_value = offset_generator.mul(as_scalar_repr).into_affine();
        let offset = Self::constant(offset_value, params);

        let result = Self {
            x: final_acc_x,
            y: final_acc_y,
            value: final_value,
        };

        let (result, _) = result.sub_unequal(cs, offset)?;

        memory.waksman_permutation(cs, window)?;
        Ok((result, this))

    }
    #[track_caller]
    pub fn mul_split_scalar_entry_point<CS: ConstraintSystem<E>, R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>>(
        self,
        cs: &mut CS,
        scalar: &Num<E>,
        endomorphism_params: EndomorphismParameters<E>,
        window: usize, 
        round_function: &R
    ) -> Result<(Self, Self), SynthesisError> {
        let params = self.x.representation_params;
        let (k1, k2, q_endo, bit_limit) = self.clone().endo_decomposition_scalar(cs, scalar, endomorphism_params)?;
        let v_1 = k1.get_variable();
        let v_2 = k2.get_variable();

        let entries_1 = decompose_allocated_num_into_skewed_table(cs, &v_1, bit_limit)?;
        let entries_2 = decompose_allocated_num_into_skewed_table(cs, &v_2, bit_limit)?;
        let offset_generator = crate::constants::make_random_points_with_unknown_discrete_log_proj::<E>(
            &crate::constants::MULTIEXP_DST[..], 
            1
        )[0];

        let generator = Self::constant(offset_generator, params);

        let (acc_1, (_, _)) = self.clone().add_unequal(cs, generator.clone())?;

        let entries_1_without_first_and_last = &entries_1[1..(entries_1.len() - 1)];
        let entries_1_without_first_and_last_vec: Vec<_> = entries_1_without_first_and_last.iter().collect(); 
        let entries_2_without_first_and_last = &entries_2[1..(entries_2.len() - 1)];
        let entries_2_without_first_and_last_vec: Vec<_> = entries_2_without_first_and_last.into_iter().collect(); 

        let mut num_doubles = 0;

        let (mut acc, (_, _)) = acc_1.add_unequal(cs, q_endo.clone())?;

        //precompute 
        let mut memory =  Memory::new();
 
        self.clone().precomputation_for_ram(cs, &q_endo, window, &mut memory)?;

        //We break the length of the scalar into window-sized blocks without the first and last bit
        let d = (bit_limit.unwrap()-2)/window; 
        use plonk::circuit::bigint_new::compute_shifts;
        let shifts = compute_shifts::<E::Fr>();
        let mut step = 0;
        // We create addresses according to the following scheme: 
        // First, there is a simple numbering addres = 0 + 1, 0+2, 0+3 ... 0+n where n is bits of the window.
        // Then the following happens. Just as a new cycle begins, we add n and add to the current number.
        // This is done to prevent address overlap. For example: 2 P + 3 Q addrx will be 5 and 3 P + 2 Q addrx will also be 5.
        // According to our trick, when n = 4, the address will be 11 in the first case, and 14 in the second.
        let mut minus_one = E::Fr::one();
        minus_one.negate();
        for l in 0..d{
            let mut lc = LinearCombination::zero();
            let mut i = window;
            for m in 0..window{
                i-= 1;
                lc.add_assign_boolean_with_coeff(entries_1_without_first_and_last_vec[m+step], shifts[window+i]);
                lc.add_assign_boolean_with_coeff(entries_2_without_first_and_last_vec[m+step], shifts[i]);

            }
            let addres = lc.into_num(cs)?;

            let point = unsafe { memory.read_and_alloc(cs, addres, params)? };
            let (new_acc, (_, t)) = acc.clone().double_and_add(cs, point)?;
            num_doubles += 1;
            acc = new_acc;
            step += window;
        };
        memory.ram_permutation_entry_point(cs, round_function)?;

        let mut x = self.x.clone();
        let y = self.y.clone();
        let this_value = self.get_value();

        let (minus_y, y) = y.negated(cs)?;

        let x2 = q_endo.x.clone();
        let y2 = q_endo.y.clone();
        let this_value2 = q_endo.get_value();

        let (minus_y2, y2) = y2.negated(cs)?;

        // remember that we split the scalar into whole blocks with
        // the size of the window width. Therefore, we may have a tail left, 
        // which also needs to be counted
        let d_last_block = bit_limit.unwrap()-2 - d*window ;
        let skip_len = entries_1_without_first_and_last_vec.len() - d_last_block;
        for (e1, e2) in entries_1_without_first_and_last_vec[skip_len..].into_iter().zip(entries_2_without_first_and_last_vec[skip_len..].into_iter()) {
            let (selected_y, _) = FieldElement::select(cs, e1, minus_y.clone(), y.clone())?;  
            let (selected_y2, _) = FieldElement::select(cs, e2, minus_y2.clone(), y2.clone())?;  
  
            let t_value = match (this_value, e1.get_value()) {
                (Some(val), Some(bit)) => {
                    let mut val = val;
                    if bit {
                        val.negate();
                    }

                    Some(val)
                },
                _ => None
            };
            let t_value2 = match (this_value2, e2.get_value()) {
                (Some(val), Some(bit)) => {
                    let mut val = val;
                    if bit {
                        val.negate();
                    }

                    Some(val)
                },
                _ => None
            };

            let t = Self {
                x: x,
                y: selected_y,
                value: t_value
            };
            let t2 = Self {
                x: x2.clone(),
                y: selected_y2,
                value: t_value2
            };

            let (p_q, _) = t.add_unequal(cs, t2)?;
            let (new_acc, (_, t)) = acc.double_and_add(cs, p_q)?;

            num_doubles += 1;
            acc = new_acc;
            x = t.x;
        }

        let (_with_skew, (acc, _this)) = acc.sub_unequal(cs, self.clone())?;
        let (with_skew, (acc, this)) = acc.sub_unequal(cs, q_endo.clone())?;
        let last_entry_1 = entries_1.last().unwrap();
        let last_entry_2 = entries_2.last().unwrap();

        let with_skew_value = with_skew.get_value();
        let with_skew_x = with_skew.x;
        let with_skew_y = with_skew.y;

        let acc_value = acc.get_value();
        let acc_x = acc.x;
        let acc_y = acc.y;
        let last_entry = last_entry_1.get_value().unwrap() && last_entry_2.get_value().unwrap();
        let final_value = match (with_skew_value, acc_value, last_entry) {
            (Some(s_value), Some(a_value), b) => {
                if b {
                    Some(s_value)
                } else {
                    Some(a_value)
                }
            }
            _ => None,
        };

        let last_entry = Boolean::and(cs, last_entry_1, last_entry_2)?;
        let (final_acc_x, _) = FieldElement::select(cs, &last_entry, with_skew_x, acc_x)?;
        let (final_acc_y, _) = FieldElement::select(cs, &last_entry, with_skew_y, acc_y)?;

        let shift = BigUint::from(1u64) << num_doubles;
        let as_scalar_repr = biguint_to_repr::<E::Fr>(shift);
        let offset_value = offset_generator.mul(as_scalar_repr).into_affine();
        let offset = Self::constant(offset_value, params);

        let result = Self {
            x: final_acc_x,
            y: final_acc_y,
            value: final_value,
        };

        let (result, _) = result.sub_unequal(cs, offset)?;

        Ok((result, this))

    }


    #[track_caller]
    pub fn mul<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
        scalar: &Num::<E>,
        bit_limit: Option<usize>
    ) -> Result<(Self, Self), SynthesisError> {
        if let Some(value) = scalar.get_value() {
            assert!(!value.is_zero(), "can not multiply by zero in the current approach");
        }
        if scalar.is_constant() {
            return self.mul_by_fixed_scalar(cs, &scalar.get_value().unwrap());
        }

        let params = self.x.representation_params;
        let this_value = self.get_value();
        let this_copy = self.clone();

        // scalar is not constant, so we first decompose it

        let v = scalar.get_variable();

        let entries = decompose_allocated_num_into_skewed_table(cs, &v, bit_limit)?;
        // we add a random point to the accumulator to avoid having zero anywhere (with high probability)
        // and unknown discrete log allows us to be "safe"

        let offset_generator = crate::constants::make_random_points_with_unknown_discrete_log_proj::<E>(
            &crate::constants::MULTIEXP_DST[..], 
            1
        )[0];

        let generator = Self::constant(offset_generator, params);

        let (mut acc, (this, _)) = self.add_unequal(cs, generator)?;

        let mut x = this.x;
        let y = this.y;

        let entries_without_first_and_last = &entries[1..(entries.len() - 1)];

        let mut num_doubles = 0;

        let (minus_y, y) = y.negated(cs)?;

        for e in entries_without_first_and_last.iter() {
            let (selected_y, _) = FieldElement::select(cs, e, minus_y.clone(), y.clone())?;  
  
            let t_value = match (this_value, e.get_value()) {
                (Some(val), Some(bit)) => {
                    let mut val = val;       
                    if bit {
                        val.negate();
                    }

                    Some(val)
                },
                _ => None
            };

            let t = Self {
                x: x,
                y: selected_y,
                value: t_value
            };

            let (new_acc, (_, t)) = acc.double_and_add(cs, t)?;

            num_doubles += 1;
            acc = new_acc;
            x = t.x;
        }

        let (with_skew, (acc, this)) = acc.sub_unequal(cs, this_copy)?;

        let last_entry = entries.last().unwrap();

        let with_skew_value = with_skew.get_value();
        let with_skew_x = with_skew.x;
        let with_skew_y = with_skew.y;

        let acc_value = acc.get_value();
        let acc_x = acc.x;
        let acc_y = acc.y;

        let final_value = match (with_skew_value, acc_value, last_entry.get_value()) {
            (Some(s_value), Some(a_value), Some(b)) => {
                if b {
                    Some(s_value)
                } else {
                    Some(a_value)
                }
            },
            _ => None
        };

        let (final_acc_x, _) = FieldElement::select(cs, last_entry, with_skew_x, acc_x)?;
        let (final_acc_y, _) = FieldElement::select(cs, last_entry, with_skew_y, acc_y)?;

        let shift = BigUint::from(1u64) << num_doubles;
        let as_scalar_repr = biguint_to_repr::<E::Fr>(shift);
        let offset_value = offset_generator.mul(as_scalar_repr).into_affine();
        let offset = Self::constant(offset_value, params);

        let result = Self {
            x: final_acc_x,
            y: final_acc_y,
            value: final_value
        };

        let (result, _) = result.sub_unequal(cs, offset)?;

        Ok((result, this))
    }

    #[track_caller]
    pub fn multiexp<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        scalars: &[Num::<E>],
        points: &[Self],
        bit_limit: Option<usize>
    ) -> Result<Self, SynthesisError> {
        assert_eq!(scalars.len(), points.len());

        let params = points[0].x.representation_params;

        let mut entries_per_scalar = Vec::with_capacity(scalars.len());

        let mut top_limit = 0;

        for s in scalars.iter() {
            let v = s.get_variable();
            let entries = decompose_allocated_num_into_skewed_table(cs, &v, bit_limit)?;
            if top_limit == 0 {
                top_limit = entries.len() - 1;
            } else {
                assert_eq!(top_limit, entries.len() - 1);
            }
            entries_per_scalar.push(entries);
        }

        assert!(top_limit > 0);

        let table = super::multiexp_table::MultiexpTable::new(cs, points)?;

        // we add a random point to the accumulator to avoid having zero anywhere (with high probability)
        // and unknown discrete log allows us to be "safe"

        let offset_generator = crate::constants::make_random_points_with_unknown_discrete_log_proj::<E>(
            &crate::constants::MULTIEXP_DST[..], 
            1
        )[0];

        let generator = Self::constant(offset_generator, params);

        let base = table.make_base(cs)?;

        let (mut acc, _) = base.add_unequal(cs, generator)?;

        let mut current_round_entries = Vec::with_capacity(scalars.len());
        let mut num_doubles = 0;

        for bit_idx in 1..top_limit {
            for entry in entries_per_scalar.iter() {
                let e = entry[bit_idx].clone();
                current_round_entries.push(e);
            }

            assert_eq!(current_round_entries.len(), table.width);

            let q = table.lookup_for_skewed_entries(cs, &current_round_entries)?;

            let (new_acc, _) = acc.double_and_add(cs, q)?;

            num_doubles += 1;
            acc = new_acc;

            current_round_entries.truncate(0);
        }

        // subtract

        for (p, entry) in points.iter().zip(entries_per_scalar.into_iter()) {
            let (with_skew, (acc_original, _)) = acc.sub_unequal(cs, p.clone())?;

            let last_entry = entry.last().unwrap();

            let with_skew_value = with_skew.get_value();
            let with_skew_x = with_skew.x;
            let with_skew_y = with_skew.y;

            let acc_value = acc_original.get_value();
            let acc_x = acc_original.x;
            let acc_y = acc_original.y;

            let final_value = match (with_skew_value, acc_value, last_entry.get_value()) {
                (Some(s_value), Some(a_value), Some(b)) => {
                    if b {
                        Some(s_value)
                    } else {
                        Some(a_value)
                    }
                },
                _ => None
            };

            let (final_acc_x, _) = FieldElement::select(cs, last_entry, with_skew_x, acc_x)?;
            let (final_acc_y, _) = FieldElement::select(cs, last_entry, with_skew_y, acc_y)?;

            let result = Self {
                x: final_acc_x,
                y: final_acc_y,
                value: final_value
            };

            acc = result;
        }
        
        let shift = BigUint::from(1u64) << num_doubles;
        let as_scalar_repr = biguint_to_repr::<E::Fr>(shift);
        let offset_value = offset_generator.mul(as_scalar_repr).into_affine();
        let offset = Self::constant(offset_value, params);

        let (result, _) = acc.sub_unequal(cs, offset)?;
        
        Ok(result)
    }

    #[track_caller]
    pub fn multiexp_using_endomorphism<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        scalars: &[Num::<E>],
        points: &[Self],
        endo_parameters: &super::endomorphism::EndomorphismParameters<E>,
    ) -> Result<Self, SynthesisError> {
        assert_eq!(scalars.len(), points.len());

        let params = points[0].x.representation_params;

        let beta = FieldElement::new_constant(endo_parameters.beta_g1, params);

        let mut points_for_k1 = Vec::with_capacity(points.len());
        let mut points_for_k2 = Vec::with_capacity(points.len());
        for p in points.iter() {
            let value = p.value;
            let endo_value = value.map(|el| endo_parameters.apply_to_g1_point(el));

            let x = p.x.clone();
            let y = p.y.clone();

            let (x_beta, (x, _)) = x.mul(cs, beta.clone())?;
            let (y_negated, y) = y.negated(cs)?;

            let p = AffinePoint {
                x,
                y, 
                value,
            };

            let p_endo = AffinePoint {
                x: x_beta,
                y: y_negated, 
                value: endo_value,
            };

            points_for_k1.push(p);
            points_for_k2.push(p_endo);
        }

        let mut scalar_k1s = Vec::with_capacity(scalars.len());
        let mut scalar_k2s = Vec::with_capacity(scalars.len());

        let mut minus_one = E::Fr::one();
        minus_one.negate();

        for s in scalars.iter() {
            let (k1, k2) = match s {
                Num::Constant(_c) => {
                    unreachable!("multiplication by constant it not yet supported");
                    // let (k1, k2) = endo_parameters.calculate_decomposition(*c);

                    // (Num::Constant(k1), Num::Constant(k1))
                },
                Num::Variable(var) => {
                    let (k1_val, k2_val) = if let Some(val) = var.get_value() {
                        let (k1, k2) = endo_parameters.calculate_decomposition(val);

                        let mut reconstruction = k2;
                        reconstruction.mul_assign(&endo_parameters.lambda);
                        reconstruction.negate();
                        reconstruction.add_assign(&k1);
            
                        assert_eq!(reconstruction, val);

                        (Some(k1), Some(k2))
                    } else {
                        (None, None)
                    };
                    let k1 = Num::Variable(AllocatedNum::alloc(cs, || Ok(*k1_val.get()?))?);
                    let k2 = Num::Variable(AllocatedNum::alloc(cs, || Ok(*k2_val.get()?))?);

                    // k = k1 - lambda * k2
                    // lambda * k2 + k - k1 = 0
                    let mut decomposition_lc = LinearCombination::zero();
                    decomposition_lc.add_assign_number_with_coeff(&k2, endo_parameters.lambda);
                    decomposition_lc.add_assign_number_with_coeff(&s, E::Fr::one());
                    decomposition_lc.add_assign_number_with_coeff(&k1, minus_one);

                    decomposition_lc.enforce_zero(cs)?;

                    (k1, k2)
                }
            };

            scalar_k1s.push(k1);
            scalar_k2s.push(k2);
        }

        let mut full_points_vector = points_for_k1;
        full_points_vector.extend(points_for_k2);

        let mut full_scalars_vector = scalar_k1s;
        full_scalars_vector.extend(scalar_k2s);

        Self::multiexp(cs, &full_scalars_vector, &full_points_vector, Some(endo_parameters.target_scalar_width))
    }
}

#[track_caller]
pub fn decompose_allocated_num_into_skewed_table<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    num: &AllocatedNum<E>,
    bit_limit: Option<usize>
) -> Result<Vec<Boolean>, SynthesisError> {
    let bit_values = compute_skewed_naf_table(&num.get_value(), bit_limit);
    let mut bits = Vec::with_capacity(bit_values.len());
    for b in bit_values {
        let a = Boolean::from(AllocatedBit::alloc(
            cs,
            b
        )?);
        bits.push(a);
    }

    // constraint reconstruction

    {
        let mut reconstructed = Term::<E>::zero();

        let bits_without_skew = &bits[0..(bits.len() - 1)];

        let mut chunks = bits_without_skew.chunks_exact(2);

        let mut two = E::Fr::one();
        two.double();

        let mut minus_one = E::Fr::one();
        minus_one.negate();

        for c in &mut chunks {
            reconstructed.scale(&two);
            reconstructed.scale(&two);

            let mut high_contribution = Term::from_boolean(&c[0]);
            high_contribution.scale(&two);
            high_contribution.negate();
            high_contribution.add_constant(&E::Fr::one());
            high_contribution.scale(&two);

            let mut low_contribution = Term::from_boolean(&c[1]);
            low_contribution.scale(&two);
            low_contribution.negate();
            low_contribution.add_constant(&E::Fr::one());

            reconstructed = reconstructed.add_multiple(cs, &[high_contribution, low_contribution])?;
        }

        let remainder = chunks.remainder();
        if remainder.len() == 1 {
            let last = &remainder[0];
            reconstructed.scale(&two);
            // we should add +1 if bit is false or add -1 if bit is true,
            // so we make false = 0 -> 1 - 2*0 = 1
            // true = 1 -> 1 - 2*1 = -1
            let mut contribution = Term::from_boolean(&last);
            contribution.scale(&two);
            contribution.negate();
            contribution.add_constant(&E::Fr::one());

            reconstructed = reconstructed.add(cs, &contribution)?;
        }

        let skew_bit = bits.last().unwrap();
        // we only subtract if true
        let mut contribution = Term::from_boolean(&skew_bit);
        contribution.negate();

        reconstructed = reconstructed.add(cs, &contribution)?;

        let as_num = reconstructed.collapse_into_num(cs)?;
        let v = as_num.get_variable();
        v.enforce_equal(cs, num)?;
    }

    Ok(bits)
}

fn get_bit<R: PrimeFieldRepr>(repr: &R, bit: usize) -> bool {
    let limb_index = bit / 64;
    let mask = 1u64 << (bit % 64);

    repr.as_ref()[limb_index] & mask > 0
}

#[track_caller]
fn compute_skewed_naf_table<F: PrimeField>(value: &Option<F>, bit_limit: Option<usize>) -> Vec<Option<bool>> {
    let bit_limit = if let Some(limit) = bit_limit {
        limit
    } else {
        F::NUM_BITS as usize
    };

    assert!(bit_limit > 0);

    if value.is_none() {
        return vec![None; bit_limit+1];
    }

    let value = value.unwrap();
    let mut value_repr = value.into_repr();

    let one_repr = F::one().into_repr();

    let mut bits = vec![None; bit_limit+1];

    if get_bit(&value_repr, 0) == false {
        *bits.last_mut().unwrap() = Some(true);
        value_repr.add_nocarry(&one_repr);
    } else {
        *bits.last_mut().unwrap() = Some(false);
    }

    let inner_bits = &mut bits[1..bit_limit];

    for (i, bit) in inner_bits.iter_mut().rev().enumerate() {
        let b = get_bit(&value_repr, i+1);
        if b {
            *bit = Some(false);
        } else {
            *bit = Some(true);
        }
    }

    bits[0] = Some(false);

    // sanity check

    {
        let mut two = F::one();
        two.double();

        let mut minus_one = F::one();
        minus_one.negate();

        let mut reconstructed = F::zero();

        let even_limit = (bit_limit / 2) * 2;

        for i in (0..even_limit).step_by(2) {
            reconstructed.double();
            reconstructed.double();

            let high_bit = bits[i].unwrap();
            let mut high_contribution = if high_bit {
                minus_one
            } else {
                F::one()
            };
            high_contribution.double();

            let low_bit = bits[i+1].unwrap();
            let low_contribution = if low_bit {
                minus_one
            } else {
                F::one()
            };

            reconstructed.add_assign(&high_contribution);
            reconstructed.add_assign(&low_contribution);
        }

        if bit_limit & 1 == 1 {
            reconstructed.double();

            let last_bit = bits[bit_limit-1].unwrap();
            if last_bit {
                reconstructed.add_assign(&minus_one);
            } else {
                reconstructed.add_assign(&F::one());
            };
        }

        if bits.last().unwrap().unwrap() {
            reconstructed.add_assign(&minus_one);
        }

        assert_eq!(reconstructed, value);
    }

    bits
}

fn simulate_multiplication<E: Engine>(point: E::G1Affine, scalar: E::Fr, num_bits: Option<usize>) {
    let entries = compute_skewed_naf_table(&Some(scalar), num_bits);
    let base = point;

    let offset_generator = crate::constants::make_random_points_with_unknown_discrete_log_proj::<E>(
        &crate::constants::MULTIEXP_DST[..], 
        1
    )[0];

    let mut accumulator = base.into_projective();
    accumulator.add_assign_mixed(&offset_generator);

    println!("initial acculumator = {}", accumulator.into_affine());

    let mut reconstructed_scalar = 1;

    let mut base_negated = base;
    base_negated.negate();

    let entries_without_first_and_last = &entries[1..(entries.len() - 1)];

    let mut num_doubles = 0;

    for e in entries_without_first_and_last.iter() {
        let b = e.unwrap();
        accumulator.double();
        reconstructed_scalar *= 2;
        if b {
            accumulator.add_assign_mixed(&base_negated);
            reconstructed_scalar -= 1;
        } else {
            accumulator.add_assign_mixed(&base);
            reconstructed_scalar += 1;
        }

        println!("Acc = {}", accumulator.into_affine());

        num_doubles += 1;
    }

    let last_entry = entries.last().unwrap();

    let mut tmp = accumulator;
    tmp.add_assign_mixed(&base_negated);
    println!("Skewed accumulator = {}", tmp);

    if last_entry.unwrap() {
        accumulator.add_assign_mixed(&base_negated);
        reconstructed_scalar -= 1;
    };
    println!("Selected accumulator = {}", accumulator);

    let shift = BigUint::from(1u64) << num_doubles;
    let as_scalar_repr = biguint_to_repr::<E::Fr>(shift);
    let mut offset = offset_generator.mul(as_scalar_repr).into_affine();
    offset.negate();

    let mut result = accumulator;
    result.add_assign_mixed(&offset);

    let result = result.into_affine();

    println!("Reconstructed scalar = {}", reconstructed_scalar);

    println!("Result = {}", result);
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::plonk::circuit::*;
    use crate::bellman::pairing::bn256::{Fq, Bn256, Fr, G1Affine};

    #[test]
    fn test_add_on_random_witnesses(){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

        for i in 0..100 {
            let mut cs = TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();

            let a_f: G1Affine = rng.gen();
            let b_f: G1Affine = rng.gen();
            let a = AffinePoint::alloc(
                &mut cs, 
                Some(a_f), 
                &params
            ).unwrap();

            let b = AffinePoint::alloc(
                &mut cs, 
                Some(b_f), 
                &params
            ).unwrap();
    
            let (result, (a, b)) = a.add_unequal(&mut cs, b).unwrap();

            assert!(cs.is_satisfied());

            let x_fe = result.x.get_field_value().unwrap();
            let y_fe = result.y.get_field_value().unwrap();

            let (x, y) = result.get_value().unwrap().into_xy_unchecked();

            assert_eq!(x_fe, x, "x coords mismatch");
            assert_eq!(y_fe, y, "y coords mismatch");

            let (x, y) = a_f.into_xy_unchecked();
            assert_eq!(a.x.get_field_value().unwrap(), x, "x coords mismatch");
            assert_eq!(a.y.get_field_value().unwrap(), y, "y coords mismatch");

            let (x, y) = b_f.into_xy_unchecked();
            assert_eq!(b.x.get_field_value().unwrap(), x, "x coords mismatch");
            assert_eq!(b.y.get_field_value().unwrap(), y, "y coords mismatch");

            if i == 0 {
                let base = cs.n();
                let _ = a.add_unequal(&mut cs, b).unwrap();
                println!("Single addition taken {} gates", cs.n() - base);
            }
        }
    }


    #[test]
    fn test_add_with_constant_on_random_witnesses(){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

        for i in 0..100 {
            let mut cs = TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();

            let a_f: G1Affine = rng.gen();
            let b_f: G1Affine = rng.gen();
            let a = AffinePoint::alloc(
                &mut cs, 
                Some(a_f), 
                &params
            ).unwrap();

            let b = AffinePoint::constant(
                b_f,
                &params
            );
    
            let (result, (a, b)) = a.add_unequal(&mut cs, b).unwrap();

            assert!(cs.is_satisfied());

            let x_fe = result.x.get_field_value().unwrap();
            let y_fe = result.y.get_field_value().unwrap();

            let (x, y) = result.get_value().unwrap().into_xy_unchecked();

            assert_eq!(x_fe, x, "x coords mismatch");
            assert_eq!(y_fe, y, "y coords mismatch");

            let (x, y) = a_f.into_xy_unchecked();
            assert_eq!(a.x.get_field_value().unwrap(), x, "x coords mismatch");
            assert_eq!(a.y.get_field_value().unwrap(), y, "y coords mismatch");

            let (x, y) = b_f.into_xy_unchecked();
            assert_eq!(b.x.get_field_value().unwrap(), x, "x coords mismatch");
            assert_eq!(b.y.get_field_value().unwrap(), y, "y coords mismatch");

            if i == 0 {
                let base = cs.n();
                let _ = a.add_unequal(&mut cs, b).unwrap();
                println!("Single addition with constant taken {} gates", cs.n() - base);
            }
        }
    }

    #[test]
    fn test_sub_on_random_witnesses(){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

        for i in 0..100 {
            let mut cs = TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();

            let a_f: G1Affine = rng.gen();
            let b_f: G1Affine = rng.gen();
            let a = AffinePoint::alloc(
                &mut cs, 
                Some(a_f), 
                &params
            ).unwrap();

            let b = AffinePoint::alloc(
                &mut cs, 
                Some(b_f), 
                &params
            ).unwrap();
    
            let (result, (a, b)) = a.sub_unequal(&mut cs, b).unwrap();

            assert!(cs.is_satisfied());

            let x_fe = result.x.get_field_value().unwrap();
            let y_fe = result.y.get_field_value().unwrap();

            let (x, y) = result.get_value().unwrap().into_xy_unchecked();

            assert_eq!(x_fe, x, "x coords mismatch");
            assert_eq!(y_fe, y, "y coords mismatch");

            let (x, y) = a_f.into_xy_unchecked();
            assert_eq!(a.x.get_field_value().unwrap(), x, "x coords mismatch");
            assert_eq!(a.y.get_field_value().unwrap(), y, "y coords mismatch");

            let (x, y) = b_f.into_xy_unchecked();
            assert_eq!(b.x.get_field_value().unwrap(), x, "x coords mismatch");
            assert_eq!(b.y.get_field_value().unwrap(), y, "y coords mismatch");

            if i == 0 {
                let base = cs.n();
                let _ = a.sub_unequal(&mut cs, b).unwrap();
                println!("Single subtraction taken {} gates", cs.n() - base);
            }
        }
    }

    #[test]
    fn test_double_on_random_witnesses(){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

        for i in 0..100 {
            let mut cs = TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();

            let a_f: G1Affine = rng.gen();

            let a = AffinePoint::alloc(
                &mut cs, 
                Some(a_f), 
                &params
            ).unwrap();
    
            let (result, a) = a.double(&mut cs).unwrap();

            assert!(cs.is_satisfied());

            let x_fe = result.x.get_field_value().unwrap();
            let y_fe = result.y.get_field_value().unwrap();

            let (x, y) = result.get_value().unwrap().into_xy_unchecked();

            assert_eq!(x_fe, x, "x coords mismatch");
            assert_eq!(y_fe, y, "y coords mismatch");

            let (x, y) = a_f.into_xy_unchecked();
            assert_eq!(a.x.get_field_value().unwrap(), x, "x coords mismatch");
            assert_eq!(a.y.get_field_value().unwrap(), y, "y coords mismatch");

            if i == 0 {
                let base = cs.n();
                let _ = a.double(&mut cs).unwrap();
                println!("Single double taken {} gates", cs.n() - base);
            }
        }
    }

    #[test]
    fn test_double_and_add_on_random_witnesses(){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

        for i in 0..100 {
            let mut cs = TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();

            let a_f: G1Affine = rng.gen();
            let b_f: G1Affine = rng.gen();

            let a = AffinePoint::alloc(
                &mut cs, 
                Some(a_f), 
                &params
            ).unwrap();

            let b = AffinePoint::alloc(
                &mut cs, 
                Some(b_f), 
                &params
            ).unwrap();
    
            let (result, (a, b)) = a.double_and_add(&mut cs, b).unwrap();

            let mut result_recalcualted = a_f.into_projective();
            result_recalcualted.double();
            result_recalcualted.add_assign_mixed(&b_f);

            let result_recalcualted = result_recalcualted.into_affine();

            assert!(cs.is_satisfied());

            let (x, y) = result_recalcualted.into_xy_unchecked();

            let x_fe = result.x.get_field_value().unwrap();
            let y_fe = result.y.get_field_value().unwrap();

            assert_eq!(x_fe, x, "x coords mismatch between normal and circuit result");
            assert_eq!(y_fe, y, "y coords mismatch between normal and circuit result");

            let (x, y) = result.get_value().unwrap().into_xy_unchecked();

            assert_eq!(x_fe, x, "x coords mismatch");
            assert_eq!(y_fe, y, "y coords mismatch");

            let (x, y) = a_f.into_xy_unchecked();
            assert_eq!(a.x.get_field_value().unwrap(), x, "x coords mismatch");
            assert_eq!(a.y.get_field_value().unwrap(), y, "y coords mismatch");

            let (x, y) = b_f.into_xy_unchecked();
            assert_eq!(b.x.get_field_value().unwrap(), x, "x coords mismatch");
            assert_eq!(b.y.get_field_value().unwrap(), y, "y coords mismatch");

            if i == 0 {
                let base = cs.n();
                let _ = a.double_and_add(&mut cs, b).unwrap();
                println!("Single double and add taken {} gates", cs.n() - base);
            }
        }
    }

    #[test]
    fn test_skewed_decomposition_on_random_witnesses(){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for _i in 0..100 {
            let a_f: Fr = rng.gen();

            let _ = compute_skewed_naf_table(&Some(a_f), None);
            
        }
    }

    #[test]
    fn test_allocated_skewed_decomposition_on_random_witnesses(){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for i in 0..100 {
            let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

            let a_f: Fr = rng.gen();

            let a = AllocatedNum::alloc(
                &mut cs, 
                || {
                    Ok(a_f)
                }
            ).unwrap();

            let _ = decompose_allocated_num_into_skewed_table(&mut cs, &a, None).unwrap();

            assert!(cs.is_satisfied());

            if i == 0 {
                println!("Single decomposition taken {} gates", cs.n());
            }
        }
    }


    #[test]
    fn test_allocated_skewed_decomposition_bls12_on_random_witnesses(){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        use crate::bellman::pairing::bls12_381::{Bls12, Fr, Fq, G1Affine, G1};

        let mut four = Fr::one();
        four.double();
        four.double();

        let _ = compute_skewed_naf_table(&Some(four), Some(3));

        for i in 0..100 {
            let mut cs = TrivialAssembly::<Bls12, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

            let a_f: Fr = rng.gen();

            let a = AllocatedNum::alloc(
                &mut cs, 
                || {
                    Ok(a_f)
                }
            ).unwrap();

            let _ = decompose_allocated_num_into_skewed_table(&mut cs, &a, None).unwrap();

            assert!(cs.is_satisfied());

            if i == 0 {
                println!("Single decomposition taken {} gates", cs.n());
            }
        }
    }

    #[test]
    fn test_base_curve_multiplication_by_two_on_random_witnesses(){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

        for i in 0..10 {
            let mut cs = TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();

            let a_f: G1Affine = rng.gen();
            let mut b_f: Fr = Fr::one();
            b_f.double();

            let a = AffinePoint::alloc(
                &mut cs, 
                Some(a_f), 
                &params
            ).unwrap();

            let b = AllocatedNum::alloc(
                &mut cs, 
                || {
                    Ok(b_f)
                }
            ).unwrap();

            let b = Num::Variable(b);

            // simulate_multiplication::<Bn256>(a_f, b_f, Some(2));
    
            let (result, a) = a.mul(&mut cs, &b, Some(257)).unwrap();

            let result_recalculated = a_f.mul(b_f.into_repr()).into_affine();

            // println!("Expected result = {}", result_recalculated);

            assert!(cs.is_satisfied());

            let x_fe = result.x.get_field_value().unwrap();
            let y_fe = result.y.get_field_value().unwrap();

            let (x, y) = result.get_value().unwrap().into_xy_unchecked();

            assert_eq!(x_fe, x, "x coords mismatch");
            assert_eq!(y_fe, y, "y coords mismatch");

            let (x, y) = result_recalculated.into_xy_unchecked();

            assert_eq!(x_fe, x, "x coords mismatch");
            assert_eq!(y_fe, y, "y coords mismatch");

            let (x, y) = a_f.into_xy_unchecked();
            assert_eq!(a.x.get_field_value().unwrap(), x, "x coords mismatch");
            assert_eq!(a.y.get_field_value().unwrap(), y, "y coords mismatch");

            if i == 0 {
                let base = cs.n();
                let _ = a.mul(&mut cs, &b, Some(2)).unwrap();
                println!("Single multiplication by 2 taken {} gates", cs.n() - base);
            }
        }
    }

    #[test]
    fn test_base_curve_multiplication_on_random_witnesses(){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

        for i in 0..10 {
            let mut cs = TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();

            let a_f: G1Affine = rng.gen();
            // let b_f: Fr = rng.gen();
            let b_f = Fr::from_str("9").unwrap();

            let a = AffinePoint::alloc(
                &mut cs, 
                Some(a_f), 
                &params
            ).unwrap();

            let b = AllocatedNum::alloc(
                &mut cs, 
                || {
                    Ok(b_f)
                }
            ).unwrap();

            let b = Num::Variable(b);
    
            let (result, a) = a.mul(&mut cs, &b, Some(254)).unwrap();

            let result_recalculated = a_f.mul(b_f.into_repr()).into_affine();

            assert!(cs.is_satisfied());

            let x_fe = result.x.get_field_value().unwrap();
            let y_fe = result.y.get_field_value().unwrap();

            let (x, y) = result.get_value().unwrap().into_xy_unchecked();

            assert_eq!(x_fe, x, "x coords mismatch between value and coordinates");
            assert_eq!(y_fe, y, "y coords mismatch between value and coordinates");

            let (x, y) = result_recalculated.into_xy_unchecked();

            assert_eq!(x_fe, x, "x coords mismatch between expected result and circuit result");
            assert_eq!(y_fe, y, "y coords mismatch between expected result and circuit result");

            assert_eq!(result.get_value().unwrap(), result_recalculated, "mismatch between expected result and circuit result");

            let (x, y) = a_f.into_xy_unchecked();
            assert_eq!(a.x.get_field_value().unwrap(), x, "x coords mismatch, input was mutated");
            assert_eq!(a.y.get_field_value().unwrap(), y, "y coords mismatch, input was mutated");

            if i == 0 {
                let base = cs.n();
                let _ = a.mul(&mut cs, &b, Some(254)).unwrap();
                println!("Affine single multiplication taken {} gates", cs.n() - base);
            }
        }
    }

    #[test]
    fn test_base_curve_multiplication_with_range_table(){
        use crate::plonk::circuit::tables::inscribe_default_range_table_for_bit_width_over_first_three_columns;
        use crate::plonk::circuit::bigint::*;
        use crate::plonk::circuit::bigint::single_table_range_constraint::{reset_stats, print_stats};
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let info = RangeConstraintInfo {
            minimal_multiple: 17,
            optimal_multiple: 17,
            multiples_per_gate: 1,
            linear_terms_used: 3,
            strategy: RangeConstraintStrategy::SingleTableInvocation,
        };
        let params = RnsParameters::<Bn256, Fq>::new_for_field_with_strategy(
            68,
            110, 
            4, 
            info,
            true
        );

        for i in 0..10 {
            let mut cs = TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();
            inscribe_default_range_table_for_bit_width_over_first_three_columns(&mut cs, 17).unwrap();
            let a_f: G1Affine = rng.gen();
            let b_f: Fr = rng.gen();

            let a = AffinePoint::alloc(
                &mut cs, 
                Some(a_f), 
                &params
            ).unwrap();

            let b = AllocatedNum::alloc(
                &mut cs, 
                || {
                    Ok(b_f)
                }
            ).unwrap();

            let b = Num::Variable(b);
    
            let (result, a) = a.mul(&mut cs, &b, None).unwrap();

            let result_recalculated = a_f.mul(b_f.into_repr()).into_affine();

            assert!(cs.is_satisfied());

            let x_fe = result.x.get_field_value().unwrap();
            let y_fe = result.y.get_field_value().unwrap();

            let (x, y) = result.get_value().unwrap().into_xy_unchecked();

            assert_eq!(x_fe, x, "x coords mismatch between value and coordinates");
            assert_eq!(y_fe, y, "y coords mismatch between value and coordinates");

            let (x, y) = result_recalculated.into_xy_unchecked();

            assert_eq!(x_fe, x, "x coords mismatch between expected result and circuit result");
            assert_eq!(y_fe, y, "y coords mismatch between expected result and circuit result");

            assert_eq!(result.get_value().unwrap(), result_recalculated, "mismatch between expected result and circuit result");

            let (x, y) = a_f.into_xy_unchecked();
            assert_eq!(a.x.get_field_value().unwrap(), x, "x coords mismatch, input was mutated");
            assert_eq!(a.y.get_field_value().unwrap(), y, "y coords mismatch, input was mutated");

            if i == 0 {
                reset_stats();
                crate::plonk::circuit::counter::reset_counter();
                let base = cs.n();
                let _ = a.mul(&mut cs, &b, None).unwrap();
                println!("Affine single multiplication taken {} gates", cs.n() - base);
                println!("Affine spent {} gates in equality checks", crate::plonk::circuit::counter::output_counter());
                print_stats();
            }
        }
    }

    #[test]
    fn test_bn254_multiexp_10_with_range_table(){
        use crate::plonk::circuit::tables::inscribe_default_range_table_for_bit_width_over_first_three_columns;
        use crate::plonk::circuit::bigint::*;
        use crate::plonk::circuit::bigint::single_table_range_constraint::{reset_stats, print_stats};
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let info = RangeConstraintInfo {
            minimal_multiple: 17,
            optimal_multiple: 17,
            multiples_per_gate: 1,
            linear_terms_used: 3,
            strategy: RangeConstraintStrategy::SingleTableInvocation,
        };
        let params = RnsParameters::<Bn256, Fq>::new_for_field_with_strategy(
            68,
            110, 
            4, 
            info,
            true
        );

        for i in 0..10 {
            let mut cs = TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();
            inscribe_default_range_table_for_bit_width_over_first_three_columns(&mut cs, 17).unwrap();

            let mut a_s = vec![];
            let mut b_s = vec![];
            for _ in 0..10 {
                let a_f: G1Affine = rng.gen();
                let b_f: Fr = rng.gen();

                a_s.push(a_f);
                b_s.push(b_f);
            }
            
            let mut a_p = vec![];
            for a in a_s.iter() {
                let a = AffinePoint::alloc(
                    &mut cs, 
                    Some(*a), 
                    &params
                ).unwrap();

                a_p.push(a);
            }

            let mut b_n = vec![];

            for b in b_s.iter() {
                let b = AllocatedNum::alloc(
                    &mut cs, 
                    || {
                        Ok(*b)
                    }
                ).unwrap();

                let b = Num::Variable(b);
                b_n.push(b);
            }

            let result = AffinePoint::multiexp(&mut cs, &b_n, &a_p, None).unwrap();

            let mut result_recalculated = G1Affine::zero().into_projective();

            for (a, b) in a_s.iter().zip(b_s.iter()) {
                let tmp = a.mul(b.into_repr());
                result_recalculated.add_assign(&tmp);
            }

            let result_recalculated = result_recalculated.into_affine();

            assert!(cs.is_satisfied());

            let x_fe = result.x.get_field_value().unwrap();
            let y_fe = result.y.get_field_value().unwrap();

            let (x, y) = result.get_value().unwrap().into_xy_unchecked();

            assert_eq!(x_fe, x, "x coords mismatch between value and coordinates");
            assert_eq!(y_fe, y, "y coords mismatch between value and coordinates");

            let (x, y) = result_recalculated.into_xy_unchecked();

            assert_eq!(x_fe, x, "x coords mismatch between expected result and circuit result");
            assert_eq!(y_fe, y, "y coords mismatch between expected result and circuit result");

            assert_eq!(result.get_value().unwrap(), result_recalculated, "mismatch between expected result and circuit result");

            if i == 0 {
                reset_stats();
                crate::plonk::circuit::counter::reset_counter();
                let base = cs.n();
                let _ = AffinePoint::multiexp(&mut cs, &b_n, &a_p, None).unwrap();
                println!("Affine 10 points multiexp without endo taken {} gates", cs.n() - base);
                println!("Affine spent {} gates in equality checks", crate::plonk::circuit::counter::output_counter());
                print_stats();
            }
        }
    }

    #[test]
    fn test_bn254_multiexp_10_with_endo_and_range_table(){
        use crate::plonk::circuit::tables::inscribe_default_range_table_for_bit_width_over_first_three_columns;
        use crate::plonk::circuit::bigint::*;
        use crate::plonk::circuit::bigint::single_table_range_constraint::{reset_stats, print_stats};
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let info = RangeConstraintInfo {
            minimal_multiple: 17,
            optimal_multiple: 17,
            multiples_per_gate: 1,
            linear_terms_used: 3,
            strategy: RangeConstraintStrategy::SingleTableInvocation,
        };
        let params = RnsParameters::<Bn256, Fq>::new_for_field_with_strategy(
            68,
            110, 
            4, 
            info,
            true
        );
        let endo_parameters = super::super::endomorphism::bn254_endomorphism_parameters();

        for i in 0..10 {
            let mut cs = TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();
            inscribe_default_range_table_for_bit_width_over_first_three_columns(&mut cs, 17).unwrap();

            let mut a_s = vec![];
            let mut b_s = vec![];
            for _ in 0..10 {
                let a_f: G1Affine = rng.gen();
                let b_f: Fr = rng.gen();

                a_s.push(a_f);
                b_s.push(b_f);
            }
            
            let mut a_p = vec![];
            for a in a_s.iter() {
                let a = AffinePoint::alloc(
                    &mut cs, 
                    Some(*a), 
                    &params
                ).unwrap();

                a_p.push(a);
            }

            let mut b_n = vec![];

            for b in b_s.iter() {
                let b = AllocatedNum::alloc(
                    &mut cs, 
                    || {
                        Ok(*b)
                    }
                ).unwrap();

                let b = Num::Variable(b);
                b_n.push(b);
            }

            let result = AffinePoint::multiexp_using_endomorphism(&mut cs, &b_n, &a_p, &endo_parameters).unwrap();

            let mut result_recalculated = G1Affine::zero().into_projective();

            for (a, b) in a_s.iter().zip(b_s.iter()) {
                let tmp = a.mul(b.into_repr());
                result_recalculated.add_assign(&tmp);
            }

            let result_recalculated = result_recalculated.into_affine();

            assert!(cs.is_satisfied());

            let x_fe = result.x.get_field_value().unwrap();
            let y_fe = result.y.get_field_value().unwrap();

            let (x, y) = result.get_value().unwrap().into_xy_unchecked();

            assert_eq!(x_fe, x, "x coords mismatch between value and coordinates");
            assert_eq!(y_fe, y, "y coords mismatch between value and coordinates");

            let (x, y) = result_recalculated.into_xy_unchecked();

            assert_eq!(x_fe, x, "x coords mismatch between expected result and circuit result");
            assert_eq!(y_fe, y, "y coords mismatch between expected result and circuit result");

            assert_eq!(result.get_value().unwrap(), result_recalculated, "mismatch between expected result and circuit result");

            if i == 0 {
                reset_stats();
                crate::plonk::circuit::counter::reset_counter();
                let base = cs.n();
                let _ = AffinePoint::multiexp_using_endomorphism(&mut cs, &b_n, &a_p, &endo_parameters).unwrap();
                println!("Affine 10 points multiexp with endo taken {} gates", cs.n() - base);
                println!("Affine spent {} gates in equality checks", crate::plonk::circuit::counter::output_counter());
                print_stats();
            }
        }
    }

    #[test]
    fn test_base_curve_multiexp_1_on_random_witnesses(){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

        for i in 0..10 {
            let mut cs = TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();

            let a_f: G1Affine = rng.gen();
            let b_f: Fr = rng.gen();

            let a = AffinePoint::alloc(
                &mut cs, 
                Some(a_f), 
                &params
            ).unwrap();

            let b = AllocatedNum::alloc(
                &mut cs, 
                || {
                    Ok(b_f)
                }
            ).unwrap();

            let b = Num::Variable(b);

            let result = AffinePoint::multiexp(&mut cs, &[b.clone()], &[a.clone()], None).unwrap();

            let result_recalculated = a_f.mul(b_f.into_repr()).into_affine();

            assert!(cs.is_satisfied());

            let x_fe = result.x.get_field_value().unwrap();
            let y_fe = result.y.get_field_value().unwrap();

            let (x, y) = result.get_value().unwrap().into_xy_unchecked();

            assert_eq!(x_fe, x, "x coords mismatch between value and coordinates");
            assert_eq!(y_fe, y, "y coords mismatch between value and coordinates");

            let (x, y) = result_recalculated.into_xy_unchecked();

            assert_eq!(x_fe, x, "x coords mismatch between expected result and circuit result");
            assert_eq!(y_fe, y, "y coords mismatch between expected result and circuit result");

            assert_eq!(result.get_value().unwrap(), result_recalculated, "mismatch between expected result and circuit result");

            let (x, y) = a_f.into_xy_unchecked();
            assert_eq!(a.x.get_field_value().unwrap(), x, "x coords mismatch, input was mutated");
            assert_eq!(a.y.get_field_value().unwrap(), y, "y coords mismatch, input was mutated");

            if i == 0 {
                let base = cs.n();
                let _ = AffinePoint::multiexp(&mut cs, &[b.clone()], &[a.clone()], None).unwrap();
                println!("One point multiexp taken {} gates", cs.n() - base);
            }
        }
    }

    #[test]
    fn test_base_curve_multiexp_2_on_random_witnesses(){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

        for i in 0..10 {
            let mut cs = TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();

            let mut a_s = vec![];
            let mut b_s = vec![];
            for _ in 0..2 {
                let a_f: G1Affine = rng.gen();
                let b_f: Fr = rng.gen();

                a_s.push(a_f);
                b_s.push(b_f);
            }
            
            let mut a_p = vec![];
            for a in a_s.iter() {
                let a = AffinePoint::alloc(
                    &mut cs, 
                    Some(*a), 
                    &params
                ).unwrap();

                a_p.push(a);
            }

            let mut b_n = vec![];

            for b in b_s.iter() {
                let b = AllocatedNum::alloc(
                    &mut cs, 
                    || {
                        Ok(*b)
                    }
                ).unwrap();

                let b = Num::Variable(b);
                b_n.push(b);
            }

            let result = AffinePoint::multiexp(&mut cs, &b_n, &a_p, None).unwrap();

            let mut result_recalculated = G1Affine::zero().into_projective();

            for (a, b) in a_s.iter().zip(b_s.iter()) {
                let tmp = a.mul(b.into_repr());
                result_recalculated.add_assign(&tmp);
            }

            let result_recalculated = result_recalculated.into_affine();

            assert!(cs.is_satisfied());

            let x_fe = result.x.get_field_value().unwrap();
            let y_fe = result.y.get_field_value().unwrap();

            let (x, y) = result.get_value().unwrap().into_xy_unchecked();

            assert_eq!(x_fe, x, "x coords mismatch between value and coordinates");
            assert_eq!(y_fe, y, "y coords mismatch between value and coordinates");

            let (x, y) = result_recalculated.into_xy_unchecked();

            assert_eq!(x_fe, x, "x coords mismatch between expected result and circuit result");
            assert_eq!(y_fe, y, "y coords mismatch between expected result and circuit result");

            assert_eq!(result.get_value().unwrap(), result_recalculated, "mismatch between expected result and circuit result");

            if i == 0 {
                let base = cs.n();
                let _ = AffinePoint::multiexp(&mut cs, &b_n, &a_p, None).unwrap();
                println!("Two points multiexp taken {} gates", cs.n() - base);
            }
        }
    }

    #[test]
    fn test_base_curve_multiexp_3_on_random_witnesses(){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

        for i in 0..10 {
            let mut cs = TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();

            let mut a_s = vec![];
            let mut b_s = vec![];
            for _ in 0..3 {
                let a_f: G1Affine = rng.gen();
                let b_f: Fr = rng.gen();

                a_s.push(a_f);
                b_s.push(b_f);
            }
            
            let mut a_p = vec![];
            for a in a_s.iter() {
                let a = AffinePoint::alloc(
                    &mut cs, 
                    Some(*a), 
                    &params
                ).unwrap();

                a_p.push(a);
            }

            let mut b_n = vec![];

            for b in b_s.iter() {
                let b = AllocatedNum::alloc(
                    &mut cs, 
                    || {
                        Ok(*b)
                    }
                ).unwrap();

                let b = Num::Variable(b);
                b_n.push(b);
            }

            let result = AffinePoint::multiexp(&mut cs, &b_n, &a_p, None).unwrap();

            let mut result_recalculated = G1Affine::zero().into_projective();

            for (a, b) in a_s.iter().zip(b_s.iter()) {
                let tmp = a.mul(b.into_repr());
                result_recalculated.add_assign(&tmp);
            }

            let result_recalculated = result_recalculated.into_affine();

            assert!(cs.is_satisfied());

            let x_fe = result.x.get_field_value().unwrap();
            let y_fe = result.y.get_field_value().unwrap();

            let (x, y) = result.get_value().unwrap().into_xy_unchecked();

            assert_eq!(x_fe, x, "x coords mismatch between value and coordinates");
            assert_eq!(y_fe, y, "y coords mismatch between value and coordinates");

            let (x, y) = result_recalculated.into_xy_unchecked();

            assert_eq!(x_fe, x, "x coords mismatch between expected result and circuit result");
            assert_eq!(y_fe, y, "y coords mismatch between expected result and circuit result");

            assert_eq!(result.get_value().unwrap(), result_recalculated, "mismatch between expected result and circuit result");

            if i == 0 {
                let base = cs.n();
                let _ = AffinePoint::multiexp(&mut cs, &b_n, &a_p, None).unwrap();
                println!("Three points multiexp taken {} gates", cs.n() - base);
            }
        }
    }

    #[test]
    fn test_base_curve_multiexp_4_on_random_witnesses(){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

        for i in 0..10 {
            let mut cs = TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();

            let mut a_s = vec![];
            let mut b_s = vec![];
            for _ in 0..4 {
                let a_f: G1Affine = rng.gen();
                let b_f: Fr = rng.gen();

                a_s.push(a_f);
                b_s.push(b_f);
            }
            
            let mut a_p = vec![];
            for a in a_s.iter() {
                let a = AffinePoint::alloc(
                    &mut cs, 
                    Some(*a), 
                    &params
                ).unwrap();

                a_p.push(a);
            }

            let mut b_n = vec![];

            for b in b_s.iter() {
                let b = AllocatedNum::alloc(
                    &mut cs, 
                    || {
                        Ok(*b)
                    }
                ).unwrap();

                let b = Num::Variable(b);
                b_n.push(b);
            }

            let result = AffinePoint::multiexp(&mut cs, &b_n, &a_p, None).unwrap();

            let mut result_recalculated = G1Affine::zero().into_projective();

            for (a, b) in a_s.iter().zip(b_s.iter()) {
                let tmp = a.mul(b.into_repr());
                result_recalculated.add_assign(&tmp);
            }

            let result_recalculated = result_recalculated.into_affine();

            assert!(cs.is_satisfied());

            let x_fe = result.x.get_field_value().unwrap();
            let y_fe = result.y.get_field_value().unwrap();

            let (x, y) = result.get_value().unwrap().into_xy_unchecked();

            assert_eq!(x_fe, x, "x coords mismatch between value and coordinates");
            assert_eq!(y_fe, y, "y coords mismatch between value and coordinates");

            let (x, y) = result_recalculated.into_xy_unchecked();

            assert_eq!(x_fe, x, "x coords mismatch between expected result and circuit result");
            assert_eq!(y_fe, y, "y coords mismatch between expected result and circuit result");

            assert_eq!(result.get_value().unwrap(), result_recalculated, "mismatch between expected result and circuit result");

            if i == 0 {
                let base = cs.n();
                let _ = AffinePoint::multiexp(&mut cs, &b_n, &a_p, None).unwrap();
                println!("Four points multiexp taken {} gates", cs.n() - base);
            }
        }
    }

    #[test]
    fn test_base_curve_multiexp_10_on_random_witnesses(){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

        for i in 0..10 {
            let mut cs = TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();

            let mut a_s = vec![];
            let mut b_s = vec![];
            for _ in 0..10 {
                let a_f: G1Affine = rng.gen();
                let b_f: Fr = rng.gen();

                a_s.push(a_f);
                b_s.push(b_f);
            }
            
            let mut a_p = vec![];
            for a in a_s.iter() {
                let a = AffinePoint::alloc(
                    &mut cs, 
                    Some(*a), 
                    &params
                ).unwrap();

                a_p.push(a);
            }

            let mut b_n = vec![];

            for b in b_s.iter() {
                let b = AllocatedNum::alloc(
                    &mut cs, 
                    || {
                        Ok(*b)
                    }
                ).unwrap();

                let b = Num::Variable(b);
                b_n.push(b);
            }

            let result = AffinePoint::multiexp(&mut cs, &b_n, &a_p, None).unwrap();

            let mut result_recalculated = G1Affine::zero().into_projective();

            for (a, b) in a_s.iter().zip(b_s.iter()) {
                let tmp = a.mul(b.into_repr());
                result_recalculated.add_assign(&tmp);
            }

            let result_recalculated = result_recalculated.into_affine();

            assert!(cs.is_satisfied());

            let x_fe = result.x.get_field_value().unwrap();
            let y_fe = result.y.get_field_value().unwrap();

            let (x, y) = result.get_value().unwrap().into_xy_unchecked();

            assert_eq!(x_fe, x, "x coords mismatch between value and coordinates");
            assert_eq!(y_fe, y, "y coords mismatch between value and coordinates");

            let (x, y) = result_recalculated.into_xy_unchecked();

            assert_eq!(x_fe, x, "x coords mismatch between expected result and circuit result");
            assert_eq!(y_fe, y, "y coords mismatch between expected result and circuit result");

            assert_eq!(result.get_value().unwrap(), result_recalculated, "mismatch between expected result and circuit result");

            if i == 0 {
                let base = cs.n();
                use std::sync::atomic::Ordering;
                let k = super::super::super::bigint::RANGE_GATES_COUNTER.load(Ordering::SeqCst);
                let _ = AffinePoint::multiexp(&mut cs, &b_n, &a_p, None).unwrap();
                let k = super::super::super::bigint::RANGE_GATES_COUNTER.load(Ordering::SeqCst) - k;
                println!("10 points multiexp taken {} gates", cs.n() - base);
                println!("Range checks take {} gates", k);
            }
        }
    }

    #[test]
    fn test_base_curve_multiexp_10_bls_12_on_random_witnesses() {
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        use crate::bellman::pairing::bls12_381::{Bls12, Fr, Fq, G1Affine, G1};

        use super::super::super::bigint::get_range_constraint_info;

        let params = RnsParameters::<Bls12, Fq>::new_for_field(68, 110, 8);

        for i in 0..10 {
            let mut cs = TrivialAssembly::<Bls12, Width4WithCustomGates, Width4MainGateWithDNext>::new();

            // let strats = get_range_constraint_info(&cs);

            // let mut params = RnsParameters::<Bls12, Fq>::new_for_field_with_strategy(
            //     96, 
            //     110, 
            //     6, 
            //     strats[0],
            //     true
            // );

            // params.set_prefer_double_limb_carry_propagation(false);

            let mut a_s = vec![];
            let mut b_s = vec![];
            for _ in 0..10 {
                let a_f: G1 = rng.gen();
                let a_f = a_f.into_affine();
                let b_f: Fr = rng.gen();

                a_s.push(a_f);
                b_s.push(b_f);
            }
            
            let mut a_p = vec![];
            for a in a_s.iter() {
                let a = AffinePoint::alloc(
                    &mut cs, 
                    Some(*a), 
                    &params
                ).unwrap();

                a_p.push(a);
            }

            let mut b_n = vec![];

            for b in b_s.iter() {
                let b = AllocatedNum::alloc(
                    &mut cs, 
                    || {
                        Ok(*b)
                    }
                ).unwrap();

                let b = Num::Variable(b);
                b_n.push(b);
            }

            let result = AffinePoint::multiexp(&mut cs, &b_n, &a_p, None).unwrap();

            let mut result_recalculated = G1Affine::zero().into_projective();

            for (a, b) in a_s.iter().zip(b_s.iter()) {
                let tmp = a.mul(b.into_repr());
                result_recalculated.add_assign(&tmp);
            }

            let result_recalculated = result_recalculated.into_affine();

            assert!(cs.is_satisfied());

            let x_fe = result.x.get_field_value().unwrap();
            let y_fe = result.y.get_field_value().unwrap();

            let (x, y) = result.get_value().unwrap().into_xy_unchecked();

            assert_eq!(x_fe, x, "x coords mismatch");
            assert_eq!(y_fe, y, "y coords mismatch");

            let (x, y) = result_recalculated.into_xy_unchecked();

            assert_eq!(x_fe, x, "x coords mismatch");
            assert_eq!(y_fe, y, "y coords mismatch");

            if i == 0 {
                let base = cs.n();
                use std::sync::atomic::Ordering;
                let k = super::super::super::bigint::RANGE_GATES_COUNTER.load(Ordering::SeqCst);
                let _ = AffinePoint::multiexp(&mut cs, &b_n, &a_p, None).unwrap();
                let k = super::super::super::bigint::RANGE_GATES_COUNTER.load(Ordering::SeqCst) - k;
                println!("10 points multiexp taken {} gates", cs.n() - base);
                println!("Range checks take {} gates", k);
            }
        }
    }

    #[test]
    fn test_base_curve_multiexp_10_bls_12_using_tables_on_random_witnesses() {
        use crate::bellman::plonk::better_better_cs::cs::*;
        use super::super::super::bigint::get_range_constraint_info;
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        use crate::bellman::pairing::bls12_381::{Bls12, Fr, Fq, G1Affine, G1};

        let mut cs = TrivialAssembly::<Bls12, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

        let over = vec![PolyIdentifier::VariablesPolynomial(0), PolyIdentifier::VariablesPolynomial(1), PolyIdentifier::VariablesPolynomial(2)];
        let table = MultiTableApplication::<Bls12>::new_range_table_of_width_3(16, over).unwrap();

        cs.add_multitable(table).unwrap();

        let strats = get_range_constraint_info(&cs);

        let mut params = RnsParameters::<Bls12, Fq>::new_for_field_with_strategy(
            96, 
            110, 
            6, 
            strats[0],
            true
        );

        params.set_prefer_double_limb_carry_propagation(false);

        let mut a_s = vec![];
        let mut b_s = vec![];
        for _ in 0..10 {
            let a_f: G1 = rng.gen();
            let a_f = a_f.into_affine();
            let b_f: Fr = rng.gen();

            a_s.push(a_f);
            b_s.push(b_f);
        }
        
        let mut a_p = vec![];
        for a in a_s.iter() {
            let a = AffinePoint::alloc(
                &mut cs, 
                Some(*a), 
                &params
            ).unwrap();

            a_p.push(a);
        }

        let mut b_n = vec![];

        for b in b_s.iter() {
            let b = AllocatedNum::alloc(
                &mut cs, 
                || {
                    Ok(*b)
                }
            ).unwrap();

            let b = Num::Variable(b);
            b_n.push(b);
        }

        let base = cs.n();

        let _result = AffinePoint::multiexp(&mut cs, &b_n, &a_p, None).unwrap();

        println!("10 points multiexp with 16 bit range tables taken {} gates", cs.n() - base);

        let mut result_recalculated = G1Affine::zero().into_projective();

        for (a, b) in a_s.iter().zip(b_s.iter()) {
            let tmp = a.mul(b.into_repr());
            result_recalculated.add_assign(&tmp);
        }

        let _result_recalculated = result_recalculated.into_affine();

        assert!(cs.is_satisfied());
    }
    #[test]
    fn test_base_curve_multiplication_by_split_scalar_with_range_table_and_endomorphism() {
        use rand::{Rng, SeedableRng, XorShiftRng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

        for i in 0..1 {
            let mut cs =
                TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();

            let a_f: G1Affine = rng.gen();
            let b_f: Fr = rng.gen();
            use plonk::circuit::tables::inscribe_combined_bitwise_ops_and_range_table;
            inscribe_combined_bitwise_ops_and_range_table(&mut cs, 8).unwrap();

            let a = AffinePoint::alloc(&mut cs, Some(a_f), &params).unwrap();

            let b = AllocatedNum::alloc(&mut cs, || Ok(b_f)).unwrap();

            let b = Num::Variable(b);

            let endo_parameters = super::super::endomorphism::bn254_endomorphism_parameters();

            let result = a.clone().mul_split_scalar_2(&mut cs, &b, endo_parameters.clone(), 2);
            // println!("{:?}", result);

            // let result_recalculated = a_f.mul(b_f.into_repr()).into_affine();

            // assert!(cs.is_satisfied());

            // let x_fe = result.x.get_field_value().unwrap();
            // let y_fe = result.y.get_field_value().unwrap();

            // let (x, y) = result.get_value().unwrap().into_xy_unchecked();

            // assert_eq!(x_fe, x, "x coords mismatch between value and coordinates");
            // assert_eq!(y_fe, y, "y coords mismatch between value and coordinates");

            // let (x, y) = result_recalculated.into_xy_unchecked();

            // assert_eq!(
            //     x_fe, x,
            //     "x coords mismatch between expected result and circuit result"
            // );
            // assert_eq!(
            //     y_fe, y,
            //     "y coords mismatch between expected result and circuit result"
            // );

            // assert_eq!(
            //     result.get_value().unwrap(),
            //     result_recalculated,
            //     "mismatch between expected result and circuit result"
            // );

            // let (x, y) = a_f.into_xy_unchecked();
            // assert_eq!(
            //     a.x.get_field_value().unwrap(),
            //     x,
            //     "x coords mismatch, input was mutated"
            // );
            // assert_eq!(
            //     a.y.get_field_value().unwrap(),
            //     y,
            //     "y coords mismatch, input was mutated"
            // );

            if i == 0 {
                crate::plonk::circuit::counter::reset_counter();
                let base = cs.n();
                let _ = a.mul_split_scalar_2(&mut cs, &b, endo_parameters, 2);
                println!("single multiplication taken {} gates", cs.n() - base);
                println!(
                    "Affine spent {} gates in equality checks",
                    crate::plonk::circuit::counter::output_counter()
                );
            }
        }
    }
    #[test]
    fn endomorphism_2() {
        use rand::{Rng, SeedableRng, XorShiftRng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

        for i in 0..1 {
            let mut cs =
                TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();

            let a_f: G1Affine = rng.gen();
            let b_f: Fr = rng.gen();


            let a = AffinePoint::alloc(&mut cs, Some(a_f), &params).unwrap();

            let b = AllocatedNum::alloc(&mut cs, || Ok(b_f)).unwrap();

            let b = Num::Variable(b);

            let endo_parameters = super::super::endomorphism::bn254_endomorphism_parameters();

            let (result, a) = a.mul_split_scalar(&mut cs, &b, endo_parameters.clone(), 1).unwrap();

            let result_recalculated = a_f.mul(b_f.into_repr()).into_affine();

            assert!(cs.is_satisfied());

            let x_fe = result.x.get_field_value().unwrap();
            let y_fe = result.y.get_field_value().unwrap();

            let (x, y) = result.get_value().unwrap().into_xy_unchecked();

            // assert_eq!(x_fe, x, "x coords mismatch between value and coordinates");
            // assert_eq!(y_fe, y, "y coords mismatch between value and coordinates");

            let (x, y) = result_recalculated.into_xy_unchecked();

            // assert_eq!(
            //     x_fe, x,
            //     "x coords mismatch between expected result and circuit result"
            // );
            // assert_eq!(
            //     y_fe, y,
            //     "y coords mismatch between expected result and circuit result"
            // );

            // assert_eq!(
            //     result.get_value().unwrap(),
            //     result_recalculated,
            //     "mismatch between expected result and circuit result"
            // );

            // let (x, y) = a_f.into_xy_unchecked();
            // assert_eq!(
            //     a.x.get_field_value().unwrap(),
            //     x,
            //     "x coords mismatch, input was mutated"
            // );
            // assert_eq!(
            //     a.y.get_field_value().unwrap(),
            //     y,
            //     "y coords mismatch, input was mutated"
            // );

            if i == 0 {
                crate::plonk::circuit::counter::reset_counter();
                let base = cs.n();
                let _ = a.mul_split_scalar(&mut cs, &b, endo_parameters, 1).unwrap();
                println!("single multiplication taken {} gates", cs.n() - base);
                println!(
                    "Affine spent {} gates in equality checks",
                    crate::plonk::circuit::counter::output_counter()
                );
            }
        }
    }
    #[test]
    fn endomorphism_3() {
        use rand::{Rng, SeedableRng, XorShiftRng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

        for i in 0..1 {
            let mut cs =
                TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();

            let a_f: G1Affine = rng.gen();
            let b_f: Fr = rng.gen();
            const RATE: usize = 2;
            const WIDTH: usize = 3;
            const INPUT_LENGTH: usize = 1;
            use plonk::circuit::rescue_copy::sponge::GenericSponge;
            use plonk::circuit::rescue_copy::rescue::params::RescueParams;
            // let mut params = crate::utils::bn254_rescue_params();
            let rescue_params = RescueParams::<Bn256, RATE, WIDTH>::default();
            use plonk::circuit::curve::sponge::GenericHasher;
            let committer = GenericHasher::<Bn256, RescueParams<Bn256, 2, 3>, 2, 3>::new_from_params(&rescue_params);
            use plonk::circuit::tables::inscribe_combined_bitwise_ops_and_range_table;
            inscribe_combined_bitwise_ops_and_range_table(&mut cs, 8).unwrap();


            let a = AffinePoint::alloc(&mut cs, Some(a_f), &params).unwrap();

            let b = AllocatedNum::alloc(&mut cs, || Ok(b_f)).unwrap();

            let b = Num::Variable(b);

            let endo_parameters = super::super::endomorphism::bn254_endomorphism_parameters();

            let res = a.clone().mul_split_scalar_entry_point(&mut cs, &b, endo_parameters.clone(), 2, &committer);

            let result_recalculated = a_f.mul(b_f.into_repr()).into_affine();

            assert!(cs.is_satisfied());

            // let x_fe = result.x.get_field_value().unwrap();
            // let y_fe = result.y.get_field_value().unwrap();

            // let (x, y) = result.get_value().unwrap().into_xy_unchecked();

            // assert_eq!(x_fe, x, "x coords mismatch between value and coordinates");
            // assert_eq!(y_fe, y, "y coords mismatch between value and coordinates");

            // let (x, y) = result_recalculated.into_xy_unchecked();

            // assert_eq!(
            //     x_fe, x,
            //     "x coords mismatch between expected result and circuit result"
            // );
            // assert_eq!(
            //     y_fe, y,
            //     "y coords mismatch between expected result and circuit result"
            // );

            // assert_eq!(
            //     result.get_value().unwrap(),
            //     result_recalculated,
            //     "mismatch between expected result and circuit result"
            // );

            // let (x, y) = a_f.into_xy_unchecked();
            // assert_eq!(
            //     a.x.get_field_value().unwrap(),
            //     x,
            //     "x coords mismatch, input was mutated"
            // );
            // assert_eq!(
            //     a.y.get_field_value().unwrap(),
            //     y,
            //     "y coords mismatch, input was mutated"
            // );

            if i == 0 {
                crate::plonk::circuit::counter::reset_counter();
                let base = cs.n();
                let _ = a.mul_split_scalar_entry_point(&mut cs, &b, endo_parameters, 2, &committer);
                println!("single multiplication taken {} gates", cs.n() - base);
                println!(
                    "Affine spent {} gates in equality checks",
                    crate::plonk::circuit::counter::output_counter()
                );
            }
        }
    }
    #[test]
    fn test_sew_table(){
        use plonk::circuit::utils::u64_to_fe;
        for i in 0..3{

            let (a, b) = vec_of_bit((3 as usize), 2);
            let f: Fr = u64_to_fe((b as u64));
            println!("{:?}", b);
            println!("{:?}", a);
            // let a_skew =compute_skewed_naf_table( &Some(f), Some(2));
            // println!("a_skew {:?}", a_skew);
            // println!("a {:?}", a);
            // println!("b {:?}", b);

            // {
            //     let mut two = Fr::one();
            //     two.double();
        
            //     let mut minus_one = Fr::one();
            //     minus_one.negate();
        
            //     let mut reconstructed = Fr::zero();
        
            //     let even_limit = (2 / 2) * 2;
        
            //     for i in (0..even_limit).step_by(2) {
            //         reconstructed.double();
            //         reconstructed.double();
        
            //         let high_bit = a_skew[i].unwrap();
            //         let mut high_contribution = if high_bit {
            //             minus_one
            //         } else {
            //             Fr::one()
            //         };
            //         high_contribution.double();
        
            //         let low_bit = a_skew[i+1].unwrap();
            //         let low_contribution = if low_bit {
            //             minus_one
            //         } else {
            //             Fr::one()
            //         };
        
            //         reconstructed.add_assign(&high_contribution);
            //         reconstructed.add_assign(&low_contribution);
            //     }
        
            //     if 2 & 1 == 1 {
            //         reconstructed.double();
        
            //         let last_bit = a_skew[2-1].unwrap();
            //         if last_bit {
            //             reconstructed.add_assign(&minus_one);
            //         } else {
            //             reconstructed.add_assign(&Fr::one());
            //         };
            //     }
        
            //     if a_skew.last().unwrap().unwrap() {
            //         reconstructed.add_assign(&minus_one);
            //     }
            //     use plonk::circuit::hashes_with_tables::utils::ff_to_u64;
            //     let result = ff_to_u64(&reconstructed);
            //     println!("{:?}", result);
            // }


        }


    }

    #[test]
    fn test_sign(){
        let a = sign_i64(12);
        println!("{:?}", a);
        
    }
    use plonk::circuit::bigint_new::inscribe_default_bitop_range_table;
    #[test]
    fn test_point_compresion(){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);
        let mut cs =
                TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();

        inscribe_default_bitop_range_table(&mut cs).unwrap();
        let a_f: G1Affine = rng.gen();


        let a = AffinePoint::alloc(&mut cs, Some(a_f), &params).unwrap();
        let naive_mul_end = cs.get_current_step_number();
        let (y_odd, _) = AffinePoint::point_compression(a.clone(), &mut cs).unwrap();
        let naive_mul_end = cs.get_current_step_number();
        let y_cord = a.y.clone();
        let limbs = y_cord.clone().into_limbs();
        let num_bits = y_cord.representation_params.binary_limbs_bit_widths[0];
        let rcd = constraint_bit_length_ext(&mut cs,  &limbs[0].num.get_variable(), num_bits).unwrap();

        let a = rcd.get_vars()[0];

        let vec_boolean = a.into_bits_le(&mut cs, Some(8)).unwrap();
        let y_odd_check = vec_boolean[0];
        assert!(cs.is_satisfied());

        assert_eq!(y_odd.get_variable().unwrap().get_value().unwrap(), y_odd_check.get_variable().unwrap().get_value().unwrap());
    }

    #[test]
    fn test_vec_boolean_to_nuber(){
        let vec_boolean = [Boolean::Constant(false), Boolean::Constant(false), Boolean::Constant(false)];
        let number = vec_boolean_to_usize(vec_boolean.to_vec());
        println!("{}", number);

    }

    #[test]
    fn test_plonktable_mul(){
        use rand::{Rng, SeedableRng, XorShiftRng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        let mut cs =
        TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();

        let b_f: Fr = rng.gen();

        let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);
        let b = AllocatedNum::alloc(&mut cs, || Ok(b_f)).unwrap();

        let b = Num::Variable(b);

        let mul_begin = cs.get_current_step_number();
        let point: AffinePoint<Bn256, G1Affine> = AffinePoint::mul_by_fixed_point(&mut cs, 2, &params, &b, Some(254)).unwrap();
        let mul_end = cs.get_current_step_number();
        println!("mul_begin{:?}", mul_begin);
        println!("mul_end{:?}", mul_end);
    }

    #[test]
    fn test_plonktable_mul_endo(){
        use rand::{Rng, SeedableRng, XorShiftRng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        let mut cs =
        TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();

        let b_f: Fr = rng.gen();

        let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);
        let b = AllocatedNum::alloc(&mut cs, || Ok(b_f)).unwrap();

        let b = Num::Variable(b);

        let endo_parameters = super::super::endomorphism::bn254_endomorphism_parameters();
        let mul_begin = cs.get_current_step_number();

        let point: AffinePoint<Bn256, G1Affine> = AffinePoint::mul_by_fixed_point_with_endo(
            &mut cs, 
            2,
            &params, 
            &b, 
            Some(254), 
            endo_parameters
        ).unwrap();

        let mul_end = cs.get_current_step_number();
        println!("mul_begin{:?}", mul_begin);
        println!("mul_end{:?}", mul_end);
    }
    
    #[test]
    fn test_decompose_into_binary_for_skew(){
        let mut cs =
        TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();
        let scalar = Fr::from_str("3").unwrap();
        let b = AllocatedNum::alloc(&mut cs, || Ok(scalar)).unwrap();
        let mul_begin = cs.get_current_step_number();
        let result = AffinePoint::decompose_into_binary_for_skew(&mut cs, &b, Some(254)).unwrap();
        let mul_end = cs.get_current_step_number();
        println!("mul_begin{:?}", mul_begin);
        println!("mul_end{:?}", mul_end);

    }

   
}