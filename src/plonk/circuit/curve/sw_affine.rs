use crate::bellman::pairing::{
    Engine,
    CurveAffine,
    CurveProjective
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
    Width4MainGateWithDNextEquation,
    MainGateEquation,
    GateEquationInternal,
    GateEquation,
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

#[derive(Clone, Debug)]
pub struct AffinePoint<'a, E: Engine, G: CurveAffine> where <G as CurveAffine>::Base: PrimeField {
    pub(crate) x: FieldElement<'a, E, G::Base>,
    pub(crate) y: FieldElement<'a, E, G::Base>,
    pub(crate) value: Option<G>,
}

impl<'a, E: Engine, G: CurveAffine> AffinePoint<'a, E, G> where <G as CurveAffine>::Base: PrimeField {
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

        let x = FieldElement::new_allocated(
            cs, 
            x, 
            params
        )?;

        let y = FieldElement::new_allocated(
            cs, 
            y, 
            params
        )?;

        let new = Self {
            x,
            y,
            value
        };

        Ok(new)
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

    pub fn is_constant(&self) -> bool {
        self.x.is_constant() & self.y.is_constant()
    }

    pub fn get_value(&self) -> Option<G> {
        self.value
    }

    pub fn add_unequal<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
        other: Self
    ) -> Result<(Self, (Self, Self)), SynthesisError> {
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
        let (other_y_negated, other_y) = other_y.negated(cs)?;
        
        // We may enforce it, but lambda calculation would not unsatisfiable if it's equal
        // this_x.enforce_not_equal(cs, &other_x)?;
        // this_y.enforce_not_equal(cs, &other_y)?;

        let (lambda, (mut tmp, _)) = FieldElement::div_from_addition_chain(cs, vec![other_y, this_y_negated], other_x_minus_this_x)?;

        let this_y_negated = tmp.pop().unwrap();
        let other_y = tmp.pop().unwrap();

        // lambda^2 + (-x' - x)
        let (new_x, (lambda, _)) = lambda.clone().square_with_addition_chain(cs, vec![other_x_negated, this_x_negated])?;

        // return Ok((this_copy.clone(), (this_copy.clone(), this_copy.clone())));

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

    pub fn sub_unequal<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
        other: Self
    ) -> Result<(Self, (Self, Self)), SynthesisError> {
        // since we are in a circuit we don't use projective coodinates cause inversions are
        // "cheap" in terms of constraints 

        // we also do not want to have branching here,
        // so this function implicitly requires that 
        // points are not equal

        // we need to calculate lambda = (y' - y)/(x' - x). We don't care about a particular
        // value of y' - y, so we don't add them explicitly and just use in inversion witness

        let params = self.x.representation_params;

        let this_value = self.get_value();
        let other_value = other.get_value();

        let this_x = self.x;
        let this_y = self.y;

        let other_x = other.x;
        let other_y = other.y;

        let this_x_base = this_x.base_field_limb.get_value().unwrap();
        let this_y_base = this_y.base_field_limb.get_value().unwrap();

        let other_x_base = other_x.base_field_limb.get_value().unwrap();
        let other_y_base = other_y.base_field_limb.get_value().unwrap();

        let (this_y_negated, this_y) = this_y.negated(cs)?;
        let (this_x_negated, this_x) = this_x.negated(cs)?;

        let (other_x_minus_this_x, (other_x, this_x_negated)) = other_x.add(cs, this_x_negated)?;

        // let (other_x_minus_this_x, (other_x, this_x)) = other_x.sub(cs, this_x)?;

        let (other_x_negated, other_x) = other_x.negated(cs)?;
        let (other_y_negated, other_y) = other_y.negated(cs)?;

        // We may enforce it, but lambda calculation would not unsatisfiable if it's equal
        // this_x.enforce_not_equal(cs, &other_x)?;
        // this_y.enforce_not_equal(cs, &other_y)?;

        // let (this_y_plus_other_y, (this_y, other_y)) = this_y.add(cs, other_y)?;

        // let (lambda, (_, other_x_minus_this_x)) = this_y_plus_other_y.div(cs, other_x_minus_this_x)?;

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
        // let (two_x_squared, (x_squared, _)) = x_squared.clone().add(cs, x_squared)?;
        let (three_x_squared, (two_x_squared, x_squared)) = two_x_squared.add(cs, x_squared)?;

        // Assume A == 0 for now

        let (two_y, y) = y.double(cs)?;
        // let (two_y, (y, _)) = y.clone().add(cs, y)?;

        let (lambda, _) = three_x_squared.div(cs, two_y)?;

        let (minus_x, x) = x.negated(cs)?;
        let (minus_y, y) = y.negated(cs)?;

        let (minus_two_x, minus_x) = minus_x.double(cs)?;
        // let (minus_two_x, (minus_x, _)) = minus_x.clone().add(cs, minus_x)?;

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

    pub fn double_and_add<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
        other: Self
    ) -> Result<(Self, (Self, Self)), SynthesisError> {
        // doubles self and adds other

        // even though https://www.researchgate.net/publication/283556724_New_Fast_Algorithms_for_Elliptic_Curve_Arithmetic_in_Affine_Coordinates exists
        // inversions are cheap, so Montgomery ladder is better

        let this_value = self.get_value();
        let other_value = other.get_value();

        let this_copy = self.clone();

        let this_x = self.x;
        let this_y = self.y;

        let other_x = other.x;
        let other_y = other.y;

        let (this_y_negated, this_y) = this_y.negated(cs)?;
        let (this_x_negated, this_x) = this_x.negated(cs)?;

        let (other_x_minus_this_x, (other_x, this_x_negated)) = other_x.add(cs, this_x_negated)?;

        let (other_x_negated, other_x) = other_x.negated(cs)?;
        let (other_y_negated, other_y) = other_y.negated(cs)?;

        let (lambda, (mut tmp, _)) = FieldElement::div_from_addition_chain(cs, vec![other_y, this_y_negated], other_x_minus_this_x)?;

        let this_y_negated = tmp.pop().unwrap();
        let other_y = tmp.pop().unwrap();

        // lambda^2 + (-x' - x)
        let (new_x, (lambda, mut tmp)) = lambda.square_with_addition_chain(cs, vec![other_x_negated, this_x_negated])?;

        let this_x_negated = tmp.pop().unwrap();

        let (new_x_minus_this_x, (new_x, this_x)) = new_x.sub(cs, this_x)?;

        let (two_y, this_y) = this_y.double(cs)?;
        // let (two_y, (this_y, _)) = this_y.clone().add(cs, this_y)?;

        let (t0, (two_y, new_x_minus_this_x)) = two_y.div(cs, new_x_minus_this_x)?;

        let (t1, (_, _)) = lambda.add(cs, t0)?;

        let (new_x_negated, new_x) = new_x.negated(cs)?;

        let (new_x, (t1, mut tmp)) = t1.square_with_addition_chain(cs, vec![this_x_negated, new_x_negated])?;

        let _ = tmp.pop().unwrap();
        let this_x_negated = tmp.pop().unwrap();

        let (new_x_minus_x, (new_x, this_x_negated)) = new_x.add(cs, this_x_negated)?;

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

    pub fn mul_by_fixed_scalar<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
        scalar: &G::Scalar
    ) -> Result<(Self, Self), SynthesisError> {
        unimplemented!()
    }

}

impl<'a, E: Engine> AffinePoint<'a, E, E::G1Affine> {
    pub fn mul<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
        scalar: &Num::<E>,
        bit_limit: Option<usize>
    ) -> Result<(Self, Self), SynthesisError> {
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

        // let offset_generator = E::G1Affine::one().mul(E::Fr::from_str("13579").unwrap().into_repr()).into_affine(); // TODO: for now
        let offset_generator = E::G1Affine::one(); // TODO: for now

        let generator = Self::constant(offset_generator, params);

        let (mut acc, (this, gen)) = self.add_unequal(cs, generator)?;

        let mut x = this.x;
        let y = this.y;

        let entries_without_first_and_last = &entries[1..(entries.len() - 1)];

        let mut num_doubles = 0;

        let (minus_y, y) = y.negated(cs)?;

        for e in entries_without_first_and_last.iter() {
            let (selected_y, _) = FieldElement::select(cs, e, minus_y.clone(), y.clone())?;  

            // let (t, (tt, y_negated)) = FieldElement::conditional_negation(cs, e, y)?;    

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

            // y = tt;
            let t = Self {
                x: x,
                y: selected_y,
                value: t_value
            };

            let (new_acc, (old_acc, t)) = acc.double_and_add(cs, t)?;

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
            top_limit = entries.len() - 1;
            entries_per_scalar.push(entries);
        }

        assert!(top_limit > 0);

        println!("Start making table");

        let table = super::multiexp_table::MultiexpTable::new(cs, points)?;

        println!("Table is ready");

        // we add a random point to the accumulator to avoid having zero anywhere (with high probability)
        // and unknown discrete log allows us to be "safe"
        let offset_generator = E::G1Affine::one(); // TODO: for now

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
            // println!("Q.x = {}, Q.y = {}", q.x.get_field_value().unwrap(), q.y.get_field_value().unwrap());

            let (new_acc, _) = acc.double_and_add(cs, q)?;

            num_doubles += 1;
            acc = new_acc;

            current_round_entries.truncate(0);
        }

        println!("acc value = {}", acc.get_value().unwrap());

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
}

fn decompose_allocated_num_into_skewed_table<E: Engine, CS: ConstraintSystem<E>>(
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

    let offset_generator = E::G1Affine::one(); 
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

    use crate::bellman::pairing::bn256::{Fq, Bn256, Fr, G1Affine};

    #[test]
    fn test_add_on_random_witnesses(){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

        for i in 0..100 {
            let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNextEquation>::new();

            let a_f: G1Affine = rng.gen();
            let b_f: G1Affine = rng.gen();
            let a = AffinePoint::alloc(
                &mut cs, 
                Some(a_f), 
                &params
            ).unwrap();

            let (x, y) = b_f.into_xy_unchecked();

            let mut x_negated = x;
            x_negated.negate();
            println!("X negated = {}", x_negated);

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
            let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNextEquation>::new();

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
            let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNextEquation>::new();

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
            let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNextEquation>::new();

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
            let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNextEquation>::new();

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
                let _ = a.double_and_add(&mut cs, b).unwrap();
                println!("Single double and add taken {} gates", cs.n() - base);
            }
        }
    }

    #[test]
    fn test_skewed_decomposition_on_random_witnesses(){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for i in 0..100 {
            let a_f: Fr = rng.gen();

            let _ = compute_skewed_naf_table(&Some(a_f), None);
            
        }
    }

    #[test]
    fn test_allocated_skewed_decomposition_on_random_witnesses(){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for i in 0..100 {
            let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNextEquation>::new();

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
            let mut cs = TrivialAssembly::<Bls12, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNextEquation>::new();

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
            let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNextEquation>::new();

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
    
            let (result, a) = a.mul(&mut cs, &b, Some(2)).unwrap();

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
            let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNextEquation>::new();

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
                let _ = a.mul(&mut cs, &b, None).unwrap();
                println!("Single multiplication taken {} gates", cs.n() - base);
            }
        }
    }

    #[test]
    fn test_base_curve_multiexp_1_on_random_witnesses(){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

        for i in 0..10 {
            let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNextEquation>::new();

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
            let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNextEquation>::new();

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

            println!("x from limbs = {}", result.x.get_field_value().unwrap());
            println!("x from value = {}", result.get_value().unwrap().into_xy_unchecked().0);
            println!("expected x = {}", result_recalculated.into_xy_unchecked().0);

            let (x, y) = result.get_value().unwrap().into_xy_unchecked();

            assert_eq!(x_fe, x, "x coords mismatch");
            assert_eq!(y_fe, y, "y coords mismatch");

            let (x, y) = result_recalculated.into_xy_unchecked();

            assert_eq!(x_fe, x, "x coords mismatch");
            assert_eq!(y_fe, y, "y coords mismatch");

            if i == 0 {
                let base = cs.n();
                let _ = AffinePoint::multiexp(&mut cs, &b_n, &a_p, None).unwrap();
                println!("Two points multiexp taken {} gates", cs.n() - base);
            }
        }
    }

    #[test]
    fn test_base_curve_multiexp_10_on_random_witnesses(){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

        for i in 0..10 {
            let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNextEquation>::new();

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

            // let x_fe = result.x.get_field_value().unwrap();
            // let y_fe = result.y.get_field_value().unwrap();

            // println!("x from limbs = {}", result.x.get_field_value().unwrap());
            // println!("x from value = {}", result.get_value().unwrap().into_xy_unchecked().0);
            // println!("expected x = {}", result_recalculated.into_xy_unchecked().0);

            // let (x, y) = result.get_value().unwrap().into_xy_unchecked();

            // assert_eq!(x_fe, x, "x coords mismatch");
            // assert_eq!(y_fe, y, "y coords mismatch");

            // let (x, y) = result_recalculated.into_xy_unchecked();

            // assert_eq!(x_fe, x, "x coords mismatch");
            // assert_eq!(y_fe, y, "y coords mismatch");

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
        let params = RnsParameters::<Bls12, Fq>::new_for_field(68, 110, 8);

        for i in 0..10 {
            let mut cs = TrivialAssembly::<Bls12, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNextEquation>::new();

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

            // let x_fe = result.x.get_field_value().unwrap();
            // let y_fe = result.y.get_field_value().unwrap();

            // println!("x from limbs = {}", result.x.get_field_value().unwrap());
            // println!("x from value = {}", result.get_value().unwrap().into_xy_unchecked().0);
            // println!("expected x = {}", result_recalculated.into_xy_unchecked().0);

            // let (x, y) = result.get_value().unwrap().into_xy_unchecked();

            // assert_eq!(x_fe, x, "x coords mismatch");
            // assert_eq!(y_fe, y, "y coords mismatch");

            // let (x, y) = result_recalculated.into_xy_unchecked();

            // assert_eq!(x_fe, x, "x coords mismatch");
            // assert_eq!(y_fe, y, "y coords mismatch");

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
}