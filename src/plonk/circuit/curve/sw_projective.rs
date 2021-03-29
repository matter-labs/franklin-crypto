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

#[derive(Clone, Debug)]
pub struct PointProjective<'a, E: Engine, G: GenericCurveAffine> where <G as GenericCurveAffine>::Base: PrimeField {
    pub x: FieldElement<'a, E, G::Base>,
    pub y: FieldElement<'a, E, G::Base>,
    pub z: FieldElement<'a, E, G::Base>,
    pub value: Option<G::Projective>,
}

impl<'a, E: Engine, G: GenericCurveAffine> PointProjective<'a, E, G> where <G as GenericCurveAffine>::Base: PrimeField {
    pub fn get_x(&self) -> FieldElement<'a, E, G::Base> {
        self.x.clone()
    }

    pub fn get_y(&self) -> FieldElement<'a, E, G::Base> {
        self.y.clone()
    }

    pub fn get_z(&self) -> FieldElement<'a, E, G::Base> {
        self.z.clone()
    }

    pub fn alloc_from_affine_non_zero<CS: ConstraintSystem<E>>(
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

        let val = if let Some(value) = value {
            Some(value.into_projective())
        } else {
            None
        };

        let x = FieldElement::new_allocated(
            cs, 
            x, 
            params
        )?;

        let (x_is_zero, x) = x.is_zero(cs)?;

        let y = FieldElement::new_allocated(
            cs, 
            y, 
            params
        )?;

        let (y_is_zero, y) = y.is_zero(cs)?;

        Boolean::enforce_equal(cs, &x_is_zero, &Boolean::constant(false))?;
        Boolean::enforce_equal(cs, &y_is_zero, &Boolean::constant(false))?;

        let z = FieldElement::new_constant(G::Base::one(), params);

        let new = Self {
            x,
            y,
            z,
            value: val
        };

        Ok(new)
    }

    pub fn alloc_from_affine_may_be_zero<CS: ConstraintSystem<E>>(
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

        let val = if let Some(value) = value {
            Some(value.into_projective())
        } else {
            None
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

        let z = FieldElement::new_constant(G::Base::one(), params);

        let new = Self {
            x,
            y,
            z,
            value: val
        };

        Ok(new)
    }

    pub fn constant_from_affine(
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

        let z = FieldElement::new_constant(G::Base::one(), params);

        let new = Self {
            x,
            y,
            z,
            value: Some(value.into_projective())
        };

        new
    }

    pub fn zero(
        params: &'a RnsParameters<E, G::Base>
    ) -> Self
    {
        let x = FieldElement::zero(params);
        let y = FieldElement::one(params);
        let z = FieldElement::zero(params);

        let new = Self {
            x,
            y,
            z,
            value: Some(G::Projective::zero())
        };

        new
    }

    pub fn is_constant(&self) -> bool {
        self.x.is_constant() & self.y.is_constant() & self.z.is_constant()
    }

    pub fn get_value(&self) -> Option<G> {
        self.value.map(|el| el.into_affine())
    }

    pub fn equals<CS: ConstraintSystem<E>>(
        &self,
        _cs: &mut CS,
        _other: &Self,
    ) -> Result<Boolean, SynthesisError> 
    {
        Ok(Boolean::constant(false))
        // let x_check = self.x.equals(cs, &other.x)?;
        // let y_check = self.y.equals(cs, &other.y)?;
        // Boolean::and(cs, &x_check, &y_check)
    }

    pub fn negate<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
    ) -> Result<(Self, Self), SynthesisError> {
        let this_value = self.value;

        let this_x = self.x;
        let this_y = self.y;
        let this_z = self.z;

        let (this_y_negated, this_y) = this_y.negated(cs)?;
       
        let new_value = this_value.map(|el| {
            let mut t = el;
            t.negate();

            t
        });
   
        let new = Self {
            x: this_x.clone(),
            y: this_y_negated,
            z: this_z.clone(),
            value: new_value
        };

        let this = Self {
            x: this_x,
            y: this_y,
            z: this_z,
            value: this_value
        };

        Ok((new, this))
    }

    #[allow(unused_variables)]
    #[track_caller]
    pub fn add<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
        other: Self
    ) -> Result<(Self, (Self, Self)), SynthesisError> {
        let params = self.x.representation_params;

        let curve_b = G::b_coeff();
        let b = FieldElement::new_constant(
            curve_b,
            params
        );
        let this_value = self.value;
        let other_value = other.value;

        let x1 = self.x;
        let y1 = self.y;
        let z1 = self.z;

        let x2 = other.x;
        let y2 = other.y;
        let z2 = other.z;

        // exception free addition in projective coordiantes

        // 1. t0 ← X1 · X2 
        let (t0, (x1, x2)) = x1.mul(cs, x2)?;
        // 2. t1 ← Y1 · Y2 
        let (t1, (y1, y2)) = y1.mul(cs, y2)?;
        // 3. t2 ← Z1 · Z2
        let (t2, (z1, z2)) = z1.mul(cs, z2)?;
        // 4. t3 ← X1 + Y1 
        let (t3, (x1, y1)) = x1.add(cs, y1)?;
        // 5. t4 ← X2 + Y2 
        let (t4, (x2, y2)) = x2.add(cs, y2)?;
        // 6. t3 ← t3 · t4
        let (t3, _) = t3.mul(cs, t4)?;
        // 7. t4 ← t0 + t1 
        let (t4, (t0, t1)) = t0.add(cs, t1)?;
        // 8. t3 ← t3 − t4 
        let (t3, (_, t4)) = t3.sub(cs, t4)?;
        // 9. t4 ← Y1 + Z1
        let (t4, (y1, z1)) = y1.add(cs, z1)?;
        // 10. X3 ← Y2 + Z2 
        let (x3, (y2, z2)) = y2.add(cs, z2)?;
        // 11. t4 ← t4 · X3 
        let (t4, (_, x3)) = t4.mul(cs, x3)?;
        // 12. X3 ← t1 + t2
        let (x3, (t1, t2)) = t1.add(cs, t2)?;
        // 13. t4 ← t4 − X3 
        let (t4, (_, x3)) = t4.sub(cs, x3)?;
        // 14. X3 ← X1 + Z1 
        let (x3, (x1, z1)) = x1.add(cs, z1)?;
        // 15. Y3 ← X2 + Z2
        let (y3, (x2, z2)) = x2.add(cs, z2)?;
        // 16. X3 ← X3 · Y3 
        let (x3, (_, y3)) = x3.mul(cs, y3)?;
        // 17. Y3 ← t0 + t2 
        let (y3, (t0, t2)) = t0.add(cs, t2)?;
        // 18. Y3 ← X3 − Y3
        let (y3, (x3, _)) = x3.sub(cs, y3)?;
        // 19. X3 ← t0 + t0 
        let (x3, t0) = t0.double(cs)?;
        // 20. t0 ← X3 + t0 
        let (t0, (x3, _)) = x3.add(cs, t0)?;
        // 21. t2 ← b3 · t2
        let (t2, _) = b.clone().mul(cs, t2)?;
        // 22. Z3 ← t1 + t2 
        let (z3, (t1, t2)) = t1.add(cs, t2)?;
        // 23. t1 ← t1 − t2 
        let (t1, (_, t2)) = t1.sub(cs, t2)?;
        // 24. Y3 ← b3 · Y3
        let (y3, _) = b.mul(cs, y3)?;
        // 25. X3 ← t4 · Y3 
        let (x3, (t4, y3)) = t4.mul(cs, y3)?;
        // 26. t2 ← t3 · t1 
        let (t2, (t3, t1)) = t3.mul(cs, t1)?;
        // 27. X3 ← t2 − X3
        let (x3, (t2, _)) = t2.sub(cs, x3)?;
        // 28. Y3 ← Y3 · t0 
        let (y3, (_, t0)) = y3.mul(cs, t0)?;
        // 29. t1 ← t1 · Z3 
        let (t1, (_, z3)) = t1.mul(cs, z3)?;
        // 30. Y3 ← t1 + Y3
        let (y3, (t1, _)) = t1.add(cs, y3)?;
        // 31. t0 ← t0 · t3 
        let (t0, (_, t3)) = t0.mul(cs, t3)?;
        // 32. Z3 ← Z3 · t4 
        let (z3, (_, t4)) = z3.mul(cs, t4)?;
        // 33. Z3 ← Z3 + t0
        let (z3, _) = z3.add(cs, t0)?;

        let new_value = match (this_value, other_value) {
            (Some(this), Some(other)) => {
                assert!(this != other);
                let mut tmp = this;
                tmp.add_assign(&other);

                Some(tmp)
            },
            _ => None
        };
   
        let new = Self {
            x: x3,
            y: y3,
            z: z3,
            value: new_value
        };

        let this = Self {
            x: x1,
            y: y1,
            z: z1,
            value: this_value
        };

        let other = Self {
            x: x2,
            y: y2,
            z: z2,
            value: other_value
        };

        Ok((new, (this, other)))
    }

    // #[track_caller]
    // pub fn sub_unequal<CS: ConstraintSystem<E>>(
    //     self,
    //     cs: &mut CS,
    //     other: Self
    // ) -> Result<(Self, (Self, Self)), SynthesisError> {
    //     // since we are in a circuit we don't use projective coodinates cause inversions are
    //     // "cheap" in terms of constraints 

    //     // we also do not want to have branching here,
    //     // so this function implicitly requires that 
    //     // points are not equal

    //     // we need to calculate lambda = (y' - y)/(x' - x). We don't care about a particular
    //     // value of y' - y, so we don't add them explicitly and just use in inversion witness

    //     let params = self.x.representation_params;

    //     let this_value = self.get_value();
    //     let other_value = other.get_value();

    //     let this_x = self.x;
    //     let this_y = self.y;

    //     let other_x = other.x;
    //     let other_y = other.y;

    //     let (this_y_negated, this_y) = this_y.negated(cs)?;
    //     let (this_x_negated, this_x) = this_x.negated(cs)?;

    //     let (other_x_minus_this_x, (other_x, this_x_negated)) = other_x.add(cs, this_x_negated)?;

    //     let (other_x_negated, other_x) = other_x.negated(cs)?;
    //     let (other_y_negated, other_y) = other_y.negated(cs)?;

    //     this_x.enforce_not_equal(cs, &other_x).expect("points have equal X coordinates in subtraction function");
    //     this_y.enforce_not_equal(cs, &other_y).expect("points have equal Y coordinates in subtraction function");

    //     let (lambda, (mut tmp, _)) = FieldElement::div_from_addition_chain(cs, vec![other_y, this_y], other_x_minus_this_x)?;

    //     let this_y = tmp.pop().unwrap();
    //     let other_y = tmp.pop().unwrap();

    //     // lambda^2 + (-x' - x)
    //     let (new_x, (lambda, _)) = lambda.clone().square_with_addition_chain(cs, vec![other_x_negated, this_x_negated])?;

    //     // lambda * -(x - new_x) + (- y)

    //     let (new_x_minus_this_x, (new_x, this_x)) = new_x.sub(cs, this_x)?;
        
    //     let (new_y, _) = lambda.fma_with_addition_chain(cs, new_x_minus_this_x, vec![this_y_negated])?;

    //     let new_value = match (this_value, other_value) {
    //         (Some(this), Some(other)) => {
    //             assert!(this != other);
    //             let mut tmp = this.into_projective();
    //             let mut t0 = other;
    //             t0.negate();
    //             tmp.add_assign_mixed(&t0);

    //             Some(tmp.into_affine())
    //         },
    //         _ => None
    //     };
   
    //     let new = Self {
    //         x: new_x,
    //         y: new_y,
    //         value: new_value
    //     };

    //     let this = Self {
    //         x: this_x,
    //         y: this_y,
    //         value: this_value
    //     };

    //     let other = Self {
    //         x: other_x,
    //         y: other_y,
    //         value: other_value
    //     };


    //     Ok((new, (this, other)))
    // }

    #[allow(unused_variables)]
    #[track_caller]
    pub fn double<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
    ) -> Result<(Self, Self), SynthesisError> {

        let params = self.x.representation_params;

        let curve_b = G::b_coeff();
        let b = FieldElement::new_constant(
            curve_b,
            params
        );
        let this_value = self.value;

        let x = self.x;
        let y = self.y;
        let z = self.z;

        // 1. t0 ← Y · Y 
        let (t0, y) = y.square(cs)?;
        // 2. Z3 ← t0 + t0 
        let (z3, t0) = t0.double(cs)?;
        // 3. Z3 ← Z3 + Z3
        let (z3, _) = z3.double(cs)?;
        // 4. Z3 ← Z3 + Z3 
        let (z3, _) = z3.double(cs)?;
        // 5. t1 ← Y · Z 
        let (t1, (y, z)) = y.mul(cs, z)?;
        // 6. t2 ← Z · Z
        let (t2, z) = z.square(cs)?;
        // 7. t2 ← b3 · t2 
        let (t2, _) = b.mul(cs, t2)?;
        // 8. X3 ← t2 · Z3 
        let (x3, (t2, z3)) = t2.mul(cs, z3)?;
        // 9. Y3 ← t0 + t2
        let (y3, (t0, t2)) = t0.add(cs, t2)?;
        // 10. Z3 ← t1 · Z3 
        let (z3, (t1, _)) = t1.mul(cs, z3)?;
        // 11. t1 ← t2 + t2 
        let (t1, t2) = t2.double(cs)?;
        // 12. t2 ← t1 + t2
        let (t2, (t1, _)) = t1.add(cs, t2)?;
        // 13. t0 ← t0 − t2 
        let (t0, (_, t2)) = t0.sub(cs, t2)?;
        // 14. Y3 ← t0 · Y3 
        let (y3, (t0, _)) = t0.mul(cs, y3)?;
        // 15. Y3 ← X3 + Y3
        let (y3, (x3, _)) = x3.add(cs, y3)?;
        // 16. t1 ← X · Y 
        let (t1, (x, y)) = x.mul(cs, y)?;
        // 17. X3 ← t0 · t1 
        let (x3, (t0, t1)) = t0.mul(cs, t1)?;
        // 18. X3 ← X3 + X3
        let (x3, _) = x3.double(cs)?;

        let new_value = this_value.map(|el| {
            let mut tmp = el;
            tmp.double();

            tmp
        });
   
        let new = Self {
            x: x3,
            y: y3,
            z: z3,
            value: new_value
        };

        let this = Self {
            x: x,
            y: y,
            z: z,
            value: this_value
        };

        Ok((new, this))
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

        let first_value = first.value;
        let second_value = second.value;
        let (x, (first_x, second_x)) = FieldElement::select(cs, flag, first.x, second.x)?;
        let (y, (first_y, second_y)) = FieldElement::select(cs, flag, first.y, second.y)?;
        let (z, (first_z, second_z)) = FieldElement::select(cs, flag, first.z, second.z)?;

        let value = match (flag.get_value(), first_value, second_value) {
            (Some(true), Some(p), _) => Some(p),
            (Some(false), _, Some(p)) => Some(p),
            (_, _, _) => None
        };

        let selected = Self { 
            x: x, 
            y: y, 
            z: z,
            value 
        };

        let first = Self {
            x: first_x,
            y: first_y,
            z: first_z,
            value: first_value
        };

        let second = Self {
            x: second_x,
            y: second_y,
            z: second_z,
            value: second_value
        };

        Ok((selected, (first, second)))
    }

    // #[track_caller]
    // pub fn is_on_curve_for_zero_a<CS: ConstraintSystem<E>>(
    //     self,
    //     cs: &mut CS,
    //     curve_b: G::Base
    // ) -> Result<(Boolean, Self), SynthesisError> {
    //     let params = self.x.representation_params;
    //     assert_eq!(curve_b, G::b_coeff());
    //     let b = FieldElement::new_constant(curve_b, params);

    //     let x = self.x;
    //     let y = self.y;
    //     let value = self.value;

    //     let (lhs, y) = y.square(cs)?;
    //     let (x_squared, x) = x.square(cs)?;
    //     let (x_cubed, (x_squared, x)) = x_squared.mul(cs, x)?;

    //     let (rhs, _) = x_cubed.add(cs, b)?;

    //     // account for lazy addition
    //     let rhs = rhs.force_reduce_into_field(cs)?;

    //     let is_on_curve = lhs.equals(cs, &rhs)?;

    //     let p = Self {
    //         x,
    //         y,
    //         value
    //     };


    //     Ok((is_on_curve, p))
    // }
}

impl<'a, E: Engine> PointProjective<'a, E, E::G1Affine> {
    #[allow(unused_variables)]
    #[track_caller]
    pub fn mul<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
        scalar: &Num::<E>,
        _bit_limit: Option<usize>
    ) -> Result<(Self, Self), SynthesisError> {
        if let Some(value) = scalar.get_value() {
            assert!(!value.is_zero(), "can not multiply by zero in the current approach");
        }
        if scalar.is_constant() {
            return self.mul_by_fixed_scalar(cs, &scalar.get_value().unwrap());
        }

        let params = self.x.representation_params;
        let this = self.clone();
        let mut this_copy = self.clone();

        // scalar is not constant, so we first decompose it

        let v = scalar.get_variable();
        let bits = v.into_bits_le(cs, None)?;

        let mut result = Self::zero(params);
        for b in bits.iter().rev() {
            let (result_doubled, result_copy) = result.double(cs)?;
            let (result_doubled_and_added, (result_doubled, t)) = result_doubled.add(cs, this_copy)?;
            this_copy = t;
            let (selected_result, _) = Self::select(cs, b, result_doubled_and_added, result_doubled)?;
            result = selected_result;
        }

        match (scalar.get_value(), self.get_value(), result.get_value()) {
            (Some(scalar), Some(value), Some(result)) => {
                let tmp = value.mul(scalar.into_repr());
                assert_eq!(tmp.into_affine(), result);
            },
            _ => {}
        }


        Ok((result, this))
    }

    // #[track_caller]
    // pub fn multiexp<CS: ConstraintSystem<E>>(
    //     cs: &mut CS,
    //     scalars: &[Num::<E>],
    //     points: &[Self],
    //     bit_limit: Option<usize>
    // ) -> Result<Self, SynthesisError> {
    //     assert_eq!(scalars.len(), points.len());

    //     let params = points[0].x.representation_params;

    //     let mut entries_per_scalar = Vec::with_capacity(scalars.len());

    //     let mut top_limit = 0;

    //     for s in scalars.iter() {
    //         let v = s.get_variable();
    //         let entries = decompose_allocated_num_into_skewed_table(cs, &v, bit_limit)?;
    //         if top_limit == 0 {
    //             top_limit = entries.len() - 1;
    //         } else {
    //             assert_eq!(top_limit, entries.len() - 1);
    //         }
    //         entries_per_scalar.push(entries);
    //     }

    //     assert!(top_limit > 0);

    //     let table = super::multiexp_table::MultiexpTable::new(cs, points)?;

    //     // we add a random point to the accumulator to avoid having zero anywhere (with high probability)
    //     // and unknown discrete log allows us to be "safe"

    //     let offset_generator = crate::constants::make_random_points_with_unknown_discrete_log::<E>(
    //         &crate::constants::MULTIEXP_DST[..], 
    //         1
    //     )[0];

    //     let generator = Self::constant(offset_generator, params);

    //     let base = table.make_base(cs)?;

    //     let (mut acc, _) = base.add_unequal(cs, generator)?;

    //     let mut current_round_entries = Vec::with_capacity(scalars.len());
    //     let mut num_doubles = 0;

    //     for bit_idx in 1..top_limit {
    //         for entry in entries_per_scalar.iter() {
    //             let e = entry[bit_idx].clone();
    //             current_round_entries.push(e);
    //         }

    //         assert_eq!(current_round_entries.len(), table.width);

    //         let q = table.lookup_for_skewed_entries(cs, &current_round_entries)?;

    //         let (new_acc, _) = acc.double_and_add(cs, q)?;

    //         num_doubles += 1;
    //         acc = new_acc;

    //         current_round_entries.truncate(0);
    //     }

    //     // subtract

    //     for (p, entry) in points.iter().zip(entries_per_scalar.into_iter()) {
    //         let (with_skew, (acc_original, _)) = acc.sub_unequal(cs, p.clone())?;

    //         let last_entry = entry.last().unwrap();

    //         let with_skew_value = with_skew.get_value();
    //         let with_skew_x = with_skew.x;
    //         let with_skew_y = with_skew.y;

    //         let acc_value = acc_original.get_value();
    //         let acc_x = acc_original.x;
    //         let acc_y = acc_original.y;

    //         let final_value = match (with_skew_value, acc_value, last_entry.get_value()) {
    //             (Some(s_value), Some(a_value), Some(b)) => {
    //                 if b {
    //                     Some(s_value)
    //                 } else {
    //                     Some(a_value)
    //                 }
    //             },
    //             _ => None
    //         };

    //         let (final_acc_x, _) = FieldElement::select(cs, last_entry, with_skew_x, acc_x)?;
    //         let (final_acc_y, _) = FieldElement::select(cs, last_entry, with_skew_y, acc_y)?;

    //         let result = Self {
    //             x: final_acc_x,
    //             y: final_acc_y,
    //             value: final_value
    //         };

    //         acc = result;
    //     }
        
    //     let shift = BigUint::from(1u64) << num_doubles;
    //     let as_scalar_repr = biguint_to_repr::<E::Fr>(shift);
    //     let offset_value = offset_generator.mul(as_scalar_repr).into_affine();
    //     let offset = Self::constant(offset_value, params);

    //     let (result, _) = acc.sub_unequal(cs, offset)?;

    //     Ok(result)
    // }
}

#[allow(unused_variables)]
#[cfg(test)]
mod test {
    use super::*;

    use crate::plonk::circuit::*;
    use crate::bellman::pairing::bn256::{Fq, Bn256, Fr, G1Affine};

    #[test]
    fn test_add_on_random_witnesses(){
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
    
        for i in 0..100 {
            let mut cs = TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();
            inscribe_default_range_table_for_bit_width_over_first_three_columns(&mut cs, 17).unwrap();
            reset_stats();
            let a_f: G1Affine = rng.gen();
            let b_f: G1Affine = rng.gen();
            let a = PointProjective::alloc_from_affine_non_zero(
                &mut cs, 
                Some(a_f), 
                &params
            ).unwrap();

            let b = PointProjective::alloc_from_affine_non_zero(
                &mut cs, 
                Some(b_f), 
                &params
            ).unwrap();

            let mut addition_result = a_f.into_projective();
            addition_result.add_assign_mixed(&b_f);

            let addition_result = addition_result.into_affine();
    
            let (result, (a, b)) = a.add(&mut cs, b).unwrap();

            assert!(cs.is_satisfied());

            let x_fe = result.x.get_field_value().unwrap();
            let y_fe = result.y.get_field_value().unwrap();
            let z_fe = result.y.get_field_value().unwrap();

            let (x, y) = result.get_value().unwrap().into_xy_unchecked();

            // assert_eq!(x_fe, x, "x coords mismatch");
            // assert_eq!(y_fe, y, "y coords mismatch");

            let (x, y) = a_f.into_xy_unchecked();
            assert_eq!(a.x.get_field_value().unwrap(), x, "x coords mismatch");
            assert_eq!(a.y.get_field_value().unwrap(), y, "y coords mismatch");

            let (x, y) = b_f.into_xy_unchecked();
            assert_eq!(b.x.get_field_value().unwrap(), x, "x coords mismatch");
            assert_eq!(b.y.get_field_value().unwrap(), y, "y coords mismatch");

            print_stats();

            if i == 0 {
                let base = cs.n();
                let _ = a.add(&mut cs, b).unwrap();
                println!("Single addition taken {} gates", cs.n() - base);
            }
        }
    }


    // #[test]
    // fn test_add_with_constant_on_random_witnesses(){
    //     use rand::{XorShiftRng, SeedableRng, Rng};
    //     let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    //     let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

    //     for i in 0..100 {
    //         let mut cs = TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();

    //         let a_f: G1Affine = rng.gen();
    //         let b_f: G1Affine = rng.gen();
    //         let a = AffinePoint::alloc(
    //             &mut cs, 
    //             Some(a_f), 
    //             &params
    //         ).unwrap();

    //         let b = AffinePoint::constant(
    //             b_f,
    //             &params
    //         );
    
    //         let (result, (a, b)) = a.add_unequal(&mut cs, b).unwrap();

    //         assert!(cs.is_satisfied());

    //         let x_fe = result.x.get_field_value().unwrap();
    //         let y_fe = result.y.get_field_value().unwrap();

    //         let (x, y) = result.get_value().unwrap().into_xy_unchecked();

    //         assert_eq!(x_fe, x, "x coords mismatch");
    //         assert_eq!(y_fe, y, "y coords mismatch");

    //         let (x, y) = a_f.into_xy_unchecked();
    //         assert_eq!(a.x.get_field_value().unwrap(), x, "x coords mismatch");
    //         assert_eq!(a.y.get_field_value().unwrap(), y, "y coords mismatch");

    //         let (x, y) = b_f.into_xy_unchecked();
    //         assert_eq!(b.x.get_field_value().unwrap(), x, "x coords mismatch");
    //         assert_eq!(b.y.get_field_value().unwrap(), y, "y coords mismatch");

    //         if i == 0 {
    //             let base = cs.n();
    //             let _ = a.add_unequal(&mut cs, b).unwrap();
    //             println!("Single addition with constant taken {} gates", cs.n() - base);
    //         }
    //     }
    // }

    // #[test]
    // fn test_sub_on_random_witnesses(){
    //     use rand::{XorShiftRng, SeedableRng, Rng};
    //     let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    //     let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

    //     for i in 0..100 {
    //         let mut cs = TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();

    //         let a_f: G1Affine = rng.gen();
    //         let b_f: G1Affine = rng.gen();
    //         let a = AffinePoint::alloc(
    //             &mut cs, 
    //             Some(a_f), 
    //             &params
    //         ).unwrap();

    //         let b = AffinePoint::alloc(
    //             &mut cs, 
    //             Some(b_f), 
    //             &params
    //         ).unwrap();
    
    //         let (result, (a, b)) = a.sub_unequal(&mut cs, b).unwrap();

    //         assert!(cs.is_satisfied());

    //         let x_fe = result.x.get_field_value().unwrap();
    //         let y_fe = result.y.get_field_value().unwrap();

    //         let (x, y) = result.get_value().unwrap().into_xy_unchecked();

    //         assert_eq!(x_fe, x, "x coords mismatch");
    //         assert_eq!(y_fe, y, "y coords mismatch");

    //         let (x, y) = a_f.into_xy_unchecked();
    //         assert_eq!(a.x.get_field_value().unwrap(), x, "x coords mismatch");
    //         assert_eq!(a.y.get_field_value().unwrap(), y, "y coords mismatch");

    //         let (x, y) = b_f.into_xy_unchecked();
    //         assert_eq!(b.x.get_field_value().unwrap(), x, "x coords mismatch");
    //         assert_eq!(b.y.get_field_value().unwrap(), y, "y coords mismatch");

    //         if i == 0 {
    //             let base = cs.n();
    //             let _ = a.sub_unequal(&mut cs, b).unwrap();
    //             println!("Single subtraction taken {} gates", cs.n() - base);
    //         }
    //     }
    // }

    // #[test]
    // fn test_double_on_random_witnesses(){
    //     use rand::{XorShiftRng, SeedableRng, Rng};
    //     let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    //     let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

    //     for i in 0..100 {
    //         let mut cs = TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();

    //         let a_f: G1Affine = rng.gen();

    //         let a = AffinePoint::alloc(
    //             &mut cs, 
    //             Some(a_f), 
    //             &params
    //         ).unwrap();
    
    //         let (result, a) = a.double(&mut cs).unwrap();

    //         assert!(cs.is_satisfied());

    //         let x_fe = result.x.get_field_value().unwrap();
    //         let y_fe = result.y.get_field_value().unwrap();

    //         let (x, y) = result.get_value().unwrap().into_xy_unchecked();

    //         assert_eq!(x_fe, x, "x coords mismatch");
    //         assert_eq!(y_fe, y, "y coords mismatch");

    //         let (x, y) = a_f.into_xy_unchecked();
    //         assert_eq!(a.x.get_field_value().unwrap(), x, "x coords mismatch");
    //         assert_eq!(a.y.get_field_value().unwrap(), y, "y coords mismatch");

    //         if i == 0 {
    //             let base = cs.n();
    //             let _ = a.double(&mut cs).unwrap();
    //             println!("Single double taken {} gates", cs.n() - base);
    //         }
    //     }
    // }

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

            let a = PointProjective::alloc_from_affine_non_zero(
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

            // let x_fe = result.x.get_field_value().unwrap();
            // let y_fe = result.y.get_field_value().unwrap();

            // let (x, y) = result.get_value().unwrap().into_xy_unchecked();

            // assert_eq!(x_fe, x, "x coords mismatch between value and coordinates");
            // assert_eq!(y_fe, y, "y coords mismatch between value and coordinates");

            // let (x, y) = result_recalculated.into_xy_unchecked();

            // assert_eq!(x_fe, x, "x coords mismatch between expected result and circuit result");
            // assert_eq!(y_fe, y, "y coords mismatch between expected result and circuit result");

            // assert_eq!(result.get_value().unwrap(), result_recalculated, "mismatch between expected result and circuit result");

            // let (x, y) = a_f.into_xy_unchecked();
            // assert_eq!(a.x.get_field_value().unwrap(), x, "x coords mismatch, input was mutated");
            // assert_eq!(a.y.get_field_value().unwrap(), y, "y coords mismatch, input was mutated");

            if i == 0 {
                reset_stats();
                crate::plonk::circuit::counter::reset_counter();
                let base = cs.n();
                let _ = a.mul(&mut cs, &b, None).unwrap();
                println!("Projective single multiplication taken {} gates", cs.n() - base);
                println!("Projective spent {} gates in equality checks", crate::plonk::circuit::counter::output_counter());
                print_stats();
            }
        }
    }

    // #[test]
    // fn test_base_curve_multiexp_1_on_random_witnesses(){
    //     use rand::{XorShiftRng, SeedableRng, Rng};
    //     let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    //     let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

    //     for i in 0..10 {
    //         let mut cs = TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();

    //         let a_f: G1Affine = rng.gen();
    //         let b_f: Fr = rng.gen();

    //         let a = AffinePoint::alloc(
    //             &mut cs, 
    //             Some(a_f), 
    //             &params
    //         ).unwrap();

    //         let b = AllocatedNum::alloc(
    //             &mut cs, 
    //             || {
    //                 Ok(b_f)
    //             }
    //         ).unwrap();

    //         let b = Num::Variable(b);

    //         let result = AffinePoint::multiexp(&mut cs, &[b.clone()], &[a.clone()], None).unwrap();

    //         let result_recalculated = a_f.mul(b_f.into_repr()).into_affine();

    //         assert!(cs.is_satisfied());

    //         let x_fe = result.x.get_field_value().unwrap();
    //         let y_fe = result.y.get_field_value().unwrap();

    //         let (x, y) = result.get_value().unwrap().into_xy_unchecked();

    //         assert_eq!(x_fe, x, "x coords mismatch between value and coordinates");
    //         assert_eq!(y_fe, y, "y coords mismatch between value and coordinates");

    //         let (x, y) = result_recalculated.into_xy_unchecked();

    //         assert_eq!(x_fe, x, "x coords mismatch between expected result and circuit result");
    //         assert_eq!(y_fe, y, "y coords mismatch between expected result and circuit result");

    //         assert_eq!(result.get_value().unwrap(), result_recalculated, "mismatch between expected result and circuit result");

    //         let (x, y) = a_f.into_xy_unchecked();
    //         assert_eq!(a.x.get_field_value().unwrap(), x, "x coords mismatch, input was mutated");
    //         assert_eq!(a.y.get_field_value().unwrap(), y, "y coords mismatch, input was mutated");

    //         if i == 0 {
    //             let base = cs.n();
    //             let _ = AffinePoint::multiexp(&mut cs, &[b.clone()], &[a.clone()], None).unwrap();
    //             println!("One point multiexp taken {} gates", cs.n() - base);
    //         }
    //     }
    // }

    // #[test]
    // fn test_base_curve_multiexp_2_on_random_witnesses(){
    //     use rand::{XorShiftRng, SeedableRng, Rng};
    //     let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    //     let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

    //     for i in 0..10 {
    //         let mut cs = TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();

    //         let mut a_s = vec![];
    //         let mut b_s = vec![];
    //         for _ in 0..2 {
    //             let a_f: G1Affine = rng.gen();
    //             let b_f: Fr = rng.gen();

    //             a_s.push(a_f);
    //             b_s.push(b_f);
    //         }
            
    //         let mut a_p = vec![];
    //         for a in a_s.iter() {
    //             let a = AffinePoint::alloc(
    //                 &mut cs, 
    //                 Some(*a), 
    //                 &params
    //             ).unwrap();

    //             a_p.push(a);
    //         }

    //         let mut b_n = vec![];

    //         for b in b_s.iter() {
    //             let b = AllocatedNum::alloc(
    //                 &mut cs, 
    //                 || {
    //                     Ok(*b)
    //                 }
    //             ).unwrap();

    //             let b = Num::Variable(b);
    //             b_n.push(b);
    //         }

    //         let result = AffinePoint::multiexp(&mut cs, &b_n, &a_p, None).unwrap();

    //         let mut result_recalculated = G1Affine::zero().into_projective();

    //         for (a, b) in a_s.iter().zip(b_s.iter()) {
    //             let tmp = a.mul(b.into_repr());
    //             result_recalculated.add_assign(&tmp);
    //         }

    //         let result_recalculated = result_recalculated.into_affine();

    //         assert!(cs.is_satisfied());

    //         let x_fe = result.x.get_field_value().unwrap();
    //         let y_fe = result.y.get_field_value().unwrap();

    //         let (x, y) = result.get_value().unwrap().into_xy_unchecked();

    //         assert_eq!(x_fe, x, "x coords mismatch between value and coordinates");
    //         assert_eq!(y_fe, y, "y coords mismatch between value and coordinates");

    //         let (x, y) = result_recalculated.into_xy_unchecked();

    //         assert_eq!(x_fe, x, "x coords mismatch between expected result and circuit result");
    //         assert_eq!(y_fe, y, "y coords mismatch between expected result and circuit result");

    //         assert_eq!(result.get_value().unwrap(), result_recalculated, "mismatch between expected result and circuit result");

    //         if i == 0 {
    //             let base = cs.n();
    //             let _ = AffinePoint::multiexp(&mut cs, &b_n, &a_p, None).unwrap();
    //             println!("Two points multiexp taken {} gates", cs.n() - base);
    //         }
    //     }
    // }

    // #[test]
    // fn test_base_curve_multiexp_3_on_random_witnesses(){
    //     use rand::{XorShiftRng, SeedableRng, Rng};
    //     let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    //     let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

    //     for i in 0..10 {
    //         let mut cs = TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();

    //         let mut a_s = vec![];
    //         let mut b_s = vec![];
    //         for _ in 0..3 {
    //             let a_f: G1Affine = rng.gen();
    //             let b_f: Fr = rng.gen();

    //             a_s.push(a_f);
    //             b_s.push(b_f);
    //         }
            
    //         let mut a_p = vec![];
    //         for a in a_s.iter() {
    //             let a = AffinePoint::alloc(
    //                 &mut cs, 
    //                 Some(*a), 
    //                 &params
    //             ).unwrap();

    //             a_p.push(a);
    //         }

    //         let mut b_n = vec![];

    //         for b in b_s.iter() {
    //             let b = AllocatedNum::alloc(
    //                 &mut cs, 
    //                 || {
    //                     Ok(*b)
    //                 }
    //             ).unwrap();

    //             let b = Num::Variable(b);
    //             b_n.push(b);
    //         }

    //         let result = AffinePoint::multiexp(&mut cs, &b_n, &a_p, None).unwrap();

    //         let mut result_recalculated = G1Affine::zero().into_projective();

    //         for (a, b) in a_s.iter().zip(b_s.iter()) {
    //             let tmp = a.mul(b.into_repr());
    //             result_recalculated.add_assign(&tmp);
    //         }

    //         let result_recalculated = result_recalculated.into_affine();

    //         assert!(cs.is_satisfied());

    //         let x_fe = result.x.get_field_value().unwrap();
    //         let y_fe = result.y.get_field_value().unwrap();

    //         let (x, y) = result.get_value().unwrap().into_xy_unchecked();

    //         assert_eq!(x_fe, x, "x coords mismatch between value and coordinates");
    //         assert_eq!(y_fe, y, "y coords mismatch between value and coordinates");

    //         let (x, y) = result_recalculated.into_xy_unchecked();

    //         assert_eq!(x_fe, x, "x coords mismatch between expected result and circuit result");
    //         assert_eq!(y_fe, y, "y coords mismatch between expected result and circuit result");

    //         assert_eq!(result.get_value().unwrap(), result_recalculated, "mismatch between expected result and circuit result");

    //         if i == 0 {
    //             let base = cs.n();
    //             let _ = AffinePoint::multiexp(&mut cs, &b_n, &a_p, None).unwrap();
    //             println!("Three points multiexp taken {} gates", cs.n() - base);
    //         }
    //     }
    // }

    // #[test]
    // fn test_base_curve_multiexp_4_on_random_witnesses(){
    //     use rand::{XorShiftRng, SeedableRng, Rng};
    //     let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    //     let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

    //     for i in 0..10 {
    //         let mut cs = TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();

    //         let mut a_s = vec![];
    //         let mut b_s = vec![];
    //         for _ in 0..4 {
    //             let a_f: G1Affine = rng.gen();
    //             let b_f: Fr = rng.gen();

    //             a_s.push(a_f);
    //             b_s.push(b_f);
    //         }
            
    //         let mut a_p = vec![];
    //         for a in a_s.iter() {
    //             let a = AffinePoint::alloc(
    //                 &mut cs, 
    //                 Some(*a), 
    //                 &params
    //             ).unwrap();

    //             a_p.push(a);
    //         }

    //         let mut b_n = vec![];

    //         for b in b_s.iter() {
    //             let b = AllocatedNum::alloc(
    //                 &mut cs, 
    //                 || {
    //                     Ok(*b)
    //                 }
    //             ).unwrap();

    //             let b = Num::Variable(b);
    //             b_n.push(b);
    //         }

    //         let result = AffinePoint::multiexp(&mut cs, &b_n, &a_p, None).unwrap();

    //         let mut result_recalculated = G1Affine::zero().into_projective();

    //         for (a, b) in a_s.iter().zip(b_s.iter()) {
    //             let tmp = a.mul(b.into_repr());
    //             result_recalculated.add_assign(&tmp);
    //         }

    //         let result_recalculated = result_recalculated.into_affine();

    //         assert!(cs.is_satisfied());

    //         let x_fe = result.x.get_field_value().unwrap();
    //         let y_fe = result.y.get_field_value().unwrap();

    //         let (x, y) = result.get_value().unwrap().into_xy_unchecked();

    //         assert_eq!(x_fe, x, "x coords mismatch between value and coordinates");
    //         assert_eq!(y_fe, y, "y coords mismatch between value and coordinates");

    //         let (x, y) = result_recalculated.into_xy_unchecked();

    //         assert_eq!(x_fe, x, "x coords mismatch between expected result and circuit result");
    //         assert_eq!(y_fe, y, "y coords mismatch between expected result and circuit result");

    //         assert_eq!(result.get_value().unwrap(), result_recalculated, "mismatch between expected result and circuit result");

    //         if i == 0 {
    //             let base = cs.n();
    //             let _ = AffinePoint::multiexp(&mut cs, &b_n, &a_p, None).unwrap();
    //             println!("Four points multiexp taken {} gates", cs.n() - base);
    //         }
    //     }
    // }

    // #[test]
    // fn test_base_curve_multiexp_10_on_random_witnesses(){
    //     use rand::{XorShiftRng, SeedableRng, Rng};
    //     let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    //     let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

    //     for i in 0..10 {
    //         let mut cs = TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();

    //         let mut a_s = vec![];
    //         let mut b_s = vec![];
    //         for _ in 0..10 {
    //             let a_f: G1Affine = rng.gen();
    //             let b_f: Fr = rng.gen();

    //             a_s.push(a_f);
    //             b_s.push(b_f);
    //         }
            
    //         let mut a_p = vec![];
    //         for a in a_s.iter() {
    //             let a = AffinePoint::alloc(
    //                 &mut cs, 
    //                 Some(*a), 
    //                 &params
    //             ).unwrap();

    //             a_p.push(a);
    //         }

    //         let mut b_n = vec![];

    //         for b in b_s.iter() {
    //             let b = AllocatedNum::alloc(
    //                 &mut cs, 
    //                 || {
    //                     Ok(*b)
    //                 }
    //             ).unwrap();

    //             let b = Num::Variable(b);
    //             b_n.push(b);
    //         }

    //         let result = AffinePoint::multiexp(&mut cs, &b_n, &a_p, None).unwrap();

    //         let mut result_recalculated = G1Affine::zero().into_projective();

    //         for (a, b) in a_s.iter().zip(b_s.iter()) {
    //             let tmp = a.mul(b.into_repr());
    //             result_recalculated.add_assign(&tmp);
    //         }

    //         let result_recalculated = result_recalculated.into_affine();

    //         assert!(cs.is_satisfied());

    //         let x_fe = result.x.get_field_value().unwrap();
    //         let y_fe = result.y.get_field_value().unwrap();

    //         let (x, y) = result.get_value().unwrap().into_xy_unchecked();

    //         assert_eq!(x_fe, x, "x coords mismatch between value and coordinates");
    //         assert_eq!(y_fe, y, "y coords mismatch between value and coordinates");

    //         let (x, y) = result_recalculated.into_xy_unchecked();

    //         assert_eq!(x_fe, x, "x coords mismatch between expected result and circuit result");
    //         assert_eq!(y_fe, y, "y coords mismatch between expected result and circuit result");

    //         assert_eq!(result.get_value().unwrap(), result_recalculated, "mismatch between expected result and circuit result");

    //         if i == 0 {
    //             let base = cs.n();
    //             use std::sync::atomic::Ordering;
    //             let k = super::super::super::bigint::RANGE_GATES_COUNTER.load(Ordering::SeqCst);
    //             let _ = AffinePoint::multiexp(&mut cs, &b_n, &a_p, None).unwrap();
    //             let k = super::super::super::bigint::RANGE_GATES_COUNTER.load(Ordering::SeqCst) - k;
    //             println!("10 points multiexp taken {} gates", cs.n() - base);
    //             println!("Range checks take {} gates", k);
    //         }
    //     }
    // }

    // #[test]
    // fn test_base_curve_multiexp_10_bls_12_on_random_witnesses() {
    //     use rand::{XorShiftRng, SeedableRng, Rng};
    //     let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    //     use crate::bellman::pairing::bls12_381::{Bls12, Fr, Fq, G1Affine, G1};

    //     use super::super::super::bigint::get_range_constraint_info;

    //     let params = RnsParameters::<Bls12, Fq>::new_for_field(68, 110, 8);

    //     for i in 0..10 {
    //         let mut cs = TrivialAssembly::<Bls12, Width4WithCustomGates, Width4MainGateWithDNext>::new();

    //         // let strats = get_range_constraint_info(&cs);

    //         // let mut params = RnsParameters::<Bls12, Fq>::new_for_field_with_strategy(
    //         //     96, 
    //         //     110, 
    //         //     6, 
    //         //     strats[0],
    //         //     true
    //         // );

    //         // params.set_prefer_double_limb_carry_propagation(false);

    //         let mut a_s = vec![];
    //         let mut b_s = vec![];
    //         for _ in 0..10 {
    //             let a_f: G1 = rng.gen();
    //             let a_f = a_f.into_affine();
    //             let b_f: Fr = rng.gen();

    //             a_s.push(a_f);
    //             b_s.push(b_f);
    //         }
            
    //         let mut a_p = vec![];
    //         for a in a_s.iter() {
    //             let a = AffinePoint::alloc(
    //                 &mut cs, 
    //                 Some(*a), 
    //                 &params
    //             ).unwrap();

    //             a_p.push(a);
    //         }

    //         let mut b_n = vec![];

    //         for b in b_s.iter() {
    //             let b = AllocatedNum::alloc(
    //                 &mut cs, 
    //                 || {
    //                     Ok(*b)
    //                 }
    //             ).unwrap();

    //             let b = Num::Variable(b);
    //             b_n.push(b);
    //         }

    //         let result = AffinePoint::multiexp(&mut cs, &b_n, &a_p, None).unwrap();

    //         let mut result_recalculated = G1Affine::zero().into_projective();

    //         for (a, b) in a_s.iter().zip(b_s.iter()) {
    //             let tmp = a.mul(b.into_repr());
    //             result_recalculated.add_assign(&tmp);
    //         }

    //         let result_recalculated = result_recalculated.into_affine();

    //         assert!(cs.is_satisfied());

    //         let x_fe = result.x.get_field_value().unwrap();
    //         let y_fe = result.y.get_field_value().unwrap();

    //         let (x, y) = result.get_value().unwrap().into_xy_unchecked();

    //         assert_eq!(x_fe, x, "x coords mismatch");
    //         assert_eq!(y_fe, y, "y coords mismatch");

    //         let (x, y) = result_recalculated.into_xy_unchecked();

    //         assert_eq!(x_fe, x, "x coords mismatch");
    //         assert_eq!(y_fe, y, "y coords mismatch");

    //         if i == 0 {
    //             let base = cs.n();
    //             use std::sync::atomic::Ordering;
    //             let k = super::super::super::bigint::RANGE_GATES_COUNTER.load(Ordering::SeqCst);
    //             let _ = AffinePoint::multiexp(&mut cs, &b_n, &a_p, None).unwrap();
    //             let k = super::super::super::bigint::RANGE_GATES_COUNTER.load(Ordering::SeqCst) - k;
    //             println!("10 points multiexp taken {} gates", cs.n() - base);
    //             println!("Range checks take {} gates", k);
    //         }
    //     }
    // }

    // #[test]
    // fn test_base_curve_multiexp_10_bls_12_using_tables_on_random_witnesses() {
    //     use crate::bellman::plonk::better_better_cs::cs::*;
    //     use super::super::super::bigint::get_range_constraint_info;
    //     use rand::{XorShiftRng, SeedableRng, Rng};
    //     let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    //     use crate::bellman::pairing::bls12_381::{Bls12, Fr, Fq, G1Affine, G1};

    //     let mut cs = TrivialAssembly::<Bls12, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

    //     let over = vec![PolyIdentifier::VariablesPolynomial(0), PolyIdentifier::VariablesPolynomial(1), PolyIdentifier::VariablesPolynomial(2)];
    //     let table = MultiTableApplication::<Bls12>::new_range_table_of_width_3(16, over).unwrap();

    //     cs.add_multitable(table).unwrap();

    //     let strats = get_range_constraint_info(&cs);

    //     let mut params = RnsParameters::<Bls12, Fq>::new_for_field_with_strategy(
    //         96, 
    //         110, 
    //         6, 
    //         strats[0],
    //         true
    //     );

    //     params.set_prefer_double_limb_carry_propagation(false);

    //     let mut a_s = vec![];
    //     let mut b_s = vec![];
    //     for _ in 0..10 {
    //         let a_f: G1 = rng.gen();
    //         let a_f = a_f.into_affine();
    //         let b_f: Fr = rng.gen();

    //         a_s.push(a_f);
    //         b_s.push(b_f);
    //     }
        
    //     let mut a_p = vec![];
    //     for a in a_s.iter() {
    //         let a = AffinePoint::alloc(
    //             &mut cs, 
    //             Some(*a), 
    //             &params
    //         ).unwrap();

    //         a_p.push(a);
    //     }

    //     let mut b_n = vec![];

    //     for b in b_s.iter() {
    //         let b = AllocatedNum::alloc(
    //             &mut cs, 
    //             || {
    //                 Ok(*b)
    //             }
    //         ).unwrap();

    //         let b = Num::Variable(b);
    //         b_n.push(b);
    //     }

    //     let base = cs.n();

    //     let result = AffinePoint::multiexp(&mut cs, &b_n, &a_p, None).unwrap();

    //     println!("10 points multiexp with 16 bit range tables taken {} gates", cs.n() - base);

    //     let mut result_recalculated = G1Affine::zero().into_projective();

    //     for (a, b) in a_s.iter().zip(b_s.iter()) {
    //         let tmp = a.mul(b.into_repr());
    //         result_recalculated.add_assign(&tmp);
    //     }

    //     let result_recalculated = result_recalculated.into_affine();

    //     assert!(cs.is_satisfied());
    // }
}