use super::*;

#[derive(Clone, Debug)]
pub struct WrapperUnchecked<'a, E: Engine> {
    pub point: AffinePoint<'a, E, E::G1Affine>,
}

impl<'a, E: Engine> WrappedAffinePoint<'a, E> for WrapperUnchecked<'a, E> {
    fn get_point(&self) -> &AffinePoint<E, E::G1Affine> {
        &self.point
    }

    fn get_zero_flag(&self) -> Boolean {
        Boolean::constant(false)
    }
   
    #[track_caller]
    fn alloc<CS: ConstraintSystem<E>, AD: aux_data::AuxData<E>>(
        cs: &mut CS,
        value: Option<E::G1Affine>,
        params: &'a RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>,
        aux_data: &AD,
    ) -> Result<Self, SynthesisError> 
    {
        let point = AffinePoint::alloc(cs, value, params)?;

        let res = WrapperUnchecked {
            point,
        };

        let is_on_curve = res.is_on_curve(cs, params, aux_data)?;

        let subgroup_check = if aux_data.requires_subgroup_check() {
            res.subgroup_check(cs, params, aux_data)?
        } else {
            Boolean::constant(true)
        };
        
        let is_valid_point = Boolean::and(cs, &is_on_curve, &subgroup_check)?;
        Boolean::enforce_equal(cs, &is_valid_point, &Boolean::constant(true))?;

        Ok(res)
    }

    #[track_caller]
    fn alloc_unchecked<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        value: Option<E::G1Affine>,
        params: &'a RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>,
    ) -> Result<Self, SynthesisError> 
    {
        let res = WrapperUnchecked { 
            point: AffinePoint::alloc(cs, value, params)? 
        };
        Ok(res)
    }

    #[track_caller]
    fn from_allocated_limb_witness<'b, CS: ConstraintSystem<E>, AD: aux_data::AuxData<E>>(
        cs: &mut CS,
        witnesses: &'b [AllocatedNum<E>],
        params: &'a RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>,
        aux_data: &AD,
    ) -> Result<(Self, &'b [AllocatedNum<E>]), SynthesisError> {
        let (x, rest) = allocate_coordinate_from_limb_witness(cs, witnesses, params)?;
        let (y, rest) = allocate_coordinate_from_limb_witness(cs, rest, params)?;

        let value = match (x.get_field_value(), y.get_field_value()) {
            (Some(x_val), Some(y_val)) => {
                let point = E::G1Affine::from_xy_unchecked(x_val, y_val);

                Some(point)
            },
            _ => {
                None
            }
        };
        let p = AffinePoint {
            value,
            x,
            y
        };

        let res = WrapperUnchecked { 
            point: p
        };

        let is_on_curve = res.is_on_curve(cs, params, aux_data)?;

        let subgroup_check = if aux_data.requires_subgroup_check() {
            res.subgroup_check(cs, params, aux_data)?
        } else {
            Boolean::constant(true)
        };
        
        let is_valid_point = Boolean::and(cs, &is_on_curve, &subgroup_check)?;
        Boolean::enforce_equal(cs, &is_valid_point, &Boolean::constant(true))?;

        Ok((res, rest))
    }

    fn zero(_params: &'a RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>) -> Self 
    {
        unimplemented!();
    }
    
    #[track_caller]
    fn constant(
        value: E::G1Affine,
        params: &'a RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>
    ) -> Self
    {
        let res = WrapperUnchecked { 
            point: AffinePoint::constant(value, params),
        };
        res
    }

    #[track_caller]
    fn equals<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        other: &Self,
        _params: &'a RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>,
    ) -> Result<Boolean, SynthesisError>
    {
        let (eq, _) = AffinePoint::equals(cs, self.point.clone(), other.point.clone())?;
        
        Ok(eq)
    }

    #[track_caller]
    fn add<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        other: &mut Self,
        _params: &'a RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>,
    ) -> Result<Self, SynthesisError>
    {
        let res = WrapperUnchecked { 
            point: self.point.clone().add_unequal(cs, other.point.clone())?.0,
        };
        Ok(res)
    } 

    #[track_caller]
    fn sub<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        other: &mut Self,
        _params: &'a RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>,
    ) -> Result<Self, SynthesisError>
    {
        let res = WrapperUnchecked { 
            point: self.point.clone().sub_unequal(cs, other.point.clone())?.0,
        };
        Ok(res)
    }

    #[track_caller]
    fn double<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        _params: &'a RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>,
    ) -> Result<Self, SynthesisError>
    {
        let res = WrapperUnchecked { 
            point: self.point.clone().double(cs)?.0,
        };
        Ok(res)
    }

    #[track_caller]
    fn negate<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        _params: &'a RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>,
    ) -> Result<Self, SynthesisError>
    {
        let (negated, _) = self.point.clone().negate(cs)?;
        let res = WrapperUnchecked { 
            point: negated,
        };
        Ok(res)
    }

    #[track_caller]
    fn select<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        flag: &Boolean,
        first: Self,
        second: Self
    ) -> Result<Self, SynthesisError>
    {
        let (selected, _) = AffinePoint::select(cs, flag, first.point, second.point)?;

        let res = WrapperUnchecked { 
            point: selected
        };

        Ok(res)
    }
    
    #[track_caller]
    fn is_on_curve<CS: ConstraintSystem<E>, AD: aux_data::AuxData<E>>(
        &self,
        cs: &mut CS,
        params: &RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>,
        aux_data: &AD,
    ) -> Result<Boolean, SynthesisError>
    {
        let lhs = self.point.y.clone().square(cs)?.0;
        
        let (mut rhs, reduced_x) = self.point.x.clone().square(cs)?;
        
        rhs = rhs.mul(cs, reduced_x)?.0;
        
        let b = FieldElement::new_constant(aux_data.get_b(), params);
        rhs = rhs.add(cs, b)?.0;

        let (on_curve, _) = FieldElement::equals(cs, lhs, rhs)?;

        Ok(on_curve)
    }

    fn subgroup_check<CS: ConstraintSystem<E>, AD: aux_data::AuxData<E>>(
        &self,
        _cs: &mut CS,
        _params: &RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>,
        _aux_data: &AD,
    ) -> Result<Boolean, SynthesisError>
    {
        // we check that (n-1)x = -x
        //let mut exp = aux_data.get_group_order().clone();
        //exp[0] -= 1;

        // TODO: we need multiplication by a constant
        //let lhs = self.mul(cs, scalar, None, params, aux_data)?;
        //let rhs = self.negate(cs)?;

        //lhs.equals(rhs)
        Ok(Boolean::constant(true))
    }

    #[track_caller]
    fn mul<CS: ConstraintSystem<E>, AD: aux_data::AuxData<E>>(
        &mut self,
        cs: &mut CS,
        scalar: &AllocatedNum::<E>,
        bit_limit: Option<usize>,
        _params: &'a RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>,
        _aux_data: &AD,
    ) -> Result<Self, SynthesisError>
    {
        let d = Num::Variable(scalar.clone());
        let res = WrapperUnchecked { 
            point: self.point.clone().mul(cs, &d, bit_limit)?.0,
        };
        Ok(res)
    }

    #[track_caller]
    fn multiexp<CS: ConstraintSystem<E>, AD: aux_data::AuxData<E>>(
        cs: &mut CS,
        scalars: &[AllocatedNum::<E>],
        points: &[Self],
        bit_limit: Option<usize>,
        _params: &'a RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>,
        _aux_data: &AD,
    ) -> Result<Self, SynthesisError>
    {
        let d_arr : Vec<Num<E>> = scalars.iter().map(|x| Num::Variable(x.clone())).collect();
        let aff_points : Vec<_> = points.into_iter().map(|x| x.point.clone()).collect();
        let res = WrapperUnchecked { 
            point: AffinePoint::multiexp(cs, &d_arr[..], &aff_points[..], bit_limit)?,
        };
        Ok(res)
    }
}

fn allocate_coordinate_from_limb_witness<'a, 'b, E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    witness: &'b [AllocatedNum<E>],
    params: &'a RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>,
) -> Result<(FieldElement<'a, E, <E::G1Affine as GenericCurveAffine>::Base>, &'b [AllocatedNum<E>]), SynthesisError> {
    if params.can_allocate_from_double_limb_witness() {
        let mut num_witness = params.num_limbs_for_in_field_representation / 2;
        if params.num_limbs_for_in_field_representation % 2 != 0 {
            num_witness += 1;
        }

        let (w, rest) = witness.split_at(num_witness);
        let w: Vec<_> = w.iter().map(|el| Num::Variable(el.clone())).collect();
        let fe = FieldElement::from_double_size_limb_witnesses(cs, &w, false, params)?;

        return Ok((fe, rest));
    } else {
        let num_witness = params.num_limbs_for_in_field_representation;

        let (w, rest) = witness.split_at(num_witness);
        let w: Vec<_> = w.iter().map(|el| Num::Variable(el.clone())).collect();
        let fe = FieldElement::coarsely_allocate_from_single_limb_witnesses(cs, &w, false, params)?;

        return Ok((fe, rest));
    }
}