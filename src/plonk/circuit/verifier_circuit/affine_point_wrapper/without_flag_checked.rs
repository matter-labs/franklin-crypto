use super::*;

#[derive(Clone, Debug)]
pub struct WrapperChecked<'a, E: Engine> {
    pub point: AffinePoint<'a, E, E::G1Affine>,
}

impl<'a, E: Engine> WrappedAffinePoint<'a, E> for WrapperChecked<'a, E> {

    fn get_point(&self) -> &AffinePoint<E, E::G1Affine> {
        &self.point
    }

    fn get_zero_flag(&self) -> Boolean {
        Boolean::constant(false)
    }
   
    fn alloc<CS: ConstraintSystem<E>, AD: aux_data::AuxData<E>>(
        cs: &mut CS,
        value: Option<E::G1Affine>,
        params: &'a RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>,
        aux_data: &AD,
    ) -> Result<Self, SynthesisError> 
    {
        let point = AffinePoint::alloc(cs, value, params)?;
        let res = WrapperChecked {
            point,
        };

        let is_on_curve = res.is_on_curve(cs, params, aux_data)?;

        let subgroup_check = if aux_data.requires_subgroup_check() {
            res.subgroup_check(cs, params, aux_data)?
        }
        else {
            Boolean::constant(true)
        };
        
        let is_valid_point = Boolean::and(cs, &is_on_curve, &subgroup_check)?;
        Boolean::enforce_equal(cs, &is_valid_point, &Boolean::constant(true))?;

        Ok(res)
    }

    fn alloc_unchecked<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        value: Option<E::G1Affine>,
        params: &'a RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>,
    ) -> Result<Self, SynthesisError> 
    {
        let res = WrapperChecked { 
            point: AffinePoint::alloc(cs, value, params)? 
        };
        Ok(res)
    }

    fn zero(_params: &'a RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>) -> Self 
    {
        unimplemented!();
    }
    
    fn constant(
        value: E::G1Affine,
        params: &'a RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>
    ) -> Self
    {
        let res = WrapperChecked { 
            point: AffinePoint::constant(value, params),
        };
        res
    }

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

    fn add<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        other: &mut Self,
        _params: &'a RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>,
    ) -> Result<Self, SynthesisError>
    {
        let (check, _) = FieldElement::equals(cs, self.point.x.clone(), other.point.x.clone())?;
        Boolean::enforce_equal(cs, &check, &Boolean::constant(false))?;
        
        let res = WrapperChecked { 
            point: self.point.clone().add_unequal(cs, other.point.clone())?.0,
        };
        Ok(res)
    } 

    fn sub<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        other: &mut Self,
        _params: &'a RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>,
    ) -> Result<Self, SynthesisError>
    {
        let (check, _) = FieldElement::equals(cs, self.point.x.clone(), other.point.x.clone())?;
        Boolean::enforce_equal(cs, &check, &Boolean::constant(false))?;
        
        let res = WrapperChecked { 
            point: self.point.clone().sub_unequal(cs, other.point.clone())?.0,
        };
        Ok(res)
    }

    fn double<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        _params: &'a RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>,
    ) -> Result<Self, SynthesisError>
    {
        let res = WrapperChecked { 
            point: self.point.clone().double(cs)?.0,
        };
        Ok(res)
    }

    fn negate<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        _params: &'a RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>,
    ) -> Result<Self, SynthesisError>
    {
        let (negated, _) = self.point.clone().negate(cs)?;
        let res = WrapperChecked { 
            point: negated,
        };
        Ok(res)
    }

    fn select<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        flag: &Boolean,
        first: Self,
        second: Self
    ) -> Result<Self, SynthesisError>
    {
        let (selected, _) = AffinePoint::select(cs, flag, first.point, second.point)?;

        let res = WrapperChecked { 
            point: selected
        };

        Ok(res)
    }
    
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

        let (check, _) = FieldElement::equals(cs, lhs, rhs)?;
   
        Ok(check)
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
        let res = WrapperChecked { 
            point: self.point.clone().mul(cs, &d, bit_limit)?.0,
        };
        Ok(res)
    }

    // TODO: mul and multiexp should be modified

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
        let res = WrapperChecked { 
            point: AffinePoint::multiexp(cs, &d_arr[..], &aff_points[..], bit_limit)?,
        };
        Ok(res)
    }
}