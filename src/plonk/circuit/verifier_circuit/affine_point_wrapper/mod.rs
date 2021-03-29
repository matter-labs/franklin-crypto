pub mod aux_data;

use crate::bellman::pairing::{
    Engine,
    GenericCurveAffine,
    CurveProjective,
};

use crate::bellman::pairing::ff::{
    Field,
    PrimeField,
    BitIterator,
};

use crate::bellman::{
    SynthesisError,
};

use crate::bellman::plonk::better_better_cs::cs::{
    Variable, 
    ConstraintSystem,
    PlonkConstraintSystemParams,
};

use crate::plonk::circuit::curve::sw_affine::*;
use crate::plonk::circuit::bigint::field::*;
use crate::plonk::circuit::allocated_num::*;
use crate::plonk::circuit::boolean::*;

pub trait WrappedAffinePoint<'a, E: Engine>: Sized + Clone + std::fmt::Debug {

    fn get_point(&self) -> &AffinePoint<E, E::G1Affine>;
    fn get_zero_flag(&self) -> Boolean;
   
    fn alloc<CS: ConstraintSystem<E>, AD: aux_data::AuxData<E>>(
        cs: &mut CS,
        value: Option<E::G1Affine>,
        params: &'a RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>,
        aux_data: &AD,
    ) -> Result<Self, SynthesisError>;

    fn alloc_unchecked<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        value: Option<E::G1Affine>,
        params: &'a RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>,
    ) -> Result<Self, SynthesisError>; 

    fn from_allocated_limb_witness<'b, CS: ConstraintSystem<E>, AD: aux_data::AuxData<E>>(
        _cs: &mut CS,
        _witnesses: &'b [AllocatedNum<E>],
        _params: &'a RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>,
        _aux_data: &AD,
    ) -> Result<(Self, &'b [AllocatedNum<E>]), SynthesisError> {
        unimplemented!("not implemented by default");
    }

    fn zero(params: &'a RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>) -> Self;
    
    fn constant(
        value: E::G1Affine,
        params: &'a RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>
    ) -> Self;

    fn equals<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        other: &Self,
        _params: &'a RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>,
    ) -> Result<Boolean, SynthesisError>; 

    fn add<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        other: &mut Self,
        params: &'a RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>,
    ) -> Result<Self, SynthesisError>; 

    fn sub<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        other: &mut Self,
        params: &'a RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>,
    ) -> Result<Self, SynthesisError>;

    fn double<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        _params: &'a RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>,
    ) -> Result<Self, SynthesisError>; 

    fn negate<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        _params: &'a RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>,
    ) -> Result<Self, SynthesisError>; 

    fn select<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        flag: &Boolean,
        first: Self,
        second: Self
    ) -> Result<Self, SynthesisError>;
    
    fn is_on_curve<CS: ConstraintSystem<E>, AD: aux_data::AuxData<E>>(
        &self,
        cs: &mut CS,
        params: &RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>,
        aux_data: &AD,
    ) -> Result<Boolean, SynthesisError>; 

    fn subgroup_check<CS: ConstraintSystem<E>, AD: aux_data::AuxData<E>>(
        &self,
        cs: &mut CS,
        params: &RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>,
        aux_data: &AD,
    ) -> Result<Boolean, SynthesisError>; 

    fn mul<CS: ConstraintSystem<E>, AD: aux_data::AuxData<E>>(
        &mut self,
        cs: &mut CS,
        scalar: &AllocatedNum::<E>,
        bit_limit: Option<usize>,
        params: &'a RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>,
        aux_data: &AD,
    ) -> Result<Self, SynthesisError>;

    fn multiexp<CS: ConstraintSystem<E>, AD: aux_data::AuxData<E>>(
        cs: &mut CS,
        scalars: &[AllocatedNum::<E>],
        points: &[Self],
        bit_limit: Option<usize>,
        params: &'a RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>,
        aux_data: &AD,
    ) -> Result<Self, SynthesisError>;
}


// pub mod with_zero_flag;
pub mod without_flag_unchecked;
pub mod without_flag_checked;