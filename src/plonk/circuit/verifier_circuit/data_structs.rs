use crate::plonk::circuit::curve::sw_affine::*;
use crate::plonk::circuit::bigint::field::*;
use crate::plonk::circuit::bigint::bigint::*;
use crate::plonk::circuit::allocated_num::*;
use crate::plonk::circuit::boolean::*;
use super::affine_point_wrapper::WrappedAffinePoint;
use super::affine_point_wrapper::aux_data::AuxData;

use crate::bellman::pairing::{
    Engine,
    CurveAffine,
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

use crate::bellman::plonk::better_cs::keys::{Proof, VerificationKey};
use crate::bellman::plonk::better_cs::cs::PlonkConstraintSystemParams as OldCSParams;


#[derive(Clone, Debug)]
pub struct ProofGadget<'a, E: Engine, WP: WrappedAffinePoint<'a, E>> {
    pub num_inputs: usize,
    pub input_values: Vec<AllocatedNum<E>>,
    pub wire_commitments: Vec<WP>,
    pub grand_product_commitment: WP,
    pub quotient_poly_commitments: Vec<WP>,

    pub wire_values_at_z: Vec<AllocatedNum<E>>,
    pub wire_values_at_z_omega: Vec<AllocatedNum<E>>,
    pub grand_product_at_z_omega: AllocatedNum<E>,
    pub quotient_polynomial_at_z: AllocatedNum<E>,
    pub linearization_polynomial_at_z: AllocatedNum<E>,
    pub permutation_polynomials_at_z: Vec<AllocatedNum<E>>,

    pub opening_at_z_proof: WP,
    pub opening_at_z_omega_proof: WP,

    _m: &'a std::marker::PhantomData<()>,
}


impl<'a, E: Engine, WP: WrappedAffinePoint<'a, E>> ProofGadget<'a, E, WP> {
    
    pub fn alloc<CS: ConstraintSystem<E>, P: OldCSParams<E>, AD: AuxData<E>>(
        cs: &mut CS,
        proof: Proof<E, P>,
        params: &'a RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
        aux_data: &AD,
    ) -> Result<Self, SynthesisError> {
        
        let input_values = proof.input_values.iter().map(|x| {
            AllocatedNum::alloc_input(cs, || Ok(*x))
        }).collect::<Result<Vec<_>, _>>()?;

        let wire_commitments = proof.wire_commitments.iter().map(|x| {
            WrappedAffinePoint::alloc(cs, Some(*x), params, aux_data)
        }).collect::<Result<Vec<_>, _>>()?;

        let grand_product_commitment = WrappedAffinePoint::alloc(cs, Some(proof.grand_product_commitment), params, aux_data)?;
        
        let quotient_poly_commitments = proof.quotient_poly_commitments.iter().map(|x| {
            WrappedAffinePoint::alloc(cs, Some(*x), params, aux_data)
        }).collect::<Result<Vec<_>, _>>()?;

        let wire_values_at_z = proof.wire_values_at_z.iter().map(|x| {
            AllocatedNum::alloc(cs, || Ok(*x))
        }).collect::<Result<Vec<_>, _>>()?;

        let wire_values_at_z_omega = proof.wire_values_at_z_omega.iter().map(|x| {
            AllocatedNum::alloc(cs, || Ok(*x))
        }).collect::<Result<Vec<_>, _>>()?;

        let grand_product_at_z_omega = AllocatedNum::alloc(cs, || Ok(proof.grand_product_at_z_omega))?; 
        let quotient_polynomial_at_z = AllocatedNum::alloc(cs, || Ok(proof.quotient_polynomial_at_z))?; 
        let linearization_polynomial_at_z = AllocatedNum::alloc(cs, || Ok(proof.linearization_polynomial_at_z))?;  

        let permutation_polynomials_at_z = proof.permutation_polynomials_at_z.iter().map(|x| {
            AllocatedNum::alloc(cs, || Ok(*x))
        }).collect::<Result<Vec<_>, _>>()?;

        let opening_at_z_proof = WrappedAffinePoint::alloc(cs, Some(proof.opening_at_z_proof), params, aux_data)?;
        let opening_at_z_omega_proof = WrappedAffinePoint::alloc(cs, Some(proof.opening_at_z_omega_proof), params, aux_data)?;
       
        Ok(ProofGadget {
            num_inputs: proof.num_inputs,
            input_values,
            wire_commitments,
            grand_product_commitment,
            quotient_poly_commitments,

            wire_values_at_z,
            wire_values_at_z_omega,
            grand_product_at_z_omega,
            quotient_polynomial_at_z,
            linearization_polynomial_at_z,
            permutation_polynomials_at_z,

            opening_at_z_proof,
            opening_at_z_omega_proof,

            _m: &std::marker::PhantomData::<()>,
        })
    }

    pub fn alloc_from_witness<CS: ConstraintSystem<E>, P: OldCSParams<E>, AD: AuxData<E>>(
        cs: &mut CS,
        num_inputs: usize,
        proof: &Option<Proof<E, P>>,
        params: &'a RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
        aux_data: &AD,
    ) -> Result<Self, SynthesisError> {

        use crate::circuit::Assignment;

        let state_width = P::STATE_WIDTH;
        let num_quotient_commitments = P::STATE_WIDTH;

        assert!(P::CAN_ACCESS_NEXT_TRACE_STEP);
        assert!(!P::HAS_CUSTOM_GATES);

        let mut input_values = vec![];
        for idx in 0..num_inputs {
            let wit = proof.as_ref().and_then(|el| Some(&el.input_values)).and_then(|el| Some(el[idx]));
            let allocated = AllocatedNum::alloc(cs, || Ok(*wit.get()?))?;

            input_values.push(allocated);
        }

        let mut wire_commitments = vec![];
        for idx in 0..state_width {
            let wit = proof.as_ref().and_then(|el| Some(&el.wire_commitments)).and_then(|el| Some(el[idx]));
            let allocated = WrappedAffinePoint::alloc(cs, wit, params, aux_data)?;

            wire_commitments.push(allocated);
        }
        
        let wit = proof.as_ref().and_then(|el| Some(el.grand_product_commitment));
        let grand_product_commitment = WrappedAffinePoint::alloc(cs, wit, params, aux_data)?;

        let mut quotient_poly_commitments = vec![];
        for idx in 0..state_width {
            let wit = proof.as_ref().and_then(|el| Some(&el.quotient_poly_commitments)).and_then(|el| Some(el[idx]));
            let allocated = WrappedAffinePoint::alloc(cs, wit, params, aux_data)?;

            quotient_poly_commitments.push(allocated);
        }

        let mut wire_values_at_z = vec![];
        for idx in 0..state_width {
            let wit = proof.as_ref().and_then(|el| Some(&el.wire_values_at_z)).and_then(|el| Some(el[idx]));
            let allocated = AllocatedNum::alloc(cs, || Ok(*wit.get()?))?;

            wire_values_at_z.push(allocated);
        }

        let mut wire_values_at_z_omega = vec![];
        for idx in 0..state_width {
            let wit = proof.as_ref().and_then(|el| Some(&el.wire_values_at_z_omega)).and_then(|el| Some(el[idx]));
            let allocated = AllocatedNum::alloc(cs, || Ok(*wit.get()?))?;

            wire_values_at_z_omega.push(allocated);
        }

        let wit = proof.as_ref().and_then(|el| Some(el.grand_product_at_z_omega));
        let grand_product_at_z_omega = AllocatedNum::alloc(cs, || Ok(*wit.get()?))?; 

        let wit = proof.as_ref().and_then(|el| Some(el.quotient_polynomial_at_z));
        let quotient_polynomial_at_z = AllocatedNum::alloc(cs, || Ok(*wit.get()?))?; 

        let wit = proof.as_ref().and_then(|el| Some(el.linearization_polynomial_at_z));
        let linearization_polynomial_at_z = AllocatedNum::alloc(cs, || Ok(*wit.get()?))?; 

        let mut permutation_polynomials_at_z = vec![];
        for idx in 0..(state_width-1) {
            let wit = proof.as_ref().and_then(|el| Some(&el.permutation_polynomials_at_z)).and_then(|el| Some(el[idx]));
            let allocated = AllocatedNum::alloc(cs, || Ok(*wit.get()?))?;

            permutation_polynomials_at_z.push(allocated);
        }

        let wit = proof.as_ref().and_then(|el| Some(el.opening_at_z_proof));
        let opening_at_z_proof = WrappedAffinePoint::alloc(cs, wit, params, aux_data)?;

        let wit = proof.as_ref().and_then(|el| Some(el.opening_at_z_omega_proof));
        let opening_at_z_omega_proof = WrappedAffinePoint::alloc(cs, wit, params, aux_data)?;

        Ok(ProofGadget {
            num_inputs: num_inputs,
            input_values,
            wire_commitments,
            grand_product_commitment,
            quotient_poly_commitments,

            wire_values_at_z,
            wire_values_at_z_omega,
            grand_product_at_z_omega,
            quotient_polynomial_at_z,
            linearization_polynomial_at_z,
            permutation_polynomials_at_z,

            opening_at_z_proof,
            opening_at_z_omega_proof,

            _m: &std::marker::PhantomData::<()>,
        })
    }
}


#[derive(Clone, Debug)]
pub struct VerificationKeyGagdet<'a, E: Engine, WP: WrappedAffinePoint<'a, E>> {
    pub n: Option<usize>,
    pub domain_size_as_allocated_num: Option<AllocatedNum<E>>,
    pub omega_as_allocated_num: Option<AllocatedNum<E>>,
    pub num_inputs: usize,
    pub selector_commitments: Vec<WP>,
    pub next_step_selector_commitments: Vec<WP>,
    pub permutation_commitments: Vec<WP>,
    pub non_residues: Vec<E::Fr>,

    _m: &'a std::marker::PhantomData<()>,
}


impl<'a, E: Engine, WP: WrappedAffinePoint<'a, E>> VerificationKeyGagdet<'a, E, WP> {
    
    pub fn alloc<CS: ConstraintSystem<E>, P: OldCSParams<E>, AD: AuxData<E>>(
        cs: &mut CS,
        vk:  VerificationKey<E, P>,
        params: &'a RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
        aux_data: &AD,
    ) -> Result<Self, SynthesisError> {

        let selector_commitments = vk.selector_commitments.iter().map(|x| {
            WrappedAffinePoint::alloc(cs, Some(*x), params, aux_data)
        }).collect::<Result<Vec<_>, _>>()?;

        let next_step_selector_commitments = vk.next_step_selector_commitments.iter().map(|x| {
            WrappedAffinePoint::alloc(cs, Some(*x), params, aux_data)
        }).collect::<Result<Vec<_>, _>>()?;

        let permutation_commitments = vk.permutation_commitments.iter().map(|x| {
            WrappedAffinePoint::alloc(cs, Some(*x), params, aux_data)
        }).collect::<Result<Vec<_>, _>>()?;

        Ok(VerificationKeyGagdet {
            n : Some(vk.n),
            domain_size_as_allocated_num: None,
            omega_as_allocated_num: None,
            num_inputs : vk.num_inputs,
            selector_commitments,
            next_step_selector_commitments,
            permutation_commitments,
            non_residues: vk.non_residues,

            _m: &std::marker::PhantomData::<()>,
        })
    }

    pub fn alloc_from_limbs_witness<CS: ConstraintSystem<E>, P: OldCSParams<E>, AD: AuxData<E>>(
        cs: &mut CS,
        num_inputs: usize,
        domain_size: &AllocatedNum<E>,
        omega: &AllocatedNum<E>,
        witness: &[AllocatedNum<E>],
        params: &'a RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
        non_residues: Vec<E::Fr>,
        aux_data: &AD,
    ) -> Result<Self, SynthesisError> {

        let num_selector_commitments = P::STATE_WIDTH + 2; 
        let num_next_step_selector_commitments = if P::CAN_ACCESS_NEXT_TRACE_STEP {
            1
        } else {
            0
        };

        let num_permutation_commitments = P::STATE_WIDTH;

        assert!(!P::HAS_CUSTOM_GATES);

        let mut w = witness;

        let mut selector_commitments = vec![];
        for _ in 0..num_selector_commitments {
            let (point, rest) = WrappedAffinePoint::from_allocated_limb_witness(cs, w, params, aux_data)?;

            w = rest;

            selector_commitments.push(point);
        }

        let mut next_step_selector_commitments = vec![];
        for _ in 0..num_next_step_selector_commitments {
            let (point, rest) = WrappedAffinePoint::from_allocated_limb_witness(cs, w, params, aux_data)?;

            w = rest;

            next_step_selector_commitments.push(point);
        }

        let mut permutation_commitments = vec![];
        for _ in 0..num_permutation_commitments {
            let (point, rest) = WrappedAffinePoint::from_allocated_limb_witness(cs, w, params, aux_data)?;

            w = rest;

            permutation_commitments.push(point);
        }

        assert_eq!(w.len(), 0);

        Ok(VerificationKeyGagdet {
            n : None,
            domain_size_as_allocated_num: Some(domain_size.clone()),
            omega_as_allocated_num: Some(omega.clone()),
            num_inputs : num_inputs,
            selector_commitments,
            next_step_selector_commitments,
            permutation_commitments,
            non_residues: non_residues,

            _m: &std::marker::PhantomData::<()>,
        })
    }
}