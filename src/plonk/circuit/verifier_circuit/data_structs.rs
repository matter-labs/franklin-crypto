use crate::plonk::circuit::curve::sw_affine::*;
use crate::plonk::circuit::bigint::field::*;
use crate::plonk::circuit::bigint::bigint::*;
use crate::plonk::circuit::allocated_num::*;
use crate::plonk::circuit::boolean::*;
use super::affine_point_wrapper::WrappedAffinePoint;
use super::affine_point_wrapper::aux_data::AuxData;

use crate::bellman::pairing::{
    Engine,
    GenericCurveAffine,
    GenericCurveProjective,
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
        params: &'a RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>,
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
        params: &'a RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>,
        aux_data: &AD,
    ) -> Result<Self, SynthesisError> {

        use crate::plonk::circuit::Assignment;

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
        for idx in 0..num_quotient_commitments {
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
        for idx in 0..1 {
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
        params: &'a RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>,
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
        params: &'a RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>,
        non_residues: Vec<E::Fr>,
        aux_data: &AD,
    ) -> Result<Self, SynthesisError> {

        let num_selector_commitments = P::STATE_WIDTH + 2; 
        let num_next_step_selector_commitments = 1;

        let num_permutation_commitments = P::STATE_WIDTH;

        assert!(P::CAN_ACCESS_NEXT_TRACE_STEP);
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

        assert_eq!(w.len(), 0, "must consume all the witness");

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

pub trait IntoLimbedWitness<E: Engine> {
    fn into_witness(&self) -> Result<Vec<E::Fr>, SynthesisError> {
        unimplemented!()
    }
    fn witness_size_for_params(params: &RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base >) -> usize;
    fn into_witness_for_params(&self, _params: &RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base >) -> Result<Vec<E::Fr>, SynthesisError> {
        unimplemented!()
    }
}

impl<E: Engine, P: OldCSParams<E>> IntoLimbedWitness<E> for VerificationKey<E, P> {
    fn witness_size_for_params(params: &RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base >) -> usize {
        let mut base = 2;

        let per_coord = if params.can_allocate_from_double_limb_witness() {
            let mut num_witness = params.num_limbs_for_in_field_representation / 2;
            if params.num_limbs_for_in_field_representation % 2 != 0 {
                num_witness += 1;
            }

            num_witness
        } else {
            params.num_limbs_for_in_field_representation
        };

        let num_selector_commitments = P::STATE_WIDTH + 2; 
        let num_next_step_selector_commitments = 1;

        let num_permutation_commitments = P::STATE_WIDTH;

        assert!(P::CAN_ACCESS_NEXT_TRACE_STEP);
        assert!(!P::HAS_CUSTOM_GATES);

        base += num_selector_commitments * 2 * per_coord;
        base += num_next_step_selector_commitments * 2 * per_coord;
        base += num_permutation_commitments * 2 * per_coord;

        base
    }

    fn into_witness_for_params(&self, params: &RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>) -> Result<Vec<E::Fr>, SynthesisError> {
        use super::utils::verification_key_into_allocated_limb_witnesses;

        let as_limbs = verification_key_into_allocated_limb_witnesses(&self, params);

        Ok(as_limbs)
    }
}


impl<E: Engine, P: OldCSParams<E>> IntoLimbedWitness<E> for Proof<E, P> {
    fn witness_size_for_params(_params: &RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base >) -> usize {
        unimplemented!();
        // let mut base = 2;

        // let per_coord = if params.can_allocate_from_double_limb_witness() {
        //     let mut num_witness = params.num_limbs_for_in_field_representation / 2;
        //     if params.num_limbs_for_in_field_representation % 2 != 0 {
        //         num_witness += 1;
        //     }

        //     num_witness
        // } else {
        //     params.num_limbs_for_in_field_representation
        // };

        // let num_selector_commitments = P::STATE_WIDTH + 2; 
        // let num_next_step_selector_commitments = 1;

        // let num_permutation_commitments = P::STATE_WIDTH;

        // assert!(P::CAN_ACCESS_NEXT_TRACE_STEP);
        // assert!(!P::HAS_CUSTOM_GATES);

        // base += num_selector_commitments * 2 * per_coord;
        // base += num_next_step_selector_commitments * 2 * per_coord;
        // base += num_permutation_commitments * 2 * per_coord;

        // base
    }

    fn into_witness_for_params(&self, params: &RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>) -> Result<Vec<E::Fr>, SynthesisError> {
        use super::utils::proof_into_single_limb_witness;

        let as_limbs = proof_into_single_limb_witness(&self, params);

        Ok(as_limbs)
    }
}

pub trait IntoLimbedCircuitWitness<E: Engine> {
    fn into_witness<CS: ConstraintSystem<E>>(&self, _cs: &mut CS) -> Result<Vec<Num<E>>, SynthesisError> {
        unimplemented!()
    }
    // fn into_witness_for_params<F: PrimeField, CS: ConstraintSystem<E>>(&self, cs: &mut CS, params: &RnsParameters<E, F>) -> Result<Vec<AllocatedNum<E>>, SynthesisError> {
    //     unimplemented!()
    // }
}

impl<'a, E: Engine, WP: WrappedAffinePoint<'a, E>> IntoLimbedCircuitWitness<E> for ProofGadget<'a, E, WP> {
    fn into_witness<CS: ConstraintSystem<E>>(&self, _cs: &mut CS) -> Result<Vec<Num<E>>, SynthesisError> {
        let mut result = vec![];

        add_scalar_field_elements(&self.input_values, &mut result);
        add_points(&self.wire_commitments, &mut result);
        add_points(&[self.grand_product_commitment.clone()], &mut result);
        add_points(&self.quotient_poly_commitments, &mut result);

        add_scalar_field_elements(&self.wire_values_at_z, &mut result);
        add_scalar_field_elements(&self.wire_values_at_z_omega, &mut result);

        add_scalar_field_elements(&[self.grand_product_at_z_omega.clone()], &mut result);
        add_scalar_field_elements(&[self.quotient_polynomial_at_z.clone()], &mut result);
        add_scalar_field_elements(&[self.linearization_polynomial_at_z.clone()], &mut result);

        add_scalar_field_elements(&self.permutation_polynomials_at_z, &mut result);

        add_points(&[self.opening_at_z_proof.clone(), self.opening_at_z_omega_proof.clone()], &mut result);

        Ok(result)
    }
}


impl<'a, E: Engine, WP: WrappedAffinePoint<'a, E>> IntoLimbedCircuitWitness<E> for VerificationKeyGagdet<'a, E, WP> {
    fn into_witness<CS: ConstraintSystem<E>>(&self, _cs: &mut CS) -> Result<Vec<Num<E>>, SynthesisError> {
        assert!(self.domain_size_as_allocated_num.is_some(), "can only be called on a gadget with variable parameters");
        assert!(self.omega_as_allocated_num.is_some(), "can only be called on a gadget with variable parameters");

        let mut result = vec![];

        result.push(Num::Variable(self.domain_size_as_allocated_num.as_ref().unwrap().clone()));
        result.push(Num::Variable(self.omega_as_allocated_num.as_ref().unwrap().clone()));

        add_points(&self.selector_commitments, &mut result);
        add_points(&self.next_step_selector_commitments, &mut result);
        add_points(&self.permutation_commitments, &mut result);

        Ok(result)
    }
}

fn add_scalar_field_elements<E: Engine>(src: &[AllocatedNum<E>], dst: &mut Vec<Num<E>>) {
    for el in src.iter() {
        let num = Num::Variable(el.clone());
        dst.push(num);
    }
}

fn add_prime_field_elements<'a, E: Engine, F: PrimeField>(src: &[FieldElement<'a, E, F>], dst: &mut Vec<Num<E>>) {
    for el in src.iter() {
        for limb in el.binary_limbs.iter() {
            let as_num = limb.term.into_num();
            dst.push(as_num);
        }        
    }
}

fn add_points<'a, E: Engine, WP: WrappedAffinePoint<'a, E>>(src: &[WP], dst: &mut Vec<Num<E>>) {
    for el in src.iter() {
        let p = el.get_point();
        let x = p.x.clone();
        let y = p.y.clone();
        add_prime_field_elements(&[x, y], dst);   
    }
}