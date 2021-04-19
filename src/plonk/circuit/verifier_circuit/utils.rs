use crate::plonk::circuit::allocated_num::*;
use crate::plonk::circuit::linear_combination::*;
use crate::plonk::circuit::rescue::*;
use crate::rescue::*;

use crate::plonk::circuit::bigint::field::*;
use crate::plonk::circuit::bigint::bigint::*;

use crate::bellman::pairing::{Engine, GenericCurveAffine};
use crate::bellman::pairing::ff::PrimeField;

use crate::bellman::plonk::better_cs::keys::{Proof, VerificationKey};
use crate::bellman::plonk::better_cs::cs::PlonkConstraintSystemParams as OldCSParams;
use crate::bellman::plonk::better_cs::cs::Circuit as OldCircuit;
use crate::bellman::plonk::better_cs::cs::ConstraintSystem as OldConstraintSystem;
use crate::bellman::plonk::better_cs::cs::PlonkCsWidth4WithNextStepParams as OldActualParams;

use crate::bellman::plonk::domains::*;

pub fn verification_key_into_allocated_limb_witnesses<E: Engine, P: OldCSParams<E>>(
    vk: &VerificationKey<E, P>,
    params: &RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>) -> Vec<E::Fr> 
        // where <E::G1Affine as GenericCurveAffine>::Base: PrimeField 
    {
    // we encode
    // domain size
    // domain generator
    // selectors
    // next step selector
    // permutation selectors

    let mut encodings = vec![];

    let required_domain_size = vk.n + 1;
    assert!(required_domain_size.is_power_of_two());
    let domain_size = E::Fr::from_str(&required_domain_size.to_string()).unwrap();

    encodings.push(domain_size);

    let domain = Domain::<E::Fr>::new_for_size(required_domain_size as u64).unwrap();
    let omega = domain.generator;

    encodings.push(omega);

    for s in vk.selector_commitments.iter() {
        assert!(!s.is_zero());
        let (x, y) = s.into_xy_unchecked();

        for coord in [x, y].iter() {
            let w = field_to_witness(coord, params);
            encodings.extend(w);
        }
    }

    for s in vk.next_step_selector_commitments.iter() {
        assert!(!s.is_zero());
        let (x, y) = s.into_xy_unchecked();

        for coord in [x, y].iter() {
            let w = field_to_witness(coord, params);
            encodings.extend(w);
        }
    }

    for s in vk.permutation_commitments.iter() {
        assert!(!s.is_zero());
        let (x, y) = s.into_xy_unchecked();

        for coord in [x, y].iter() {
            let w = field_to_witness(coord, params);
            encodings.extend(w);
        }
    }

    encodings
}

pub fn proof_into_allocated_limb_witnesses<E: Engine, P: OldCSParams<E>>(
    proof: &Proof<E, P>,
    params: &RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>) -> Vec<E::Fr> 
    {
    // we encode
    // inputs
    // witness commitments
    // grand product commitment
    // quotient commitments
    // openings
    // proof at z
    // proof at z*omega

    let mut encodings = vec![];

    encodings.extend_from_slice(&proof.input_values);

    add_points(&proof.wire_commitments, &mut encodings, params);

    add_point(&proof.grand_product_commitment, &mut encodings, params);

    add_points(&proof.quotient_poly_commitments, &mut encodings, params);

    encodings.extend_from_slice(&proof.wire_values_at_z);

    encodings.extend_from_slice(&proof.wire_values_at_z_omega);

    encodings.push(proof.grand_product_at_z_omega);
    encodings.push(proof.quotient_polynomial_at_z);
    encodings.push(proof.linearization_polynomial_at_z);

    encodings.extend_from_slice(&proof.permutation_polynomials_at_z);

    add_point(&proof.opening_at_z_proof, &mut encodings, params);
    add_point(&proof.opening_at_z_omega_proof, &mut encodings, params);

    encodings
}

pub fn proof_into_single_limb_witness<E: Engine, P: OldCSParams<E>>(
    proof: &Proof<E, P>,
    params: &RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>) -> Vec<E::Fr> 
{
    // change the params

    let mut new_params = params.clone();
    new_params.set_prefer_single_limb_allocation(true);

    let params = &new_params;
    // we encode
    // inputs
    // witness commitments
    // grand product commitment
    // quotient commitments
    // openings
    // proof at z
    // proof at z*omega

    let mut encodings = vec![];

    encodings.extend_from_slice(&proof.input_values);

    add_points(&proof.wire_commitments, &mut encodings, params);

    add_point(&proof.grand_product_commitment, &mut encodings, params);

    add_points(&proof.quotient_poly_commitments, &mut encodings, params);

    encodings.extend_from_slice(&proof.wire_values_at_z);

    encodings.extend_from_slice(&proof.wire_values_at_z_omega);

    encodings.push(proof.grand_product_at_z_omega);
    encodings.push(proof.quotient_polynomial_at_z);
    encodings.push(proof.linearization_polynomial_at_z);

    encodings.extend_from_slice(&proof.permutation_polynomials_at_z);

    add_point(&proof.opening_at_z_proof, &mut encodings, params);
    add_point(&proof.opening_at_z_omega_proof, &mut encodings, params);

    encodings
}

pub fn field_to_witness<E: Engine, F: PrimeField>(element: &F, params: &RnsParameters<E, F>) -> Vec<E::Fr> {
    if params.can_allocate_from_double_limb_witness() {
        let mut num_witness = params.num_limbs_for_in_field_representation / 2;
        if params.num_limbs_for_in_field_representation % 2 != 0 {
            num_witness += 1;
        }

        let coord_as_bigint = fe_to_biguint(element);

        let witness_limbs = split_into_fixed_number_of_limbs(
            coord_as_bigint, 
            params.binary_limbs_params.limb_size_bits * 2, 
            num_witness
        );

        let witnesses: Vec<_> = witness_limbs.into_iter().map(|el| biguint_to_fe::<E::Fr>(el)).collect();

        witnesses
    } else {
        let num_witness = params.num_limbs_for_in_field_representation;

        let coord_as_bigint = fe_to_biguint(element);

        let witness_limbs = split_into_fixed_number_of_limbs(
            coord_as_bigint, 
            params.binary_limbs_params.limb_size_bits, 
            num_witness
        );

        let witnesses: Vec<_> = witness_limbs.into_iter().map(|el| biguint_to_fe::<E::Fr>(el)).collect();

        witnesses
    }
}

pub fn add_point<E: Engine>(src: &E::G1Affine, dst: &mut Vec<E::Fr>, params: &RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>) {
    assert!(!src.is_zero());
    let (x, y) = src.into_xy_unchecked();

    for coord in [x, y].iter() {
        let w = field_to_witness(coord, params);
        dst.extend(w);
    }
}

pub fn add_points<E: Engine>(src: &[E::G1Affine], dst: &mut Vec<E::Fr>, params: &RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>) {
    for s in src.iter() {
        add_point(s, dst, params);
    }
}