#![feature(core_intrinsics)]

use crate::bellman::pairing::{
    Engine,
    CurveAffine,
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
};

use crate::bellman::plonk::better_better_cs::cs::*;
use crate::bellman::plonk::better_cs::keys::{Proof, VerificationKey};
use crate::bellman::plonk::better_cs::cs::PlonkConstraintSystemParams as OldCSParams;
use crate::bellman::plonk::domains::*;

use crate::plonk::circuit::bigint::field::*;
use crate::plonk::circuit::curve::*;
use crate::plonk::circuit::boolean::*;
use crate::plonk::circuit::allocated_num::*;

use super::channel::*;
use super::data_structs::*;
use super::helper_functions::*;
use super::affine_point_wrapper::aux_data::AuxData;
use super::affine_point_wrapper::WrappedAffinePoint;

use std::cell::Cell;


pub struct PlonkVerifierCircuit<'a, E, T, P, OldP, AD, WP> 
where 
E: Engine, T: ChannelGadget<E>, AD: AuxData<E>, OldP: OldCSParams<E>, 
P: PlonkConstraintSystemParams<E>, WP: WrappedAffinePoint<'a, E>,
{
    _engine_marker : std::marker::PhantomData<E>,
    _channel_marker : std::marker::PhantomData<T>,
    _cs_params_marker: std::marker::PhantomData<P>,
    _point_wrapper_marker: std::marker::PhantomData<WP>,

    channel_params: &'a T::Params,

    public_inputs : Vec<E::Fr>,
    supposed_outputs: Vec<E::G1Affine>,
    proof: Cell<Option<Proof<E, OldP>>>,
    vk: Cell<Option<VerificationKey<E, OldP>>>,
    aux_data: AD,
    params: &'a RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
}


impl<'a, E, T, P, OldP, AD, WP> PlonkVerifierCircuit<'a, E, T, P, OldP, AD, WP> 
where 
E: Engine, T: ChannelGadget<E>, AD: AuxData<E>, P: PlonkConstraintSystemParams<E>, 
OldP: OldCSParams<E>, WP: WrappedAffinePoint<'a, E>,
{
    pub fn new(
        channel_params: &'a T::Params, 
        public_inputs: Vec<E::Fr>, 
        supposed_outputs: Vec<E::G1Affine>,
        proof: Proof<E, OldP>,
        vk: VerificationKey<E, OldP>,
        aux_data: AD,
        params: &'a RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
    ) -> Self 
    {

        PlonkVerifierCircuit {
            
            _engine_marker : std::marker::PhantomData::<E>,
            _channel_marker : std::marker::PhantomData::<T>,
            _cs_params_marker: std::marker::PhantomData::<P>,
            _point_wrapper_marker: std::marker::PhantomData::<WP>,

            channel_params,
            public_inputs,
            supposed_outputs,

            proof: Cell::new(Some(proof)),
            vk: Cell::new(Some(vk)),
            aux_data,
            params,
        }
    }
}

impl<'a, E, T, P, OldP, AD, WP> Circuit<E> for PlonkVerifierCircuit<'a, E, T, P, OldP, AD, WP> 
where 
E: Engine, T: ChannelGadget<E>, AD: AuxData<E>, P: PlonkConstraintSystemParams<E>, 
OldP: OldCSParams<E>, WP: WrappedAffinePoint<'a, E>
{
    fn synthesize<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {

        assert!(P::CAN_ACCESS_NEXT_TRACE_STEP);

        let mut channel = T::new(self.channel_params);

        let actual_proof = self.proof.replace(None);
        let actual_vk = self.vk.replace(None);

        let mut proof = ProofGadget::<E, WP>::alloc(cs, actual_proof.unwrap(), self.params, &self.aux_data)?;
        let mut vk = VerificationKeyGagdet::<E, WP>::alloc(cs, actual_vk.unwrap(), self.params, &self.aux_data)?;
        
        if proof.n != vk.n {
            return Err(SynthesisError::MalformedVerifyingKey);
        }

        if proof.num_inputs != vk.num_inputs {
            return Err(SynthesisError::MalformedVerifyingKey);
        }

        let n = proof.n;
        let required_domain_size = n + 1;
        if required_domain_size.is_power_of_two() == false {
            return Err(SynthesisError::MalformedVerifyingKey);
        }
        let domain = Domain::<E::Fr>::new_for_size(required_domain_size as u64)?;

        let selector_q_const_index = P::STATE_WIDTH + 1;
        let selector_q_m_index = P::STATE_WIDTH;

        // Commit public inputs
        for inp in proof.input_values.iter() {
            channel.consume(inp.clone(), cs)?;
        }

        // Commit wire values
        for w in proof.wire_commitments.iter() {
            channel.consume_point(cs, w.clone())?;
        }

        let beta = channel.produce_challenge(cs)?;
        let gamma = channel.produce_challenge(cs)?;

        // commit grand product
        channel.consume_point(cs, proof.grand_product_commitment.clone())?;

        let alpha = channel.produce_challenge(cs)?;
    
        // Commit parts of the quotient polynomial
        for w in proof.quotient_poly_commitments.iter() {
            channel.consume_point(cs, w.clone())?;
        }

        let z = channel.produce_challenge(cs)?;
        // let mut z_by_omega = z.clone();
        // z_by_omega.scale(&domain.generator);

        // commit every claimed value

        for el in proof.wire_values_at_z.iter() {
            channel.consume(el.clone(), cs)?;
        }

        for el in proof.wire_values_at_z_omega.iter() {
            channel.consume(el.clone(), cs)?;
        }

        for el in proof.permutation_polynomials_at_z.iter() {
            channel.consume(el.clone(), cs)?;
        }

        channel.consume(proof.quotient_polynomial_at_z.clone(), cs)?;
        channel.consume(proof.linearization_polynomial_at_z.clone(), cs)?;

        println!("C");

        let omega_inv = domain.generator.inverse().expect("should exist");
        let domain_size_decomposed = decompose_const_to_bits::<E, _>(&[required_domain_size as u64]);
        let z_in_pow_domain_size = AllocatedNum::pow(cs, &z, &domain_size_decomposed)?;
        let l_0_at_z = evaluate_lagrange_poly(cs, required_domain_size, 0, &omega_inv, z.clone(), z_in_pow_domain_size.clone())?;
        
        // do the actual check for relationship at z
        {
            let mut lhs = proof.quotient_polynomial_at_z.clone();
            let tmp_arg = z_in_pow_domain_size.clone();
            let vanishing_at_z = evaluate_vanishing_poly(cs, required_domain_size, &omega_inv, z.clone(), tmp_arg)?;
            lhs = lhs.mul(cs, &vanishing_at_z)?;

            let quotient_linearization_challenge = E::Fr::one();

            let mut rhs = proof.linearization_polynomial_at_z.clone();

            // add public inputs
            {
                for (idx, input) in proof.input_values.iter().enumerate() {
                    let tmp = if idx == 0 {
                        l_0_at_z.mul(cs, &input)?
                    } else {
                        let tmp = evaluate_lagrange_poly(cs, required_domain_size, idx, &omega_inv, z.clone(), z_in_pow_domain_size.clone())?;
                        tmp.mul(cs, &input)?
                    }; 
                    rhs = rhs.add(cs, &tmp)?;
                }
            }

            // - \alpha (a + perm(z) * beta + gamma)*()*(d + gamma) & z(z*omega)

            let mut z_part = proof.grand_product_at_z_omega.clone();

            for (w, p) in proof.wire_values_at_z.iter().zip(proof.permutation_polynomials_at_z.iter()) {
                let mut tmp = p.clone();
                tmp = tmp.mul(cs, &beta)?;
                tmp = tmp.add(cs, &gamma)?;
                tmp = tmp.add(cs, &w)?;
                z_part = tmp.mul(cs, &tmp)?;
            }   

            // last poly value and gamma
            let mut tmp = gamma.clone();
            tmp = tmp.add(cs, &proof.wire_values_at_z.iter().rev().next().unwrap())?;

            z_part = z_part.mul(cs, &tmp)?;
            z_part = z_part.mul(cs, &alpha)?;
            rhs = rhs.sub(cs, &z_part)?; 

            let quotient_linearization_challenge = alpha.mul(cs, &alpha)?;
            
            // - L_0(z) * \alpha^2
            let tmp = l_0_at_z.mul(cs, &quotient_linearization_challenge)?;
            rhs = rhs.sub(cs, &tmp)?;

            lhs.enforce_equal(cs, &rhs)?;
        }

        let v = channel.produce_challenge(cs)?;
        channel.consume_point(cs, proof.opening_at_z_proof.clone())?;
        channel.consume_point(cs, proof.opening_at_z_omega_proof.clone())?;

        let u = channel.produce_challenge(cs)?;

        // first let's reconstruct the linearization polynomial from
        // honomorphic commitments, and simultaneously add (through the separation scalar "u")
        // part for opening of z(X) at z*omega

        // calculate the power to add z(X) commitment that is opened at x*omega
        // it's r(X) + witness + all permutations + 1
        let v_power_for_standalone_z_x_opening = 1 + 1 + P::STATE_WIDTH + (P::STATE_WIDTH-1);
        println!("D");

        let mut virtual_commitment_for_linearization_poly = {

            let mut r;

            // main gate. Does NOT include public inputs
            {
                // Q_const(x)
                r = vk.selector_commitments[selector_q_const_index].clone();

                for i in 0..P::STATE_WIDTH {
                    // Q_k(X) * K(z)
                    // here multiexp may be used
                    let mut tmp = vk.selector_commitments[i].mul(cs, &proof.wire_values_at_z[i], None, self.params, &self.aux_data)?;
                    r = r.add(cs, &mut tmp, self.params)?;
                }

                // Q_m(X) * A(z) * B(z)
                // add to multiexp as well
                let mut scalar = proof.wire_values_at_z[0].clone();
                scalar = scalar.mul(cs, &proof.wire_values_at_z[1])?;
                let mut tmp = vk.selector_commitments[selector_q_m_index].mul(cs, &scalar, None, self.params, &self.aux_data)?;
                r = r.add(cs, &mut tmp, self.params)?;

                // Q_d_next(X) * D(z*omega)
                tmp = vk.next_step_selector_commitments[0].mul(cs, &proof.wire_values_at_z_omega[0], None, self.params, &self.aux_data)?;
                r = r.add(cs, &mut tmp, self.params)?;
            }

            // v * [alpha * (a + beta*z + gamma)(b + beta*k_1*z + gamma)()() * z(X) -
            // - \alpha * (a*perm_a(z)*beta + gamma)()()*beta*z(z*omega) * perm_d(X) +
            // + alpha^2 * L_0(z) * z(X) ] + 
            // + v^{P} * u * z(X)
            // and join alpha^2 * L_0(z) and v^{P} * u into the first term containing z(X)

            // [alpha * (a + beta*z + gamma)(b + beta*k_1*z + gamma)()() + alpha^2 * L_0(z)] * z(X)
            let grand_product_part_at_z = {
                let mut scalar = AllocatedNum::dumb();

                // permutation part
                for (i, (wire, non_res)) in proof.wire_values_at_z.iter()
                                .zip(Some(E::Fr::one()).iter().chain(&vk.non_residues)).enumerate() 
                {
                    // tmp = non_res * z * beta + wire
                    let zero = E::Fr::zero();
                    let one = E::Fr::one();
                    let mut tmp = AllocatedNum::general_equation(cs, &z, &beta, &wire, non_res, &zero, &zero, &one, &zero)?;
                    // on first iteration: scalar = tmp + gamma
                    // else: scalar = scalar * (tmp + gamma)
                    if i == 0 {
                        scalar = tmp.add(cs, &gamma)?;
                    }
                    else {
                        tmp = tmp.add(cs, &gamma)?;
                        scalar = scalar.mul(cs, &tmp)?;
                    }
                }

                scalar = scalar.mul(cs, &alpha)?;

                // + L_0(z) * alpha^2
                let tmp = l_0_at_z.mul(cs, &alpha)?.mul(cs, &alpha)?;
                scalar.add(cs, &tmp)?
            };

            // v^{P} * u * z(X)
            let grand_product_part_at_z_omega = {
                // + v^{P} * u
                let d = decompose_const_to_bits::<E, _>(&[v_power_for_standalone_z_x_opening as u64]);
                AllocatedNum::pow(cs, &v, d)?.mul(cs, &u)?
            };

            // \alpha * (a*perm_a(z)*beta + gamma)()()*beta*z(z*omega) * perm_d(X)
            let last_permutation_part_at_z = {
                let mut scalar = AllocatedNum::dumb();

                // permutation part
                for (i, (wire, perm_at_z)) in proof.wire_values_at_z.iter()
                                .zip(&proof.permutation_polynomials_at_z).enumerate() 
                {
                    // tmp = perm_at_z * beta + wire
                    let zero = E::Fr::zero();
                    let one = E::Fr::one();
                    let mut tmp = AllocatedNum::general_equation(cs, &perm_at_z, &beta, &wire, &one, &zero, &zero, &one, &zero)?;
                    // on first iteration: scalar = tmp + gamma
                    // else: scalar = scalar * (tmp + gamma)
                    if i == 0 {
                        scalar = tmp.add(cs, &gamma)?;
                    }
                    else {
                        tmp = tmp.add(cs, &gamma)?;
                        scalar = scalar.mul(cs, &tmp)?;
                    }
                    
                }

                scalar = scalar.mul(cs, &beta)?.mul(cs, &proof.grand_product_at_z_omega)?.mul(cs, &alpha)?;
                scalar
            };


            {
                // also add to multiexp
                let mut tmp1 = proof.grand_product_commitment.mul(cs, &grand_product_part_at_z, None, self.params, &self.aux_data)?;
                 
                let mut tmp2 = vk.permutation_commitments.last_mut().unwrap().mul(
                    cs, &last_permutation_part_at_z, None, self.params, &self.aux_data)?;
                     
                tmp1 = tmp1.sub(cs, &mut tmp2, self.params)?;
               
                r = r.add(cs, &mut tmp1, self.params)?;
            }

            r = r.mul(cs, &v, None, self.params, &self.aux_data)?;
            let mut tmp = proof.grand_product_commitment.mul(cs, &grand_product_part_at_z_omega, None, self.params, &self.aux_data)?;
            r = r.add(cs, &mut tmp, self.params)?;

            r
        };

        // now check the openings
        // aggregate t(X) from parts

        let mut commitments_aggregation = proof.quotient_poly_commitments[0].clone();

        let mut current = z_in_pow_domain_size.clone();
        for part in proof.quotient_poly_commitments.iter_mut().skip(1) {
            //second multiexp
            let mut temp = part.mul(cs, &current, None, self.params, &self.aux_data)?;
            commitments_aggregation = commitments_aggregation.add(cs, &mut temp, self.params)?;
            current = current.mul(cs, &z_in_pow_domain_size)?;
        }

        commitments_aggregation = commitments_aggregation.add(cs, &mut virtual_commitment_for_linearization_poly, self.params)?;
        let mut multiopening_challenge = v.clone();

        // do the same for wires
        for com in proof.wire_commitments.iter_mut() {
            // add to second multiexp as well
            multiopening_challenge = multiopening_challenge.mul(cs, &v)?; 
            let mut tmp = com.mul(cs, &multiopening_challenge, None, self.params, &self.aux_data)?;
            commitments_aggregation = commitments_aggregation.add(cs, &mut tmp, self.params)?;
        }

        // and for all permutation polynomials except the last one
        assert_eq!(vk.permutation_commitments.len(), proof.permutation_polynomials_at_z.len() + 1);
        
        let arr_len = vk.permutation_commitments.len();
        for com in vk.permutation_commitments[0..(arr_len - 1)].iter_mut() {
            // v^{1+STATE_WIDTH + STATE_WIDTH - 1}
            // second multiexp
            let mut tmp = com.mul(cs, &multiopening_challenge, None, self.params, &self.aux_data)?;
            commitments_aggregation = commitments_aggregation.add(cs, &mut tmp, self.params)?;
        }
        
        // we skip z(X) at z
        multiopening_challenge = multiopening_challenge.mul(cs, &v)?; 

        // aggregate last wire commitment (that is opened at z*omega)
        // using multiopening challenge and u
        multiopening_challenge = multiopening_challenge.mul(cs, &v)?; 
        let scalar = multiopening_challenge.mul(cs, &u)?;
        // add to second multiexp
        let mut tmp = proof.wire_commitments.last_mut().unwrap().mul(cs, &scalar, None, self.params, &self.aux_data)?;
        commitments_aggregation = commitments_aggregation.add(cs, &mut tmp, self.params)?;

        // subtract the opening value using one multiplication

        let mut multiopening_challenge_for_values = AllocatedNum::dumb();
        let mut aggregated_value = proof.quotient_polynomial_at_z;
        for (i, value_at_z) in Some(proof.linearization_polynomial_at_z).iter()
                .chain(&proof.wire_values_at_z)
                .chain(&proof.permutation_polynomials_at_z)
                .enumerate() 
        {
            multiopening_challenge_for_values = if i == 0 {
                v.clone() 
            } else { 
                multiopening_challenge_for_values.mul(cs, &v)?  
            };
            
            let tmp = value_at_z.mul(cs, &multiopening_challenge_for_values)?;
            aggregated_value = aggregated_value.add(cs, &tmp)?;
        }

        // add parts that are opened at z*omega using `u`
        {
            multiopening_challenge_for_values = multiopening_challenge_for_values.mul(cs, &v)?;  
            let scalar = multiopening_challenge_for_values.mul(cs, &u)?;
            let tmp = proof.grand_product_at_z_omega.mul(cs, &scalar)?;
            aggregated_value = aggregated_value.add(cs, &tmp)?;
        }
    
        {
            multiopening_challenge_for_values = multiopening_challenge_for_values.mul(cs, &v)?; 
            let scalar = multiopening_challenge_for_values.mul(cs, &u)?;
            let tmp = proof.wire_values_at_z_omega[0].mul(cs, &scalar)?;
            aggregated_value = aggregated_value.add(cs, &tmp)?;
        }

        println!("ttt");

        // make equivalent of (f(x) - f(z))
        // also add to second multiexp
        let mut tmp = WP::constant(E::G1Affine::one(), self.params);
        tmp = tmp.mul(cs, &aggregated_value, None, self.params, &self.aux_data)?;
        commitments_aggregation = commitments_aggregation.sub(cs, &mut tmp, self.params)?;

        // next, we need to check that
        // e(proof_for_z + u*proof_for_z_omega, g2^x) = 
        // e(z*proof_for_z + z*omega*u*proof_for_z_omega + (aggregated_commitment - aggregated_opening), g2^1) 
        // however, we are going to compute the pairing itself outside the circuit
        // here we only go to prepare the pairing argumets:
        // arg1 = proof_for_z + u*proof_for_z_omega
        // arg2 = z*proof_for_z + z*omega*u*proof_for_z_omega + (aggregated_commitment - aggregated_opening)

        let mut arg1 = proof.opening_at_z_omega_proof.mul(cs, &u, None, self.params, &self.aux_data)?;
        arg1 = arg1.add(cs, &mut proof.opening_at_z_proof, self.params)?;

        // to second multiexp
        let mut tmp = proof.opening_at_z_proof.mul(cs, &z, None, self.params, &self.aux_data)?;
        let mut arg2 = commitments_aggregation.add(cs, &mut tmp, self.params)?;
      
        let scalar = AllocatedNum::mul_scaled(cs, &z, &u, &domain.generator)?;
        let mut tmp = proof.opening_at_z_omega_proof.mul(cs, &scalar, None, self.params, &self.aux_data)?;
        //to second multiexp
        arg2 = arg2.add(cs, &mut tmp, self.params)?;

        // check if arg_i = supposed_output_i
        // TODO: suppused_outputs shoulf be definitely public

        let supposed_output_0 = WrappedAffinePoint::alloc_unchecked(cs, None, self.params)?;
        let supposed_output_1 = WrappedAffinePoint::alloc_unchecked(cs, None, self.params)?;

        let comp1 = arg1.equals(cs, &supposed_output_0, self.params)?;
        let comp2 = arg2.equals(cs, &supposed_output_1, self.params)?;
        let final_comp = Boolean::and(cs, &comp1, &comp2)?;

        Boolean::enforce_equal(cs, &final_comp, &Boolean::constant(true))?;

        Ok(())
    }
}