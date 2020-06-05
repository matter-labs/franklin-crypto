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

use crate::bellman::plonk::better_cs::cs::PlonkConstraintSystemParams;
use crate::bellman::plonk::better_cs::keys::{Proof, VerificationKey};
use crate::bellman::plonk::domains::*;

use crate::plonk::circuit::bigint::field::*;
use crate::plonk::circuit::curve::*;
use crate::plonk::circuit::boolean::*;
use crate::plonk::circuit::allocated_num::*;

use super::channel::*;
use super::data_structs::*;
use super::helper_functions::*;


pub struct PlonkVerifierCircuit<'a, E, T, P, AD> 
where E: Engine, T: ChannelGadget<E>, P: PlonkConstraintSystemParams<E>, AD: AuxData<E>
{
    _engine_marker : std::marker::PhantomData<E>,
    _channel_marker : std::marker::PhantomData<T>,

    channel_params: T::Params,

    public_inputs : Vec<E::Fr>,
    supposed_outputs: Vec<E::Fr>,
    proof: Proof<E, P>,
    vk: VerificationKey<E, P>,
    aux_data: AD,
    params: &'a RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
}


impl<'a, E, T, P, AD> PlonkVerifierCircuit<'a, E, T, P, AD> 
where E: Engine, T: ChannelGadget<E>, P: PlonkConstraintSystemParams<E>, AD: AuxData<E>
{
    pub fn new(
        channel_params: T::Params, 
        public_inputs: Vec<E::Fr>, 
        supposed_outputs: Vec<E::Fr>,
        proof: Proof<E, P>,
        vk: VerificationKey<E, P>,
        aux_data: AD,
        params: &'a RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
    ) -> Self 
    {

        PlonkVerifierCircuit {
            
            _engine_marker : std::marker::PhantomData::<E>,
            _channel_marker : std::marker::PhantomData::<T>,

            channel_params,
            public_inputs,
            supposed_outputs,

            proof,
            vk,
            aux_data,
            params,
        }
    }

    fn synthesize<CS: ConstraintSystem<E>>(
        mut self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {

        assert!(P::CAN_ACCESS_NEXT_TRACE_STEP);

        let mut channel = T::new(&self.channel_params);
        let proof = ProofGadget::alloc(cs, self.proof, self.params)?;
        let vk = VerificationKeyGagdet::alloc(cs, self.vk, self.params)?;
        
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
            channel.consume(*inp, cs)?;
        }

        // Commit wire values
        for w in proof.wire_commitments.iter() {
            channel.consume_point(cs, *w)?;
        }

        let beta = channel.produce_challenge(cs)?;
        let gamma = channel.produce_challenge(cs)?;

        // commit grand product
        channel.consume_point(cs, proof.grand_product_commitment)?;

        let alpha = channel.produce_challenge(cs)?;
    
        // Commit parts of the quotient polynomial
        for w in proof.quotient_poly_commitments.iter() {
            channel.consume_point(cs, *w)?;
        }

        let z = channel.produce_challenge(cs)?;
        // let mut z_by_omega = z.clone();
        // z_by_omega.scale(&domain.generator);

        // commit every claimed value

        for el in proof.wire_values_at_z.iter() {
            channel.consume(*el, cs)?;
        }

        for el in proof.wire_values_at_z_omega.iter() {
            channel.consume(*el, cs)?;
        }

        for el in proof.permutation_polynomials_at_z.iter() {
            channel.consume(*el, cs)?;
        }

        channel.consume(proof.quotient_polynomial_at_z, cs)?;
        channel.consume(proof.linearization_polynomial_at_z, cs)?;

        let omega_inv = domain.generator.inverse().expect("should exist");
        let domain_size_decomposed = decompose_const_to_bits::<E, _>(&[required_domain_size as u64]);
        let z_in_pow_domain_size = AllocatedNum::pow(cs, &z, &domain_size_decomposed)?;
        let l_0_at_z = evaluate_lagrange_poly(cs, required_domain_size, 0, &omega_inv, z, z_in_pow_domain_size)?;
        
        // do the actual check for relationship at z
        {
            let mut lhs = proof.quotient_polynomial_at_z;
            let vanishing_at_z = evaluate_vanishing_poly(cs, required_domain_size, &omega_inv, z.clone(), z_in_pow_domain_size.clone())?;
            lhs = lhs.mul(cs, &vanishing_at_z)?;

            let mut quotient_linearization_challenge = E::Fr::one();

            let mut rhs = proof.linearization_polynomial_at_z;

            // add public inputs
            {
                for (idx, input) in proof.input_values.iter().enumerate() {
                    let tmp = if idx == 0 {
                        l_0_at_z.mul(cs, &input)?
                    } else {
                        let tmp = evaluate_lagrange_poly(cs, required_domain_size, idx, &omega_inv, z, z_in_pow_domain_size)?;
                        tmp.mul(cs, &input)?
                    }; 
                    rhs = rhs.add(cs, &tmp)?;
                }
            }

            // - \alpha (a + perm(z) * beta + gamma)*()*(d + gamma) & z(z*omega)

            let mut z_part = proof.grand_product_at_z_omega;

            for (w, p) in proof.wire_values_at_z.iter().zip(proof.permutation_polynomials_at_z.iter()) {
                let mut tmp = *p;
                tmp = tmp.mul(cs, &beta)?;
                tmp = tmp.add(cs, &gamma)?;
                tmp = tmp.add(cs, &w)?;
                z_part = tmp.mul(cs, &tmp)?;
            }   

            // last poly value and gamma
            let mut tmp = gamma;
            tmp = tmp.add(cs, &proof.wire_values_at_z.iter().rev().next().unwrap())?;

            z_part = z_part.mul(cs, &tmp)?;
            z_part = z_part.mul(cs, &alpha)?;
            rhs = rhs.sub(cs, &z_part)?; 

            let quotient_linearization_challenge = alpha.mul(cs, &alpha)?;
            
            // - L_0(z) * \alpha^2
            let mut tmp = l_0_at_z.mul(cs, &quotient_linearization_challenge)?;
            rhs = rhs.sub(cs, &tmp)?;

            lhs.enforce_equal(cs, &rhs)?;
        }

        let v = channel.produce_challenge(cs)?;
        channel.consume_point(cs, proof.opening_at_z_proof)?;
        channel.consume_point(cs, proof.opening_at_z_omega_proof)?;

        let u = channel.produce_challenge(cs)?;

        // first let's reconstruct the linearization polynomial from
        // honomorphic commitments, and simultaneously add (through the separation scalar "u")
        // part for opening of z(X) at z*omega

        // calculate the power to add z(X) commitment that is opened at x*omega
        // it's r(X) + witness + all permutations + 1
        let v_power_for_standalone_z_x_opening = 1 + 1 + P::STATE_WIDTH + (P::STATE_WIDTH-1);

        let virtual_commitment_for_linearization_poly = {

            // main gate. Does NOT include public inputs
            {
                // Q_const(x)
                let mut r = vk.selector_commitments[selector_q_const_index];

                for i in 0..P::STATE_WIDTH {
                    // Q_k(X) * K(z)
                    let mut tmp = vk.selector_commitments[i].mul(cs, &proof.wire_values_at_z[i], None, self.params)?;
                    r = r.add(cs, &mut tmp, self.params)?;
                }

                // Q_m(X) * A(z) * B(z)
                let mut scalar = proof.wire_values_at_z[0];
                scalar = scalar.mul(cs, &proof.wire_values_at_z[1])?;
                let mut tmp = vk.selector_commitments[selector_q_m_index].mul(cs, &scalar, None, self.params)?;
                r = r.add(cs, &mut tmp, self.params)?;

                // Q_d_next(X) * D(z*omega)
                tmp = vk.next_step_selector_commitments[0].mul(cs, &proof.wire_values_at_z_omega[0], None, self.params)?;
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
            let d = decompose_const_to_bits(&[v_power_for_standalone_z_x_opening as u64]);
            v.pow(cs, d)?.mul(cs, &u)?
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
            let mut tmp = proof.grand_product_commitment.mul(cs, &grand_product_part_at_z, None, self.params)?;
            
            let mut tmp = proof.grand_product_commitment.mul(grand_product_part_at_z.into_repr());
            tmp.sub_assign(&verification_key.permutation_commitments.last().unwrap().mul(last_permutation_part_at_z.into_repr()));
            
            r.add_assign(&tmp);
        }

        r.mul_assign(v.into_repr());

        r.add_assign(&proof.grand_product_commitment.mul(grand_product_part_at_z_omega.into_repr()));

        r
    };

    // now check the openings

    let mut multiopening_challenge = E::Fr::one();

    // reassemble a homomorphic commitment

    // aggregate t(X) from parts

    let mut commitments_aggregation = proof.quotient_poly_commitments[0].into_projective();

    let mut current = z_in_domain_size;
    for part in proof.quotient_poly_commitments.iter().skip(1) {
        commitments_aggregation.add_assign(&part.mul(current.into_repr()));
        current.mul_assign(&z_in_domain_size);
    }

    // do the same for linearization
    multiopening_challenge.mul_assign(&v); // to preserve sequence
    commitments_aggregation.add_assign(&virtual_commitment_for_linearization_poly); // v^1 is contained inside

    debug_assert_eq!(multiopening_challenge, v.pow(&[1 as u64]));

    // do the same for wires
    for com in proof.wire_commitments.iter() {
        multiopening_challenge.mul_assign(&v); // v^{1+STATE_WIDTH}
        let tmp = com.mul(multiopening_challenge.into_repr());
        commitments_aggregation.add_assign(&tmp);
    }

    debug_assert_eq!(multiopening_challenge, v.pow(&[1 + 4 as u64]));

    // and for all permutation polynomials except the last one
    assert_eq!(verification_key.permutation_commitments.len(), proof.permutation_polynomials_at_z.len() + 1);

    for com in verification_key.permutation_commitments[0..(verification_key.permutation_commitments.len() - 1)].iter() {
        multiopening_challenge.mul_assign(&v); // v^{1+STATE_WIDTH + STATE_WIDTH - 1}
        let tmp = com.mul(multiopening_challenge.into_repr());
        commitments_aggregation.add_assign(&tmp);
    }

    multiopening_challenge.mul_assign(&v); // we skip z(X) at z

    // aggregate last wire commitment (that is opened at z*omega)
    // using multiopening challenge and u
    multiopening_challenge.mul_assign(&v);
    let mut scalar = multiopening_challenge;
    scalar.mul_assign(&u);
    commitments_aggregation.add_assign(&proof.wire_commitments.last().unwrap().mul(scalar.into_repr()));

    // subtract the opening value using one multiplication

    let mut multiopening_challenge_for_values = E::Fr::one();
    let mut aggregated_value = proof.quotient_polynomial_at_z;
    for value_at_z in Some(proof.linearization_polynomial_at_z).iter()
            .chain(&proof.wire_values_at_z)
            .chain(&proof.permutation_polynomials_at_z) 
        {
            multiopening_challenge_for_values.mul_assign(&v);   
            let mut tmp = *value_at_z;
            tmp.mul_assign(&multiopening_challenge_for_values);
            aggregated_value.add_assign(&tmp);
        }

    // add parts that are opened at z*omega using `u`
    {
        multiopening_challenge_for_values.mul_assign(&v);  
        let mut scalar = multiopening_challenge_for_values;
        scalar.mul_assign(&u);
        let mut tmp = proof.grand_product_at_z_omega;
        tmp.mul_assign(&scalar);

        aggregated_value.add_assign(&tmp);
    }
    {
        multiopening_challenge_for_values.mul_assign(&v);  
        let mut scalar = multiopening_challenge_for_values;
        scalar.mul_assign(&u);
        let mut tmp = proof.wire_values_at_z_omega[0];
        tmp.mul_assign(&scalar);

        aggregated_value.add_assign(&tmp);
    }

    assert_eq!(multiopening_challenge, multiopening_challenge_for_values);

    // make equivalent of (f(x) - f(z))
    commitments_aggregation.sub_assign(&E::G1Affine::one().mul(aggregated_value.into_repr()));

    // now check that
    // e(proof_for_z + u*proof_for_z_omega, g2^x) = e(z*proof_for_z + z*omega*u*proof_for_z_omega + (aggregated_commitment - aggregated_opening), g2^1) 
    // with a corresponding change of sign

    let mut pair_with_generator = commitments_aggregation;

    pair_with_generator.add_assign(&proof.opening_at_z_proof.mul(z.into_repr()));
    let mut scalar = z_by_omega;
    scalar.mul_assign(&u);
    pair_with_generator.add_assign(&proof.opening_at_z_omega_proof.mul(scalar.into_repr()));

    let mut pair_with_x = proof.opening_at_z_omega_proof.mul(u.into_repr());
    pair_with_x.add_assign_mixed(&proof.opening_at_z_proof);
    pair_with_x.negate();

    let valid = E::final_exponentiation(
        &E::miller_loop(&[
            (&pair_with_generator.into_affine().prepare(), &verification_key.g2_elements[0].prepare()),
            (&pair_with_x.into_affine().prepare(), &verification_key.g2_elements[1].prepare())
        ])
    ).unwrap() == E::Fqk::one();

    Ok(valid)
}