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
use crate::plonk::circuit::simple_term::*;

use super::channel::*;
use super::data_structs::*;
use super::helper_functions::*;
use super::affine_point_wrapper::aux_data::AuxData;
use super::affine_point_wrapper::WrappedAffinePoint;

use std::cell::Cell;

#[track_caller]
pub fn aggregate_proof<'a, E, CS, T, P, OldP, AD, WP>(
    cs: &mut CS,
    channel_params: &'a T::Params,
    public_inputs: &[AllocatedNum<E>],
    vk: &VerificationKeyGagdet<'a, E, WP>,
    proof: &ProofGadget<'a, E, WP>,
    aux_data: &AD,
    params: &'a RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
) -> Result<[WP; 2], SynthesisError>
    where 
    E: Engine, CS: ConstraintSystem<E>, T: ChannelGadget<E>, AD: AuxData<E>, OldP: OldCSParams<E>, 
    P: PlonkConstraintSystemParams<E>, WP: WrappedAffinePoint<'a, E>
{
    assert!(P::CAN_ACCESS_NEXT_TRACE_STEP);

    let mut channel = T::new(channel_params);

    if proof.num_inputs != vk.num_inputs {
        return Err(SynthesisError::MalformedVerifyingKey);
    }

    let required_domain_size = if let Some(n) = vk.n {
        assert!(vk.domain_size_as_allocated_num.is_none());
        let required_domain_size = n + 1;
        if required_domain_size.is_power_of_two() == false {
            return Err(SynthesisError::MalformedVerifyingKey);
        }

        Some(required_domain_size)
    } else {
        assert!(vk.domain_size_as_allocated_num.is_some());

        None
    };

    let (omega_const, omega_inv_const) = if let Some(required_domain_size) = required_domain_size {
        let domain = Domain::<E::Fr>::new_for_size(required_domain_size as u64)?;
        let omega = domain.generator;
        let omega_inv = domain.generator.inverse().expect("should exist");

        (Some(omega), Some(omega_inv))
    } else {
        (None, None)
    };

    let domain_size_decomposed = if let Some(domain_size) = vk.domain_size_as_allocated_num.as_ref() {
        assert!(vk.n.is_none());
        let absolute_limit = (E::Fr::S + 1) as usize;
        let decomposed = domain_size.into_bits_le(cs, Some(absolute_limit))?;

        Some(decomposed)
    } else {
        assert!(vk.n.is_some());

        None
    };

    let selector_q_const_index = P::STATE_WIDTH + 1;
    let selector_q_m_index = P::STATE_WIDTH;

    // Commit public inputs
    for inp in proof.input_values.iter() {
        channel.consume(inp.clone(), cs)?;
    }

    for (inp, inp_from_proof) in public_inputs.iter().zip(proof.input_values.iter()) {
        inp.enforce_equal(cs, inp_from_proof)?;
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
    channel.consume(proof.grand_product_at_z_omega.clone(), cs)?;

    let z_in_pow_domain_size = if let Some(required_domain_size) = required_domain_size {
        assert!(required_domain_size.is_power_of_two());
        let mut z_in_pow_domain_size = z.clone();
        for _ in 0..required_domain_size.trailing_zeros() {
            z_in_pow_domain_size = z_in_pow_domain_size.square(cs)?;
        }

        z_in_pow_domain_size
    } else {
        let pow_decomposition = domain_size_decomposed.as_ref().unwrap();

        let mut pow_decomposition = pow_decomposition.to_vec();
        pow_decomposition.reverse();

        let z_in_pow_domain_size = AllocatedNum::<E>::pow(cs, &z, &pow_decomposition)?;

        z_in_pow_domain_size
    };

    let omega_inv_variable = if let Some(omega) = vk.omega_as_allocated_num.as_ref() {
        let inv = omega.inverse(cs).expect(&format!("Inverse of the domain generator must exist! Omega = {:?}", omega.get_value()));

        Some(inv)
    } else {
        None
    };

    let l_0_at_z = if let Some(required_domain_size) = required_domain_size { 
        let omega_inv = omega_inv_const.unwrap();
        let l_0_at_z = evaluate_lagrange_poly(
            cs, 
            required_domain_size, 
            0, 
            &omega_inv, 
            z.clone(), 
            z_in_pow_domain_size.clone()
        )?;

        l_0_at_z
    } else {
        let l_0_at_z = evaluate_lagrange_poly_for_variable_domain_size(
            cs,
            0,
            vk.domain_size_as_allocated_num.as_ref().unwrap().clone(),
            omega_inv_variable.as_ref().unwrap(),
            z.clone(), 
            z_in_pow_domain_size.clone()
        )?;

        l_0_at_z
    };

    // do the actual check for relationship at z
    {
        let mut lhs = proof.quotient_polynomial_at_z.clone();
        let vanishing_at_z = evaluate_vanishing_poly(cs, z_in_pow_domain_size.clone())?;
        lhs = lhs.mul(cs, &vanishing_at_z)?;

        let mut rhs = proof.linearization_polynomial_at_z.clone();

        // add public inputs
        {
            for (idx, input) in proof.input_values.iter().enumerate() {
                let tmp = if idx == 0 {
                    l_0_at_z.mul(cs, &input)?
                } else {
                    let tmp = if let Some(required_domain_size) = required_domain_size { 
                        let omega_inv = omega_inv_const.unwrap();
                        let tmp = evaluate_lagrange_poly(cs, required_domain_size, idx, &omega_inv, z.clone(), z_in_pow_domain_size.clone())?;

                        tmp
                    } else {
                        let tmp = evaluate_lagrange_poly_for_variable_domain_size(
                            cs,
                            idx,
                            vk.domain_size_as_allocated_num.as_ref().unwrap().clone(),
                            omega_inv_variable.as_ref().unwrap(),
                            z.clone(), 
                            z_in_pow_domain_size.clone()
                        )?;

                        tmp
                    };

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

            z_part = z_part.mul(cs, &tmp)?;
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

    let mut virtual_commitment_for_linearization_poly = {

        let mut r = vk.selector_commitments[selector_q_const_index].clone();
        let mut points: Vec<WP> = vec![];
        let mut scalars: Vec<AllocatedNum<E>> = vec![];

        // main gate. Does NOT include public inputs
        {
            // Q_const(x)
            for i in 0..P::STATE_WIDTH {
                // Q_k(X) * K(z)
                // here multiexp may be used
                points.push(vk.selector_commitments[i].clone());
                scalars.push(proof.wire_values_at_z[i].clone());
            }

            // Q_m(X) * A(z) * B(z)
            // add to multiexp as well
            let mut scalar = proof.wire_values_at_z[0].clone();
            scalar = scalar.mul(cs, &proof.wire_values_at_z[1])?;
            points.push(vk.selector_commitments[selector_q_m_index].clone());
            scalars.push(scalar);

            points.push(vk.next_step_selector_commitments[0].clone());
            scalars.push(proof.wire_values_at_z_omega[0].clone());
        }

        // v * [alpha * (a + beta*z + gamma)(b + beta*k_1*z + gamma)()() * z(X) -
        // - \alpha * (a*perm_a(z)*beta + gamma)()()*beta*z(z*omega) * perm_d(X) +
        // + alpha^2 * L_0(z) * z(X) ] + 
        // + v^{P} * u * z(X)
        // and join alpha^2 * L_0(z) and v^{P} * u into the first term containing z(X)

        // [alpha * (a + beta*z + gamma)(b + beta*k_1*z + gamma)()() + alpha^2 * L_0(z)] * z(X)
        let grand_product_part_at_z = {
            let mut scalar: Option<AllocatedNum<E>> = None;

            // permutation part
            for (_i, (wire, non_res)) in proof.wire_values_at_z.iter()
                            .zip(Some(E::Fr::one()).iter().chain(&vk.non_residues)).enumerate() 
            {
                // tmp = non_res * z * beta + wire
                use crate::circuit::Assignment;

                let mut tmp = AllocatedNum::alloc(
                    cs,
                    || {
                        // non_res * z * beta + wire

                        let mut result = *z.get_value().get()?;
                        result.mul_assign(beta.get_value().get()?);
                        result.mul_assign(&non_res);

                        result.add_assign(wire.get_value().get()?);

                        Ok(result)
                    }
                )?;

                // create arithmetic terms

                let z_beta_by_non_res_term = ArithmeticTerm::from_variable_and_coeff(z.get_variable(), *non_res).mul_by_variable(beta.get_variable());
                let wire_term = ArithmeticTerm::from_variable(wire.get_variable());
                let tmp_term = ArithmeticTerm::from_variable(tmp.get_variable());
                let mut term = MainGateTerm::new();
                term.add_assign(z_beta_by_non_res_term);
                term.add_assign(wire_term);
                term.sub_assign(tmp_term);

                cs.allocate_main_gate(term)?;

                // we've enforces tmp value

                // let mut tmp = AllocatedNum::general_equation(cs, &z, &beta, &wire, non_res, &zero, &zero, &one, &zero)?;

                // on first iteration: scalar = tmp + gamma
                // else: scalar = scalar * (tmp + gamma)

                if let Some(existing_scalar) = scalar.take() {
                    tmp = tmp.add(cs, &gamma)?;
                    let s = existing_scalar.mul(cs, &tmp)?;

                    scalar = Some(s);
                } else {
                    let s = tmp.add(cs, &gamma)?;

                    scalar = Some(s);
                } 

                assert!(scalar.is_some());
            }

            let mut scalar = scalar.unwrap();

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
            let mut scalar: Option<AllocatedNum<E>> = None;

            // permutation part
            for (_i, (wire, perm_at_z)) in proof.wire_values_at_z.iter()
                            .zip(&proof.permutation_polynomials_at_z).enumerate() 
            {
                // tmp = perm_at_z * beta + wire
                use crate::circuit::Assignment;

                let mut tmp = AllocatedNum::alloc(
                    cs,
                    || {
                        // perm(z) * beta + wire

                        let mut result = *beta.get_value().get()?;
                        result.mul_assign(perm_at_z.get_value().get()?);

                        result.add_assign(wire.get_value().get()?);

                        Ok(result)
                    }
                )?;

                // create arithmetic terms

                let z_beta_by_non_res_term = ArithmeticTerm::from_variable(perm_at_z.get_variable()).mul_by_variable(beta.get_variable());
                let wire_term = ArithmeticTerm::from_variable(wire.get_variable());
                let tmp_term = ArithmeticTerm::from_variable(tmp.get_variable());
                let mut term = MainGateTerm::new();
                term.add_assign(z_beta_by_non_res_term);
                term.add_assign(wire_term);
                term.sub_assign(tmp_term);

                cs.allocate_main_gate(term)?;

                // tmp is now constrained

                // on first iteration: scalar = tmp + gamma
                // else: scalar = scalar * (tmp + gamma)

                if let Some(existing_scalar) = scalar.take() {
                    tmp = tmp.add(cs, &gamma)?;
                    let s = existing_scalar.mul(cs, &tmp)?;

                    scalar = Some(s);
                } else {
                    let s = tmp.add(cs, &gamma)?;
                    
                    scalar = Some(s);
                }

                assert!(scalar.is_some());
            }

            let mut scalar = scalar.unwrap();

            scalar = scalar.mul(cs, &beta)?.mul(cs, &proof.grand_product_at_z_omega)?.mul(cs, &alpha)?;

            scalar
        };

        {
            // also add to multiexp
            points.push(proof.grand_product_commitment.clone());
            scalars.push(grand_product_part_at_z);
            
            let mut last_permutation = vk.permutation_commitments.last().unwrap().clone();
            points.push(last_permutation.negate(cs, params)?);
            scalars.push(last_permutation_part_at_z);
        }

        let mut tmp = WP::multiexp(cs, &scalars[..], &points[..], None, params, aux_data)?;
        r = r.add(cs, &mut tmp, params)?;

        r = r.mul(cs, &v, None, params, aux_data)?;
        let mut grand_product = proof.grand_product_commitment.clone();
        let mut tmp = grand_product.mul(cs, &grand_product_part_at_z_omega, None, params, aux_data)?;
        r = r.add(cs, &mut tmp, params)?;

        r
    };

    // now check the openings
    // aggregate t(X) from parts

    let mut commitments_aggregation = proof.quotient_poly_commitments[0].clone();

    let mut scalars : Vec<AllocatedNum<E>> = vec![];
    let mut points: Vec<WP> = vec![];

    let mut current = z_in_pow_domain_size.clone();
    for part in proof.quotient_poly_commitments.iter().skip(1) {
        //second multiexp
        points.push(part.clone());
        scalars.push(current.clone());
        current = current.mul(cs, &z_in_pow_domain_size)?;
    }

    let mut multiopening_challenge = v.clone();
    // power of v is contained inside
    commitments_aggregation = commitments_aggregation.add(cs, &mut virtual_commitment_for_linearization_poly, params)?;

    // do the same for wires
    for com in proof.wire_commitments.iter() {
        // add to second multiexp as well
        multiopening_challenge = multiopening_challenge.mul(cs, &v)?; 
        points.push(com.clone());
        scalars.push(multiopening_challenge.clone());
    }

    // and for all permutation polynomials except the last one
    assert_eq!(vk.permutation_commitments.len(), proof.permutation_polynomials_at_z.len() + 1);
    
    let arr_len = vk.permutation_commitments.len();
    for com in vk.permutation_commitments[0..(arr_len - 1)].iter() {
        // v^{1+STATE_WIDTH + STATE_WIDTH - 1}
        // second multiexp
        multiopening_challenge = multiopening_challenge.mul(cs, &v)?; 
        points.push(com.clone());
        scalars.push(multiopening_challenge.clone());
    }
    
    // we skip z(X) at z
    multiopening_challenge = multiopening_challenge.mul(cs, &v)?; 

    // aggregate last wire commitment (that is opened at z*omega)
    // using multiopening challenge and u
    multiopening_challenge = multiopening_challenge.mul(cs, &v)?; 
    let scalar = multiopening_challenge.mul(cs, &u)?;
    // add to second multiexp
    points.push(proof.wire_commitments.last().unwrap().clone());
    scalars.push(scalar);

    // subtract the opening value using one multiplication

    let mut multiopening_challenge_for_values = v.clone();
    let mut aggregated_value = proof.quotient_polynomial_at_z.clone();
    for (i, value_at_z) in Some(proof.linearization_polynomial_at_z.clone()).iter()
            .chain(&proof.wire_values_at_z)
            .chain(&proof.permutation_polynomials_at_z)
            .enumerate() 
    {
        if i != 0 { 
            multiopening_challenge_for_values = multiopening_challenge_for_values.mul(cs, &v)?;
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

    // make equivalent of (f(x) - f(z))
    // also add to second multiexp
    let mut val = E::G1Affine::one();
    val.negate();
    points.push(WP::constant(val, params));
    scalars.push(aggregated_value);

    // next, we need to check that
    // e(proof_for_z + u*proof_for_z_omega, g2^x) = 
    // e(z*proof_for_z + z*omega*u*proof_for_z_omega + (aggregated_commitment - aggregated_opening), g2^1) 
    // however, we are going to compute the pairing itself outside the circuit
    // here we only go to prepare the pairing argumets:
    // arg1 = proof_for_z + u*proof_for_z_omega
    // arg2 = z*proof_for_z + z*omega*u*proof_for_z_omega + (aggregated_commitment - aggregated_opening)

    let mut opening_at_z_proof = proof.opening_at_z_proof.clone();
    let mut opening_at_z_omega_proof = proof.opening_at_z_omega_proof.clone();
    let mut pair_with_x_negated = opening_at_z_omega_proof.mul(cs, &u, None, params, aux_data)?;
    pair_with_x_negated = pair_with_x_negated.add(cs, &mut opening_at_z_proof, params)?;
    
    let pair_with_x = pair_with_x_negated.negate(cs, params)?;

    // to second multiexp
    points.push(proof.opening_at_z_proof.clone());
    scalars.push(z.clone());

    let z_omega_term = if let Some(_required_domain_size) = required_domain_size { 
        let omega = omega_const.unwrap();
        
        let mut z_omega_term = Term::<E>::from_allocated_num(z.clone());
        z_omega_term.scale(&omega);

        z_omega_term
    } else {
        let omega = vk.omega_as_allocated_num.as_ref().unwrap().clone();

        let omega_term = Term::<E>::from_allocated_num(omega);
        let z_term = Term::<E>::from_allocated_num(z.clone());

        let z_omega_term = z_term.mul(cs, &omega_term)?;

        z_omega_term
    };

    let u_as_term = Term::<E>::from_allocated_num(u.clone());
    // z*omega*u
    let z_omega_by_u = z_omega_term.mul(cs, &u_as_term)?.collapse_into_num(cs)?.get_variable();

    points.push(proof.opening_at_z_omega_proof.clone());
    scalars.push(z_omega_by_u);

    let mut tmp = WP::multiexp(cs, &scalars[..], &points[..], None, params, aux_data)?;
    //to second multiexp
    let pair_with_generator = commitments_aggregation.add(cs, &mut tmp, params)?;

    Ok([pair_with_generator, pair_with_x])
}


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
    type MainGate = Width4MainGateWithDNext;

    fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<E>>>, SynthesisError> {
        use crate::plonk::circuit::bigint::range_constraint_gate::TwoBitDecompositionRangecheckCustomGate;

        Ok(
            vec![
                Self::MainGate::default().into_internal(),
                TwoBitDecompositionRangecheckCustomGate::default().into_internal(),
                
            ]
        )
    }

    fn synthesize<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {

        assert!(P::CAN_ACCESS_NEXT_TRACE_STEP);

        let actual_proof = self.proof.replace(None);
        let actual_vk = self.vk.replace(None);

        let proof = ProofGadget::<E, WP>::alloc(cs, actual_proof.unwrap(), self.params, &self.aux_data)?;
        let vk = VerificationKeyGagdet::<E, WP>::alloc(cs, actual_vk.unwrap(), self.params, &self.aux_data)?;

        let _ = aggregate_proof::<E, _, T, P, OldP, AD, WP>(
            cs,
            self.channel_params,
            &proof.input_values,
            &vk,
            &proof,
            &self.aux_data,
            &self.params
        )?;

        Ok(())
    }
}