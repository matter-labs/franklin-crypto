use crate::bellman::pairing::{
    Engine,
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


use crate::plonk::circuit::bigint::*;
use crate::plonk::circuit::curve::*;
use crate::plonk::circuit::boolean::*;
use crate::plonk::circuit::allocated_num::*;

use channel;
use helper_functions;
use data_structs;


pub struct PlonkVerifierCircuit<E, T> 
where E: Engine, T: ChannelGadget<E>>
{
    _engine_marker : std::marker::PhantomData<E>,
    _channel_marker : std::marker::PhantomData<T>,
    channel_params: T::Params,
    
    public_inputs : Vec<E::Fr>,
    supposed_outputs: Vec<E::Fr>
}


impl<E, T> RedShiftVerifierCircuit<E, T> 
where E: Engine, T: ChannelGadget<E>
{
    pub fn new(channel_params: T::Params, public_inputs: Vec<E::Fr>, supposed_output: Vec<E::Fr>) -> Self {

        RedShiftVerifierCircuit {
            
            _engine_marker : std::marker::PhantomData::<E>,
            _oracle_marker : std::marker::PhantomData::<O>,
            _channel_marker : std::marker::PhantomData::<T>,

            channel_params,
            oracle_params,
            fri_params,
            input_stream: stream,
            public_inputs : public,
        }
    }
}


impl<E, T> Circuit<E> for PlonkVerifierCircuit<E, T> 
where 
    E: Engine, T: ChannelGadget<E>
 {

    fn synthesize<CS: ConstraintSystem<E>>(
        mut self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {

        let mut channel = T::new(self.channel_params);
        
        let precomputation = RedshiftSetupPrecomputation::<E,O>::from_stream(
            cs.namespace(|| "initialize precomputation"), 
            &mut self.input_stream, 
            top_level_height,
        )?;

        let proof = RedshiftProof::<E, O>::from_stream(
            cs.namespace(|| "initialize proof"),
            &mut self.input_stream, 
            self.fri_params.clone(),
        )?;

        //self.input_stream.next().unwrap();

        let a_com = find_by_label("a", &proof.commitments)?;
        channel.consume(a_com.clone(), unnamed(cs))?;
   
        let b_com = find_by_label("b", &proof.commitments)?;
        channel.consume(b_com.clone(), unnamed(cs))?;
        
        let c_com = find_by_label("c", &proof.commitments)?;
        channel.consume(c_com.clone(), unnamed(cs))?;

        let beta = channel.produce_challenge(unnamed(cs))?;
        let gamma = channel.produce_challenge(unnamed(cs))?;

        let z_1_com = find_by_label("z_1", &proof.commitments)?;
        channel.consume(z_1_com.clone(), unnamed(cs))?;
        
        let z_2_com = find_by_label("z_2", &proof.commitments)?; 
        channel.consume(z_2_com.clone(), unnamed(cs))?;

        let alpha = channel.produce_challenge(unnamed(cs))?;

        let t_low_com = find_by_label("t_low", &proof.commitments)?;
        channel.consume(t_low_com.clone(), unnamed(cs))?;
    
        let t_mid_com = find_by_label("t_mid", &proof.commitments)?;
        channel.consume(t_mid_com.clone(), unnamed(cs))?;

        let t_high_com = find_by_label("t_high", &proof.commitments)?;
        channel.consume(t_high_com.clone(), unnamed(cs))?;

        // TODO: we should be very carefule in choosing z!
        // at least it should be nonzero, but I suppose that it also should not been contained in our domain
        // add additiona constraints in order to ensure this!

        let z = channel.produce_challenge(unnamed(cs))?;

        // check the final equation at single point z!

        let a_at_z = find_by_label("a", &proof.opening_values)?;
        let b_at_z = find_by_label("b", &proof.opening_values)?;
        let c_at_z = find_by_label("c", &proof.opening_values)?;
        let c_shifted_at_z = find_by_label("c_shifted", &proof.opening_values)?;

        let q_l_at_z = find_by_label("q_l", &proof.opening_values)?;
        let q_r_at_z = find_by_label("q_r", &proof.opening_values)?;
        let q_o_at_z = find_by_label("q_o", &proof.opening_values)?;
        let q_m_at_z = find_by_label("q_m", &proof.opening_values)?;
        let q_c_at_z = find_by_label("q_c", &proof.opening_values)?;
        let q_add_sel_at_z = find_by_label("q_add_sel", &proof.opening_values)?;

        let s_id_at_z = find_by_label("s_id", &proof.opening_values)?;
        let sigma_1_at_z = find_by_label("sigma_1", &proof.opening_values)?;
        let sigma_2_at_z = find_by_label("sigma_2", &proof.opening_values)?;
        let sigma_3_at_z = find_by_label("sigma_3", &proof.opening_values)?;

        let z_1_at_z = find_by_label("z_1",  &proof.opening_values)?;
        let z_2_at_z = find_by_label("z_2", &proof.opening_values)?;

        let z_1_shifted_at_z = find_by_label("z_1_shifted", &proof.opening_values)?;
        let z_2_shifted_at_z = find_by_label("z_2_shifted", &proof.opening_values)?;

        let t_low_at_z = find_by_label("t_low", &proof.opening_values)?;
        let t_mid_at_z = find_by_label("t_mid", &proof.opening_values)?;
        let t_high_at_z = find_by_label("t_high", &proof.opening_values)?;

        // compute the righthandsize term: T_low(z) + T_mid(z) * z^n + T_high(z) * z^(2n)

        let decomposed_domain_size = u64_into_boolean_vec_le(unnamed(cs), Some(domain_size as u64))?;
        let z_in_pow_domain_size = AllocatedNum::pow(unnamed(cs), &z, decomposed_domain_size.iter())?;

        let mut rhs : Num<E> = t_low_at_z.clone().into();
        let mid_term = t_mid_at_z.mul(unnamed(cs), &z_in_pow_domain_size)?;
        rhs.mut_add_number_with_coeff(&mid_term, E::Fr::one());

        let z_in_pow_2_domain_size = z_in_pow_domain_size.square(unnamed(cs))?;
        let highest_term = t_high_at_z.mul(unnamed(cs), &z_in_pow_2_domain_size)?;
        rhs.mut_add_number_with_coeff(&highest_term, E::Fr::one());

        // begin computing the lhs term

        // prepare public inputs 
        // TODO: check if I have taken the right domain (or increase by LDE factor?)

        let domain = Domain::<E::Fr>::new_for_size(domain_size as u64).expect("domain of this size should exist");
        let omega = domain.generator;
        let omega_inv = omega.inverse().expect("must exist");

        let l_0_at_z = evaluate_lagrange_poly(unnamed(cs), domain_size, 0, &omega_inv, z.clone(), z_in_pow_domain_size.clone())?;
        let mut PI_at_z = Num::zero();

        for (i, val) in self.public_inputs.into_iter().enumerate() {
            let input = AllocatedNum::alloc_input(cs.namespace(|| "allocating public input"), || Ok(val))?;
            let langrange_coef = match i {
                0 => l_0_at_z.clone(),
                _ => evaluate_lagrange_poly(unnamed(cs), domain_size, i, &omega_inv, z.clone(), z_in_pow_domain_size.clone())?,
            };
            let temp = input.mul(unnamed(cs),&langrange_coef)?;
            PI_at_z.sub_assign(&temp.into());
        }

        let mut inverse_vanishing_at_z = evaluate_inverse_vanishing_poly(unnamed(cs), domain_size, &omega_inv, z.clone(), z_in_pow_domain_size.clone())?;
        let l_n_minus_one_at_z = evaluate_lagrange_poly(unnamed(cs), domain_size, n-1, &omega_inv, z.clone(), z_in_pow_domain_size.clone())?;

        // (q_l a + q_r b + q_o c + q_m a * b + q_c + q_add_sel q_next) * inv_vanishing_poly

        let term1 = {
            let mut res : Num<E> = q_c_at_z.clone().into();

            res += q_l_at_z.mul(unnamed(cs), &a_at_z)?;
            res += q_r_at_z.mul(unnamed(cs), &b_at_z)?;  
            res += q_o_at_z.mul(unnamed(cs), &c_at_z)?;
            res += q_m_at_z.mul(unnamed(cs), &a_at_z)?.mul(unnamed(cs), &b_at_z)?;
        
            // add additional shifted selector
            res += q_add_sel_at_z.mul(unnamed(cs), &c_shifted_at_z)?;

            // add public inputs
            res += &PI_at_z;

            let res = Num::mul(unnamed(cs), &res, &inverse_vanishing_at_z.clone().into())?;
            res
        };

        // from now on: permutation check

        let n_fe = E::Fr::from_str(&n.to_string()).expect("must be valid field element");
        let mut two_n_fe = n_fe;
        two_n_fe.double();

        // TODO: think how to organize types to make it more readable
        // macros (usual one) would work
        // and do something to avoid clonings

        let term2 = {
            
            let mut res : Num<E> = z_1_at_z.clone().into();

            let mut tmp : Num<E> = s_id_at_z.mul(unnamed(cs), &beta)?.into();
            tmp += a_at_z.clone();
            tmp += gamma.clone();
            res = Num::mul(unnamed(cs), &res, &tmp)?.into();
            
            tmp = s_id_at_z.clone().into();
            tmp.add_assign(&Num::from_constant(&n_fe, cs));
            tmp = Num::mul(unnamed(cs), &tmp, &beta.clone().into())?.into();
            tmp += b_at_z.clone();
            tmp += gamma.clone();
            res = Num::mul(unnamed(cs), &res, &tmp)?.into();

            tmp = s_id_at_z.clone().into();
            tmp.add_assign(&Num::from_constant(&two_n_fe, cs));
            tmp = Num::mul(unnamed(cs), &tmp, &beta.clone().into())?.into();
            tmp += c_at_z.clone();
            tmp += gamma.clone();
            res = Num::mul(unnamed(cs), &res, &tmp)?.into();

            res -= z_1_shifted_at_z.clone();

            inverse_vanishing_at_z = inverse_vanishing_at_z.mul(unnamed(cs), &alpha)?;
            Num::mul(unnamed(cs), &res, &inverse_vanishing_at_z.clone().into())?
        };

        let term3 = {
            let mut res : Num<E> = z_2_at_z.clone().into();

            let mut tmp : Num<E> = sigma_1_at_z.mul(unnamed(cs), &beta)?.into();
            tmp += a_at_z.clone();
            tmp += gamma.clone();
            res = Num::mul(unnamed(cs), &res, &tmp)?.into();

            tmp = sigma_2_at_z.mul(unnamed(cs), &beta)?.into();
            tmp += b_at_z.clone();
            tmp += gamma.clone();
            res = Num::mul(unnamed(cs), &res, &tmp)?.into();

            tmp = sigma_3_at_z.mul(unnamed(cs), &beta)?.into();
            tmp += c_at_z.clone();
            tmp += gamma.clone();
            res = Num::mul(unnamed(cs), &res, &tmp)?.into();
           
            res -= z_2_shifted_at_z.clone();

            inverse_vanishing_at_z = inverse_vanishing_at_z.mul(unnamed(cs), &alpha)?;
            Num::mul(unnamed(cs), &res, &inverse_vanishing_at_z.clone().into())?
        };

        let term4 = {
            let mut res : Num<E> = z_1_shifted_at_z.clone().into();
            res -= z_2_shifted_at_z.clone();
            res = Num::mul(unnamed(cs), &res, &l_n_minus_one_at_z.clone().into())?.into();
            
            inverse_vanishing_at_z = inverse_vanishing_at_z.mul(unnamed(cs), &alpha)?;
            Num::mul(unnamed(cs), &res, &inverse_vanishing_at_z.clone().into())?
        };

        let term5 = {
            let mut res : Num<E> = z_1_at_z.clone().into();
            res -= z_2_at_z.clone();
            res = Num::mul(unnamed(cs), &res, &l_0_at_z.clone().into())?.into();

            inverse_vanishing_at_z = inverse_vanishing_at_z.mul(unnamed(cs), &alpha)?;
            Num::mul(unnamed(cs), &res, &inverse_vanishing_at_z.clone().into())?
        };

        let mut lhs = Num::zero();
        lhs += term1;
        lhs += term2;
        lhs += term3;
        lhs += term4;
        lhs += term5;
        
        // compare!
        let unit = Num::from_constant(&E::Fr::one(), cs);
        Num::enforce(
            cs.namespace(|| "Plonk equality check at point z"), 
            &lhs,
            &unit,
            &rhs,
        );

        // Fri validation starts from here
        let aggregation_challenge = channel.produce_challenge(unnamed(cs))?;

        let mut upper_layer_commitments = proof.commitments;
        let opening_values = proof.opening_values;
        upper_layer_commitments.extend(precomputation.data.iter().map(|item| {
            Labeled::new(item.label, item.data.commitment.clone())
        }));
      
        let fri_challenges = get_fri_challenges::<E, O, T, _>(cs, &proof.fri_proof, &mut channel)?;
       
        let natural_first_element_indexes = (0..self.fri_params.R).map(|_| {
            let packed = channel.produce_challenge(unnamed(cs))?;
            let mut bits = packed.into_bits_le(unnamed(cs))?;
            bits.truncate(64);

            
            Ok(bits)
        }).collect::<Result<_, SynthesisError>>()?;

        let upper_layer_combiner = ReshiftCombiner::<E, O> {
            setup_precomp: precomputation,
            opening_values,
            z,
            aggr_challenge: aggregation_challenge,
            omega,
        };

        let fri_verifier_gadget = FriVerifierGadget::<E, O, _> {
            collapsing_factor : self.fri_params.collapsing_factor as usize,
            //number of iterations done during FRI query phase
            num_query_rounds : self.fri_params.R,
            initial_degree_plus_one : self.fri_params.initial_degree_plus_one.get(),
            lde_factor: self.fri_params.lde_factor,
            //the degree of the resulting polynomial at the bottom level of FRI
            final_degree_plus_one : self.fri_params.final_degree_plus_one.get(),
            upper_layer_combiner,

            _engine_marker : std::marker::PhantomData::<E>,
            _oracle_marker : std::marker::PhantomData::<O>,
        };
       
        let is_fri_valid = fri_verifier_gadget.verify_proof(
            cs.namespace(|| "FRI verification"),
            &self.oracle_params,
            &upper_layer_commitments,
            &proof.fri_proof.commitments,
            &proof.fri_proof.final_coefficients,
            &fri_challenges,
            natural_first_element_indexes,
            &proof.fri_proof.fri_round_queries,
        )?;

        Boolean::enforce_equal(cs.namespace(|| "check output bit"), &is_fri_valid, &Boolean::constant(true))?;

        Ok(())
    }
}


pub fn verify<E: Engine, P: PlonkConstraintSystemParams<E>, T: Transcript<E::Fr>>(
    proof: &Proof<E, P>,
    verification_key: &VerificationKey<E, P>,
) -> Result<bool, SynthesisError> {
    use crate::pairing::CurveAffine;
    use crate::pairing::CurveProjective;

    assert!(P::CAN_ACCESS_NEXT_TRACE_STEP);

    let mut transcript = T::new();

    if proof.n != verification_key.n {
        return Err(SynthesisError::MalformedVerifyingKey);
    }

    if proof.num_inputs != verification_key.num_inputs {
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

    let non_residues = make_non_residues::<E::Fr>(P::STATE_WIDTH - 1, &domain);

    // Commit public inputs
    for inp in proof.input_values.iter() {
        transcript.commit_field_element(&inp);
    }

    // Commit wire values
    for w in proof.wire_commitments.iter() {
        commit_point_as_xy::<E, _>(&mut transcript, &w);
    }

    let beta = transcript.get_challenge();
    let gamma = transcript.get_challenge();

    // commit grand product
    commit_point_as_xy::<E, _>(&mut transcript, &proof.grand_product_commitment);

    let alpha = transcript.get_challenge();

    // Commit parts of the quotient polynomial
    for w in proof.quotient_poly_commitments.iter() {
        commit_point_as_xy::<E, _>(&mut transcript, &w);
    }

    let z = transcript.get_challenge();
    let mut z_by_omega = z;
    z_by_omega.mul_assign(&domain.generator);

    // commit every claimed value

    for el in proof.wire_values_at_z.iter() {
        transcript.commit_field_element(el);
    }

    for el in proof.wire_values_at_z_omega.iter() {
        transcript.commit_field_element(el);
    }

    for el in proof.permutation_polynomials_at_z.iter() {
        transcript.commit_field_element(el);
    }

    transcript.commit_field_element(&proof.quotient_polynomial_at_z);

    transcript.commit_field_element(&proof.linearization_polynomial_at_z);


    // do the actual check for relationship at z

    {
        let mut lhs = proof.quotient_polynomial_at_z;
        let vanishing_at_z = evaluate_vanishing_for_size(&z, required_domain_size as u64);
        lhs.mul_assign(&vanishing_at_z);

        let mut quotient_linearization_challenge = E::Fr::one();

        let mut rhs = proof.linearization_polynomial_at_z;

        // add public inputs
        {
            for (idx, input) in proof.input_values.iter().enumerate() {
                let mut tmp = evaluate_lagrange_poly_at_point(idx, &domain, z)?;
                tmp.mul_assign(&input);

                rhs.add_assign(&tmp);
            }
        }

        quotient_linearization_challenge.mul_assign(&alpha);

        // - \alpha (a + perm(z) * beta + gamma)*()*(d + gamma) & z(z*omega)

        let mut z_part = proof.grand_product_at_z_omega;

        for (w, p) in proof.wire_values_at_z.iter().zip(proof.permutation_polynomials_at_z.iter()) {
            let mut tmp = *p;
            tmp.mul_assign(&beta);
            tmp.add_assign(&gamma);
            tmp.add_assign(&w);
            
            z_part.mul_assign(&tmp);
        }   

        // last poly value and gamma
        let mut tmp = gamma;
        tmp.add_assign(&proof.wire_values_at_z.iter().rev().next().unwrap());

        z_part.mul_assign(&tmp);
        z_part.mul_assign(&quotient_linearization_challenge);

        rhs.sub_assign(&z_part);

        quotient_linearization_challenge.mul_assign(&alpha);
        
        // - L_0(z) * \alpha^2

        let mut l_0_at_z = evaluate_l0_at_point(required_domain_size as u64, z)?;
        l_0_at_z.mul_assign(&quotient_linearization_challenge);

        rhs.sub_assign(&l_0_at_z);

        if lhs != rhs {
            return Ok(false);
        }
    }

    let v = transcript.get_challenge();

    commit_point_as_xy::<E, _>(&mut transcript, &proof.opening_at_z_proof);

    commit_point_as_xy::<E, _>(&mut transcript, &proof.opening_at_z_omega_proof);

    let u = transcript.get_challenge();

    let z_in_domain_size = z.pow(&[required_domain_size as u64]);

    // first let's reconstruct the linearization polynomial from
    // honomorphic commitments, and simultaneously add (through the separation scalar "u")
    // part for opening of z(X) at z*omega

    // calculate the power to add z(X) commitment that is opened at x*omega
    // it's r(X) + witness + all permutations + 1
    let v_power_for_standalone_z_x_opening = 1 + 1 + P::STATE_WIDTH + (P::STATE_WIDTH-1);

    let virtual_commitment_for_linearization_poly = {
        let mut r = E::G1::zero();

        // main gate. Does NOT include public inputs
        {
            // Q_const(x)
            r.add_assign_mixed(&verification_key.selector_commitments[selector_q_const_index]);

            for i in 0..P::STATE_WIDTH {
                // Q_k(X) * K(z)
                r.add_assign(&verification_key.selector_commitments[i].mul(proof.wire_values_at_z[i].into_repr()));
            }

            // Q_m(X) * A(z) * B(z)
            let mut scalar = proof.wire_values_at_z[0];
            scalar.mul_assign(&proof.wire_values_at_z[1]);
            r.add_assign(&verification_key.selector_commitments[selector_q_m_index].mul(scalar.into_repr()));

            // Q_d_next(X) * D(z*omega)
            r.add_assign(&verification_key.next_step_selector_commitments[0].mul(proof.wire_values_at_z_omega[0].into_repr()));
        }

        // v * [alpha * (a + beta*z + gamma)(b + beta*k_1*z + gamma)()() * z(X) -
        // - \alpha * (a*perm_a(z)*beta + gamma)()()*beta*z(z*omega) * perm_d(X) +
        // + alpha^2 * L_0(z) * z(X) ] + 
        // + v^{P} * u * z(X)
        // and join alpha^2 * L_0(z) and v^{P} * u into the first term containing z(X)

        // [alpha * (a + beta*z + gamma)(b + beta*k_1*z + gamma)()() + alpha^2 * L_0(z)] * z(X)
        let grand_product_part_at_z = {
            let mut scalar = E::Fr::one();

            // permutation part
            for (wire, non_res) in proof.wire_values_at_z.iter()
                            .zip(Some(E::Fr::one()).iter().chain(&non_residues)) 
            {
                let mut tmp = z;
                tmp.mul_assign(&non_res);
                tmp.mul_assign(&beta);
                tmp.add_assign(&wire);
                tmp.add_assign(&gamma);

                scalar.mul_assign(&tmp);
            }

            scalar.mul_assign(&alpha);

            let l_0_at_z = evaluate_l0_at_point(required_domain_size as u64, z)?;

            // + L_0(z) * alpha^2
            let mut tmp = l_0_at_z;
            tmp.mul_assign(&alpha);
            tmp.mul_assign(&alpha);
            scalar.add_assign(&tmp);

            // * v
            // scalar.mul_assign(&v);

            scalar
        };

        // v^{P} * u * z(X)
        let grand_product_part_at_z_omega = {
            // + v^{P} * u
            let mut tmp = v.pow(&[v_power_for_standalone_z_x_opening as u64]);
            tmp.mul_assign(&u);

            tmp
        };

        // \alpha * (a*perm_a(z)*beta + gamma)()()*beta*z(z*omega) * perm_d(X)
        let last_permutation_part_at_z = {
            let mut scalar = E::Fr::one();

            // permutation part
            for (wire, perm_at_z) in proof.wire_values_at_z.iter()
                            .zip(&proof.permutation_polynomials_at_z) 
            {
                let mut tmp = beta;
                tmp.mul_assign(&perm_at_z);
                tmp.add_assign(&wire);
                tmp.add_assign(&gamma);

                scalar.mul_assign(&tmp);
            }

            scalar.mul_assign(&beta);
            scalar.mul_assign(&proof.grand_product_at_z_omega);
            scalar.mul_assign(&alpha);
            // scalar.mul_assign(&v);

            scalar
        };

        {
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