// new test paradigm: using better_cs for witness generation and better_better_cs for actual constraint system

#[cfg(test)]
mod test {
    use crate::bellman::pairing::{
        Engine,
        CurveAffine,
        CurveProjective
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
    };

    use crate::bellman::plonk::better_cs::keys::{Proof, VerificationKey};
    use crate::bellman::plonk::better_cs::cs::PlonkConstraintSystemParams as OldCSParams;
    use crate::bellman::plonk::better_cs::cs::Circuit as OldCircuit;
    use crate::bellman::plonk::better_cs::cs::ConstraintSystem as OldConstraintSystem;
    use crate::bellman::plonk::better_cs::cs::PlonkCsWidth4WithNextStepParams as OldActualParams;

    use super::super::data_structs::*;
    use super::super::verifying_circuit::*;
    

    #[derive(Clone)]
    pub struct BenchmarkCircuit<E: Engine>{
        num_steps: usize,
        a: E::Fr,
        b: E::Fr,
        output: E::Fr,

        _engine_marker: std::marker::PhantomData<E>,
    }

    pub fn fibbonacci<F: Field>(a: &F, b: &F, num_steps: usize) -> F {

        let mut a = a.clone();
        let mut b = b.clone();

        for _ in 0..num_steps {
            b.add_assign(&a);
            std::mem::swap(&mut a, &mut b);
        }

        a
    }

    impl<E: Engine> OldCircuit<E, OldActualParams> for BenchmarkCircuit<E> {
        fn synthesize<CS: OldConstraintSystem<E, OldActualParams>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
            // yeah, fibonacci...

            let one = E::Fr::one();
            let mut negative_one = one;
            negative_one.negate();
            
            let mut a = cs.alloc_input(|| {
                Ok(self.a.clone())
            })?;

            let mut b = cs.alloc_input(|| {
                Ok(self.b.clone())
            })?;

            let mut a_value = self.a.clone();
            let mut b_value = self.b.clone();

            for _ in 0..self.num_steps {

                b_value.add_assign(&a_value);
                
                let temp = cs.alloc(|| {
                    Ok(b_value.clone())
                })?;

                type StateVariables = [Variable; 4];
    type ThisTraceStepCoefficients = [E::Fr; 6];
    type NextTraceStepCoefficients = [E::Fr; 1];

                cs.new_gate(&self, [a, b, cs.get_dummy_variable(), temp]
        variables: P::StateVariables, 
        this_step_coeffs: P::ThisTraceStepCoefficients,
        next_step_coeffs: P::NextTraceStepCoefficients
    ) -> Result<(), SynthesisError>;

                cs.enforce_zero_3((a, b, temp), (one, one, negative_one))?;
                std::mem::swap(&mut a_value, &mut b_value);

                b = a;
                a = temp;
            }

            let output = cs.alloc_input(|| {
                Ok(self.output.clone())
            })?;

            cs.enforce_zero_2((a, output), (one, negative_one))?;

            Ok(())
        }
    }
}

//     pub fn recursion_test() 
//     {

//     }
    
//     #[test]
//     fn test_recursion_for_bn256() 
//     {
//         type E = bellman::pairing::bn256::Bn256;

//         // prepare parameters
//         let a = Fr::one();


//         let b = Fr::one();
//         let num_steps = 10000;

//         let fri_params = FriParams {
//             initial_degree_plus_one: std::cell::Cell::new(0),
//             lde_factor: 16,
//             R: 20,
//             collapsing_factor: 2,
//             final_degree_plus_one: std::cell::Cell::new(1),
//         };

//         let bn256_rescue_params = BN256Rescue::default();

//         let oracle_params = RescueTreeParams {
//             values_per_leaf: 1 << fri_params.collapsing_factor,
//             rescue_params: &bn256_rescue_params,
//             _marker: std::marker::PhantomData::<Fr>,
//         };

//         let channel_params = RescueChannelParams {
//             rescue_params: &bn256_rescue_params,
//             _marker: std::marker::PhantomData::<Fr>,
//         };

//         let res = redshift_template::<E, O, T>(
//             a,
//             b,
//             num_steps,
//             &fri_params,
//             &oracle_params,
//             &channel_params,
//         ).expect("should pass");

//         let is_valid = res.0;
//         let setup_precomp = res.1;
//         let proof = res.2;

//         assert_eq!(is_valid, true);

//         println!("REDSHIFT PROOF DONE");

//         let mut container = Vec::<Fr>::new();

//         let coset_size = 1 << fri_params.collapsing_factor;
//         let top_level_oracle_size = (fri_params.initial_degree_plus_one.get() * fri_params.lde_factor) / coset_size;
//         let top_leve_height = log2_floor(top_level_oracle_size);

//         setup_precomp.to_stream(&mut container, top_leve_height);
//         proof.to_stream(&mut container, fri_params.clone());

//         let rescue_params = BN256Rescue::default();
//         let oracle_params =  RescueTreeGadgetParams {
//             num_elems_per_leaf: coset_size,
//             rescue_params: &rescue_params,
//             _marker: std::marker::PhantomData::<Fr>,
//         };

//         let iter = container.into_iter().map(|x| Some(x));

//         type OG<'a> = RescueTreeGadget<'a, E, BN256Rescue, BN256RescueSbox>;
//         type TG<'a> = RescueChannelGadget<'a, E, BN256Rescue, BN256RescueSbox>;

//         let output = fibbonacci(&a, &b, num_steps);

//         let redshift_recursion_circuit = RedShiftVerifierCircuit::<E, OG, TG, _>::new(
//             &rescue_params,
//             oracle_params, 
//             fri_params, 
//             iter, 
//             vec![a, b, output],
//         );

//         // verify that circuit is satifiable
//         let mut test_assembly = TestConstraintSystem::new();
//         let now = Instant::now();
//         redshift_recursion_circuit.synthesize(&mut test_assembly).expect("should synthesize");
//         println!("CIRCUIT synthesize took {}s", now.elapsed().as_secs());
//         println!("NUM OF RESCUE PERMUTATIONS in CIRCUIT: {}", RESCUE_PERMUTATIONS_COUNT.load(Ordering::SeqCst));

//         if !test_assembly.is_satisfied() 
//         {
//             println!("UNSATISFIED AT: {}", test_assembly.which_is_unsatisfied().unwrap());
//         }
//         assert!(test_assembly.is_satisfied(), "some constraints are not satisfied");

//         println!("Num of constraints: {}", test_assembly.num_constraints());
//     }

//     #[test]
//     fn redshift_recursion_estimator() 
//     {
//         type E = bellman::pairing::bn256::Bn256;
//         type O<'a> = FriSpecificRescueTree<'a, Fr, BN256Rescue>;
//         type T<'a> = RescueChannel<'a, Fr, BN256Rescue>;

//         // prepare parameters
//         // TODO: log2 and multicore nt_fft fail on small number of steps (<= 10),
//         // the reason of failure should be additionally investigated
//         let a = Fr::one();
//         let b = Fr::one();
//         let num_steps = 268435456 / 16;

//         let fri_params = FriParams {
//             initial_degree_plus_one: std::cell::Cell::new(num_steps),
//             lde_factor: 16,
//             R: 20,
//             collapsing_factor: 2,
//             final_degree_plus_one: std::cell::Cell::new(1),
//         };
//         fri_params.recompute_final_degree(true);

//         let bn256_rescue_params = BN256Rescue::default();

//         let oracle_params = RescueTreeParams {
//             values_per_leaf: 1 << fri_params.collapsing_factor,
//             rescue_params: &bn256_rescue_params,
//             _marker: std::marker::PhantomData::<Fr>,
//         };

//         let channel_params = RescueChannelParams {
//             rescue_params: &bn256_rescue_params,
//             _marker: std::marker::PhantomData::<Fr>,
//         };

//         let container  = iter::repeat(None);

//         let coset_size = 1 << fri_params.collapsing_factor;
//         let rescue_params = BN256Rescue::default();
//         let oracle_params =  RescueTreeGadgetParams {
//             num_elems_per_leaf: coset_size,
//             rescue_params: &rescue_params,
//             _marker: std::marker::PhantomData::<Fr>,
//         };

//         type OG<'a> = RescueTreeGadget<'a, E, BN256Rescue, BN256RescueSbox>;
//         type TG<'a> = RescueChannelGadget<'a, E, BN256Rescue, BN256RescueSbox>;

//         let output = fibbonacci(&a, &b, num_steps);

//         let redshift_recursion_circuit = RedShiftVerifierCircuit::<E, OG, TG, _>::new(
//             &rescue_params,
//             oracle_params, 
//             fri_params, 
//             container, 
//             vec![a, b, output],
//         );

//         // verify that circuit is satifiable
//         let mut test_assembly = TestConstraintSystem::new();
//         let now = Instant::now();
//         redshift_recursion_circuit.synthesize(&mut test_assembly).expect("should synthesize");
//         println!("CIRCUIT synthesize took {}s", now.elapsed().as_secs());
//         println!("Num of constraints: {}", test_assembly.num_constraints());
//         println!("NUM OF RESCUE PERMUTATIONS in CIRCUIT: {}", RESCUE_PERMUTATIONS_COUNT.load(Ordering::SeqCst));

//         if !test_assembly.is_satisfied() 
//         {
//             println!("UNSATISFIED AT: {}", test_assembly.which_is_unsatisfied().unwrap());
//         }
//         assert!(test_assembly.is_satisfied(), "some constraints are not satisfied");

//         println!("Num of constraints: {}", test_assembly.num_constraints());
//     }

// }

// pub fn redshift_template<E: Engine, I: Oracle<E::Fr>, T: Channel<E::Fr, Input = I::Commitment>>(
//     a: E::Fr,
//     b: E::Fr,
//     num_steps: usize,
//     fri_params: &FriParams,
//     oracle_params: &I::Params,
//     channel_params: &T::Params,
// ) -> Result<(bool, RedshiftSetupPrecomputation<E::Fr, I>, RedshiftProof<E::Fr, I>), SynthesisError>
// {

//     let output = fibbonacci(&a, &b, num_steps);
    
//     let circuit = BenchmarkCircuit::<E> {
//         num_steps,
//         a,
//         b,
//         output,
//         _marker: std::marker::PhantomData::<E>
//     };

//     // verify that circuit is satifiable
//     let mut test_assembly = TestAssembly::new();
//     circuit.synthesize(&mut test_assembly)?;
//     assert!(test_assembly.is_satisfied(false), "some constraints are not satisfied");
    
//     // TODO: setup is never actually used! get rid of this function!
    
//     let now = Instant::now();
//     let (_setup, setup_precomp) = setup_with_precomputations::<E, BenchmarkCircuit<E>, I, T>(
//         &circuit,
//         fri_params,
//         oracle_params,
//         channel_params,
//     )?;
    
//     println!("SETUP PRECOMPUTATION took {}s", now.elapsed().as_secs());

//     let now = Instant::now();
//     let proof = prove_with_setup_precomputed::<E, BenchmarkCircuit<E>, I, T> (
//         &circuit,
//         &setup_precomp, 
//         fri_params,
//         oracle_params,
//         channel_params, 
//     )?;
//     println!("PROOF took {}s", now.elapsed().as_secs());
//     println!("NUM OF RESCUE PERMUTATIONS in PROVER: {}", NUM_RESCUE_PERMUTATIONS_COUNTER.load(Ordering::SeqCst));

//     NUM_RESCUE_PERMUTATIONS_COUNTER.store(0, Ordering::SeqCst);
//     let now = Instant::now();
//     let is_valid = verify_proof::<E, I, T>(
//         proof.clone(),
//         &[a, b, output],
//         &setup_precomp,
//         fri_params,
//         oracle_params,
//         channel_params,
//     )?;
    
//     println!("PROOF VERIFICATION took {}s", now.elapsed().as_secs());
//     println!("NUM OF RESCUE PERMUTATIONS in VERIFIER: {}", NUM_RESCUE_PERMUTATIONS_COUNTER.load(Ordering::SeqCst));

//     Ok((is_valid, setup_precomp, proof))
// }