#[cfg(test)]
mod test {
    use crate::bellman::pairing::{
        Engine,
        CurveAffine,
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

    use crate::bellman::plonk::better_cs::cs::PlonkConstraintSystemParams;
    use crate::bellman::plonk::better_cs::keys::{Proof, VerificationKey};

    use super::super::data_structs::*;
    use super::super::verifying_circuit::*;

    #[derive(Clone)]
    pub struct BenchmarkCircuit<E: Engine>{
        num_steps: usize,
        a: E::Fr,
        b: E::Fr,
        output: E::Fr,
        _marker: std::marker::PhantomData<E>
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

    impl<E: Engine> Circuit<E> for BenchmarkCircuit<E> {
        fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
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
    
    #[test]
    fn test_recursion_for_bn256() 
    {
        type E = bellman::pairing::bn256::Bn256;

        // prepare parameters
        let a = Fr::one();
        let b = Fr::one();
        let num_steps = 10000;

        let fri_params = FriParams {
            initial_degree_plus_one: std::cell::Cell::new(0),
            lde_factor: 16,
            R: 20,
            collapsing_factor: 2,
            final_degree_plus_one: std::cell::Cell::new(1),
        };

        let bn256_rescue_params = BN256Rescue::default();

        let oracle_params = RescueTreeParams {
            values_per_leaf: 1 << fri_params.collapsing_factor,
            rescue_params: &bn256_rescue_params,
            _marker: std::marker::PhantomData::<Fr>,
        };

        let channel_params = RescueChannelParams {
            rescue_params: &bn256_rescue_params,
            _marker: std::marker::PhantomData::<Fr>,
        };

        let res = redshift_template::<E, O, T>(
            a,
            b,
            num_steps,
            &fri_params,
            &oracle_params,
            &channel_params,
        ).expect("should pass");

        let is_valid = res.0;
        let setup_precomp = res.1;
        let proof = res.2;

        assert_eq!(is_valid, true);

        println!("REDSHIFT PROOF DONE");

        let mut container = Vec::<Fr>::new();

        let coset_size = 1 << fri_params.collapsing_factor;
        let top_level_oracle_size = (fri_params.initial_degree_plus_one.get() * fri_params.lde_factor) / coset_size;
        let top_leve_height = log2_floor(top_level_oracle_size);

        setup_precomp.to_stream(&mut container, top_leve_height);
        proof.to_stream(&mut container, fri_params.clone());

        let rescue_params = BN256Rescue::default();
        let oracle_params =  RescueTreeGadgetParams {
            num_elems_per_leaf: coset_size,
            rescue_params: &rescue_params,
            _marker: std::marker::PhantomData::<Fr>,
        };

        let iter = container.into_iter().map(|x| Some(x));

        type OG<'a> = RescueTreeGadget<'a, E, BN256Rescue, BN256RescueSbox>;
        type TG<'a> = RescueChannelGadget<'a, E, BN256Rescue, BN256RescueSbox>;

        let output = fibbonacci(&a, &b, num_steps);

        let redshift_recursion_circuit = RedShiftVerifierCircuit::<E, OG, TG, _>::new(
            &rescue_params,
            oracle_params, 
            fri_params, 
            iter, 
            vec![a, b, output],
        );

        // verify that circuit is satifiable
        let mut test_assembly = TestConstraintSystem::new();
        let now = Instant::now();
        redshift_recursion_circuit.synthesize(&mut test_assembly).expect("should synthesize");
        println!("CIRCUIT synthesize took {}s", now.elapsed().as_secs());
        println!("NUM OF RESCUE PERMUTATIONS in CIRCUIT: {}", RESCUE_PERMUTATIONS_COUNT.load(Ordering::SeqCst));

        if !test_assembly.is_satisfied() 
        {
            println!("UNSATISFIED AT: {}", test_assembly.which_is_unsatisfied().unwrap());
        }
        assert!(test_assembly.is_satisfied(), "some constraints are not satisfied");

        println!("Num of constraints: {}", test_assembly.num_constraints());
    }

    #[test]
    fn redshift_recursion_estimator() 
    {
        type E = bellman::pairing::bn256::Bn256;
        type O<'a> = FriSpecificRescueTree<'a, Fr, BN256Rescue>;
        type T<'a> = RescueChannel<'a, Fr, BN256Rescue>;

        // prepare parameters
        // TODO: log2 and multicore nt_fft fail on small number of steps (<= 10),
        // the reason of failure should be additionally investigated
        let a = Fr::one();
        let b = Fr::one();
        let num_steps = 268435456 / 16;

        let fri_params = FriParams {
            initial_degree_plus_one: std::cell::Cell::new(num_steps),
            lde_factor: 16,
            R: 20,
            collapsing_factor: 2,
            final_degree_plus_one: std::cell::Cell::new(1),
        };
        fri_params.recompute_final_degree(true);

        let bn256_rescue_params = BN256Rescue::default();

        let oracle_params = RescueTreeParams {
            values_per_leaf: 1 << fri_params.collapsing_factor,
            rescue_params: &bn256_rescue_params,
            _marker: std::marker::PhantomData::<Fr>,
        };

        let channel_params = RescueChannelParams {
            rescue_params: &bn256_rescue_params,
            _marker: std::marker::PhantomData::<Fr>,
        };

        let container  = iter::repeat(None);

        let coset_size = 1 << fri_params.collapsing_factor;
        let rescue_params = BN256Rescue::default();
        let oracle_params =  RescueTreeGadgetParams {
            num_elems_per_leaf: coset_size,
            rescue_params: &rescue_params,
            _marker: std::marker::PhantomData::<Fr>,
        };

        type OG<'a> = RescueTreeGadget<'a, E, BN256Rescue, BN256RescueSbox>;
        type TG<'a> = RescueChannelGadget<'a, E, BN256Rescue, BN256RescueSbox>;

        let output = fibbonacci(&a, &b, num_steps);

        let redshift_recursion_circuit = RedShiftVerifierCircuit::<E, OG, TG, _>::new(
            &rescue_params,
            oracle_params, 
            fri_params, 
            container, 
            vec![a, b, output],
        );

        // verify that circuit is satifiable
        let mut test_assembly = TestConstraintSystem::new();
        let now = Instant::now();
        redshift_recursion_circuit.synthesize(&mut test_assembly).expect("should synthesize");
        println!("CIRCUIT synthesize took {}s", now.elapsed().as_secs());
        println!("Num of constraints: {}", test_assembly.num_constraints());
        println!("NUM OF RESCUE PERMUTATIONS in CIRCUIT: {}", RESCUE_PERMUTATIONS_COUNT.load(Ordering::SeqCst));

        if !test_assembly.is_satisfied() 
        {
            println!("UNSATISFIED AT: {}", test_assembly.which_is_unsatisfied().unwrap());
        }
        assert!(test_assembly.is_satisfied(), "some constraints are not satisfied");

        println!("Num of constraints: {}", test_assembly.num_constraints());
    }

}