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
        ScalarEngine,
    };

    use crate::bellman::{
        SynthesisError,
    };

    use crate::bellman::plonk::better_better_cs::cs::{
        Variable, 
        ConstraintSystem,
    };

    use crate::bellman::plonk::better_cs::keys::{Proof, VerificationKey, SetupPolynomialsPrecomputations, SetupPolynomials};
    use crate::bellman::plonk::better_cs::cs::PlonkConstraintSystemParams as OldCSParams;
    use crate::bellman::plonk::better_cs::cs::Circuit as OldCircuit;
    use crate::bellman::plonk::better_cs::cs::ConstraintSystem as OldConstraintSystem;
    use crate::bellman::plonk::better_cs::cs::PlonkCsWidth4WithNextStepParams as OldActualParams;

    use crate::bellman::plonk::better_cs::generator::GeneratorAssembly as OldAssembly;
    use crate::bellman::plonk::better_cs::generator::GeneratorAssembly4WithNextStep as OldActualAssembly;
    use crate::bellman::plonk::better_cs::prover::ProverAssembly as OldProver;
    use crate::bellman::plonk::better_cs::prover::ProverAssembly4WithNextStep as OldActualProver;
    use crate::bellman::plonk::better_cs::verifier::verify;
    use crate::bellman::worker::*;
    use crate::bellman::plonk::commitments::transcript::*;
    use crate::bellman::kate_commitment::*;
    use crate::bellman::plonk::fft::cooley_tukey_ntt::*;
    use crate::bellman::plonk::better_better_cs::cs::{
        TrivialAssembly, 
        Circuit, 
        PlonkCsWidth4WithNextStepParams, 
        Width4MainGateWithDNext
    };

    use super::super::aux_data::*;
    use super::super::data_structs::*;
    use super::super::verifying_circuit::*;
    use super::super::channel::*;
    use crate::plonk::circuit::curve::sw_affine::*;
    use crate::plonk::circuit::bigint::field::*;
    use crate::plonk::circuit::rescue::*;
    use crate::rescue::RescueEngine;
    use crate::bellman::pairing::bn256::{Bn256};
    use crate::rescue::bn256::Bn256RescueParams;
    use crate::rescue::bn256::rescue_transcript::RescueTranscript;
    use crate::bellman::plonk::commitments::transcript::Transcript;


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
            let zero = E::Fr::zero();
            
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

                // *q_a = gate.1[0];
                // *q_b = gate.1[1];
                // *q_c = gate.1[2];
                // *q_d = gate.1[3];
                // *q_m = gate.1[4];
                // *q_const = gate.1[5];
                // *q_d_next = gate.2[0];

                let state_variables = [a, b, cs.get_dummy_variable(), temp];
                let this_step_coeffs = [one.clone(), one.clone(), zero.clone(), negative_one, zero.clone(), zero.clone()];
                let next_step_coeffs = [zero];

                cs.new_gate(state_variables, this_step_coeffs, next_step_coeffs)?;
                std::mem::swap(&mut a_value, &mut b_value);

                b = a;
                a = temp;
            }

            let output = cs.alloc_input(|| {
                Ok(self.output.clone())
            })?;

            let state_variables = [a, cs.get_dummy_variable(), cs.get_dummy_variable(), output];
            let this_step_coeffs = [one.clone(), zero.clone(), zero.clone(), negative_one, zero.clone(), zero.clone()];
            let next_step_coeffs = [zero];

            cs.new_gate(state_variables, this_step_coeffs, next_step_coeffs)?;
            Ok(())
        }
    }

    pub fn recursion_test<E, T, CG, AD>(
        a: E::Fr, 
        b: E::Fr, 
        num_steps: usize,
        channel_params: &CG::Params,
        rns_params: &RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
        transcript_params: <T as Prng<E::Fr>>::Params,
    )
    where E: Engine, T: Transcript<E::Fr>, CG: ChannelGadget<E>, AD: AuxData<E>
    {
        let worker = Worker::new();
        let output = fibbonacci(&a, &b, num_steps);
    
        let circuit = BenchmarkCircuit::<E> {
            num_steps,
            a,
            b,
            output,
            _engine_marker: std::marker::PhantomData::<E>,
        };

        let mut assembly = OldActualAssembly::<E>::new();
        circuit.clone().synthesize(&mut assembly).expect("should synthesize");
        assembly.finalize();
        let setup = assembly.setup(&worker).expect("should setup");

        let crs_mons = Crs::<E, CrsForMonomialForm>::crs_42(setup.permutation_polynomials[0].size(), &worker);
        let crs_vals = Crs::<E, CrsForLagrangeForm>::crs_42(setup.permutation_polynomials[0].size(), &worker);

        let verification_key = VerificationKey::from_setup(
            &setup, 
            &worker, 
            &crs_mons
        ).expect("should create vk");

        let precomputations = SetupPolynomialsPrecomputations::from_setup(
            &setup, 
            &worker
        ).expect("should create precomputations");

        let mut prover = OldActualProver::<E>::new();
        circuit.synthesize(&mut prover).expect("should synthesize");
        prover.finalize();

        let size = setup.permutation_polynomials[0].size();

        let omegas_bitreversed = BitReversedOmegas::<E::Fr>::new_for_domain_size(size.next_power_of_two());
        let omegas_inv_bitreversed = 
            <OmegasInvBitreversed::<E::Fr> as CTPrecomputations::<E::Fr>>::new_for_domain_size(size.next_power_of_two());

        println!("BEFORE PROOVE");

        let proof = prover.prove::<T, _, _>(
            &worker,
            &setup,
            &precomputations,
            &crs_vals,
            &crs_mons,
            &omegas_bitreversed,
            &omegas_inv_bitreversed,
            transcript_params.clone(),
        ).expect("should prove");

        println!("DONE");

        let (is_valid, arg1, arg2) = verify::<_, _, T>(&proof, &verification_key, transcript_params).expect("should verify");

        assert!(is_valid);

        let verifier_circuit = PlonkVerifierCircuit::<E, CG, PlonkCsWidth4WithNextStepParams, OldActualParams, AD>::new(
            channel_params, 
            vec![a, b, output], 
            vec![arg1.unwrap(), arg2.unwrap()], 
            proof, 
            verification_key, 
            AD::new(), 
            rns_params,
        );

        let mut cs = TrivialAssembly::<E, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();
        verifier_circuit.synthesize(&mut cs).expect("should synthesize");
        cs.finalize();
        println!("number of gates: {}", cs.n());
        assert!(cs.is_satisfied());
    }

    #[test]
    fn bn256_recursion_test() 
    {   
        let a = <Bn256 as ScalarEngine>::Fr::one();
        let b = <Bn256 as ScalarEngine>::Fr::one();
        let num_steps = 1000;

        let rns_params = RnsParameters::<Bn256, <Bn256 as Engine>::Fq>::new_for_field(68, 110, 4);
        let rescue_params = Bn256RescueParams::new_checked_2_into_1();
 
        recursion_test::<Bn256, RescueTranscript<Bn256>, RescueChannelGadget<Bn256>, BN256AuxData>(
            a, b, num_steps, &rescue_params, &rns_params, &rescue_params,
        );
    }
}

        
