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


    pub fn recursion_test<E: Engine, T: Transcript<E::Fr>>(a: E::Fr, b: E::Fr, num_steps: usize) -> Result<(), SynthesisError>
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
        circuit.clone().synthesize(&mut assembly)?;
        assembly.finalize();
        let setup = assembly.setup(&worker)?;

        let crs_mons = Crs::<E, CrsForMonomialForm>::crs_42(setup.permutation_polynomials[0].size(), &worker);
        let crs_vals = Crs::<E, CrsForLagrangeForm>::crs_42(setup.permutation_polynomials[0].size(), &worker);

        let verification_key = VerificationKey::from_setup(
            &setup, 
            &worker, 
            &crs_mons
        ).unwrap();

        let precomputations = SetupPolynomialsPrecomputations::from_setup(
            &setup, 
            &worker
        ).unwrap();

        let mut prover = OldActualProver::<E>::new();
        circuit.synthesize(&mut prover)?;
        prover.finalize();

        let size = setup.permutation_polynomials[0].size();

        let omegas_bitreversed = BitReversedOmegas::<E::Fr>::new_for_domain_size(size.next_power_of_two());
        let omegas_inv_bitreversed = 
            <OmegasInvBitreversed::<E::Fr> as CTPrecomputations::<E::Fr>>::new_for_domain_size(size.next_power_of_two());

        let proof = prover.prove::<T, _, _>(
            &worker,
            &setup,
            &precomputations,
            &crs_vals,
            &crs_mons,
            &omegas_bitreversed,
            &omegas_inv_bitreversed,
        )?;

        let (is_valid, arg1, arg2) = verify::<_, _, T>(&proof, &verification_key)?;

        assert!(is_valid);

        let verifier_circuit = PlonkVerifierCircuit<'a, E, T, P, OldP, AD> 
        where E: Engine, T: ChannelGadget<E>, AD: AuxData<E>, OldP: OldCSParams<E>, P: PlonkConstraintSystemParams<E>
        {
            _engine_marker : std::marker::PhantomData<E>,
            _channel_marker : std::marker::PhantomData<T>,
            _cs_params_marker: std::marker::PhantomData<P>,

            channel_params: T::Params,

            public_inputs : Vec<E::Fr>,
            supposed_outputs: Vec<E::G1Affine>,
            proof: Cell<Option<Proof<E, OldP>>>,
            vk: Cell<Option<VerificationKey<E, OldP>>>,
            aux_data: AD,
            params: &'a RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
        }
                //test_constraint_system_is_satisfied;
        }

        cs.synthesize();
}

        
