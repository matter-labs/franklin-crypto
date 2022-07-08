#[cfg(test)]
mod test {
    use crate::bellman::pairing::bls12_381::Bls12;
    use crate::bellman::pairing::bn256::Bn256;
    use crate::bellman::pairing::ff::*;
    use crate::bellman::plonk::better_better_cs::cs::*;
    use crate::bellman::Engine;
    use crate::bellman::SynthesisError;
    use crate::plonk::circuit::allocated_num::{AllocatedNum, Num};
    use crate::plonk::circuit::byte::Byte;
    use std::sync::Arc;

    use super::super::gadgets::*;
    use super::super::hasher::*;
    use super::super::utils::*;
    use crate::plonk::circuit::custom_rescue_gate::Rescue5CustomGate;
    use rand::{Rng, SeedableRng, StdRng};
    use std::convert::TryInto;
    use std::time::SystemTime;

    struct TestReinforcementConcreteCircuit<E: Engine> {
        input: [E::Fr; RC_STATE_WIDTH],
        output: [E::Fr; RC_STATE_WIDTH],
        elems_to_absorb: [E::Fr; RC_RATE],
        params: Arc<ReinforcedConcreteParams<E::Fr>>,
        is_const_test: bool,
    }

    impl<E: Engine> Circuit<E> for TestReinforcementConcreteCircuit<E> {
        type MainGate = Width4MainGateWithDNext;

        fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<E>>>, SynthesisError> {
            Ok(vec![
                Width4MainGateWithDNext::default().into_internal(),
                Rescue5CustomGate::default().into_internal(),
            ])
        }

        fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
            let mut actual_output_vars = Vec::with_capacity(RC_STATE_WIDTH);
            for value in self.output.iter() {
                if !self.is_const_test {
                    let new_var = AllocatedNum::alloc_input(cs, || Ok(value.clone()))?;
                    actual_output_vars.push(Num::Variable(new_var));
                } else {
                    actual_output_vars.push(Num::Constant(value.clone()));
                }
            }

            let alphas: [E::Fr; 2] = {
                self.params
                    .alphas
                    .iter()
                    .map(|x| from_u64::<E::Fr>(*x as u64))
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap()
            };
            let betas = self.params.betas.clone();
            let s_arr = self.params.si.clone();
            let p_prime = self.params.p_prime;
            let perm_f = |x: u16| -> u16 { self.params.sbox[x as usize] };

            let mut rc_gadget =
                ReinforcementConcreteGadget::new(cs, alphas, betas, p_prime, s_arr, perm_f, false)?;

            let supposed_output_vars = {
                let mut input_vars = Vec::with_capacity(self.input.len());
                for value in self.input.iter() {
                    if !self.is_const_test {
                        let new_var = AllocatedNum::alloc(cs, || Ok(value.clone()))?;
                        input_vars.push(Num::Variable(new_var));
                    } else {
                        input_vars.push(Num::Constant(value.clone()));
                    }
                }

                let mut values_to_absorb = Vec::with_capacity(self.elems_to_absorb.len());
                for value in self.elems_to_absorb.iter() {
                    if !self.is_const_test {
                        let new_var = AllocatedNum::alloc(cs, || Ok(value.clone()))?;
                        values_to_absorb.push(Num::Variable(new_var));
                    } else {
                        values_to_absorb.push(Num::Constant(value.clone()));
                    }
                }

                rc_gadget.reset(Some(&input_vars[..]));
                rc_gadget.absorb(cs, &values_to_absorb[..])?;
                rc_gadget.get_cur_state()
            };

            for (a, b) in supposed_output_vars
                .iter()
                .zip(actual_output_vars.into_iter())
            {
                a.enforce_equal(cs, &b)?;
            }

            Ok(())
        }
    }

    fn rc_gadget_test_template<E: DefaultRcParams>(is_const_test: bool) {
        // let seed: &[_] = &[1, 2, 3, 4, 5];
        // let mut rng: StdRng = SeedableRng::from_seed(seed);
        let seed = [SystemTime::now()
            .duration_since(SystemTime::UNIX_EPOCH)
            .unwrap()
            .as_secs() as usize];
        let mut rng: StdRng = SeedableRng::from_seed(&seed[..]);

        let mut input = [E::Fr::zero(); RC_STATE_WIDTH];
        input.iter_mut().for_each(|x| *x = rng.gen());

        let mut elems_to_absorb = [E::Fr::zero(); RC_RATE];
        elems_to_absorb.iter_mut().for_each(|x| *x = rng.gen());

        let params = E::get_default_rc_params();
        let hasher = ReinforcedConcrete::<E::Fr>::new(&params);
        let output = hasher.tester(&input, &elems_to_absorb);

        let circuit = TestReinforcementConcreteCircuit::<E> {
            input,
            output,
            elems_to_absorb,
            params,
            is_const_test,
        };
        let mut assembly =
            TrivialAssembly::<E, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();
        circuit.synthesize(&mut assembly).expect("must work");

        println!("Assembly contains {} gates", assembly.n());
        println!(
            "Total length of all tables: {}",
            assembly.total_length_of_all_tables
        );
        assert!(assembly.is_satisfied());
    }

    #[test]
    fn rc_bn256_gadget_test() {
        rc_gadget_test_template::<Bn256>(false)
    }

    #[test]
    fn rc_bn256_cnst_propagation_test() {
        rc_gadget_test_template::<Bn256>(true)
    }

    #[test]
    fn rc_bls12_gadget_test() {
        rc_gadget_test_template::<Bls12>(false)
    }

    #[test]
    fn rc_bls12_cnst_propagation_test() {
        rc_gadget_test_template::<Bls12>(true)
    }
}
