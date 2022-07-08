#[cfg(test)]
mod test {
    use crate::bellman::pairing::ff::*;
    use crate::bellman::plonk::better_better_cs::cs::*;
    use crate::bellman::Engine;
    use crate::bellman::SynthesisError;
    use crate::plonk::circuit::allocated_num::{AllocatedNum, Num};
    use crate::plonk::circuit::boolean::AllocatedBit;
    use crate::plonk::circuit::boolean::Boolean;
    use crate::plonk::circuit::byte::Byte;
    use crate::tiny_keccak::Keccak;

    use crate::bellman::pairing::bn256::{Bn256, Fr};

    use super::super::super::utils::*;
    use super::super::gadgets::*;
    use super::super::utils::*;

    use rand::{Rng, SeedableRng, StdRng};
    use std::convert::TryInto;

    struct TestKeccakCircuit<E: Engine> {
        input: Vec<E::Fr>,
        output: [E::Fr; DEFAULT_KECCAK_DIGEST_WORDS_SIZE],
        is_const_test: bool,
        is_byte_test: bool,
    }

    impl<E: Engine> Circuit<E> for TestKeccakCircuit<E> {
        type MainGate = Width4MainGateWithDNext;

        fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<E>>>, SynthesisError> {
            Ok(vec![Width4MainGateWithDNext::default().into_internal()])
        }

        fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
            let mut actual_output_vars = Vec::with_capacity(DEFAULT_KECCAK_DIGEST_WORDS_SIZE);
            for value in self.output.iter() {
                if !self.is_const_test {
                    let new_var = AllocatedNum::alloc_input(cs, || Ok(value.clone()))?;
                    actual_output_vars.push(Num::Variable(new_var));
                } else {
                    actual_output_vars.push(Num::Constant(value.clone()));
                }
            }

            let keccak_gadget = Keccak256Gadget::new(cs, None, None, None, None, false, "")?;

            let supposed_output_vars = if !self.is_byte_test {
                let mut input_vars = Vec::with_capacity(self.input.len());
                for value in self.input.iter() {
                    if !self.is_const_test {
                        let new_var = AllocatedNum::alloc(cs, || Ok(value.clone()))?;
                        input_vars.push(Num::Variable(new_var));
                    } else {
                        input_vars.push(Num::Constant(value.clone()));
                    }
                }
                keccak_gadget.digest(cs, &input_vars[..])?
            } else {
                let mut input_vars = Vec::with_capacity(self.input.len());
                for value in self.input.iter() {
                    if !self.is_const_test {
                        let new_var = AllocatedNum::alloc(cs, || Ok(value.clone()))?;
                        let byte = Byte::from_num_unconstrained(cs, Num::Variable(new_var));
                        input_vars.push(byte);
                    } else {
                        let byte = Byte::from_cnst(value.clone());
                        input_vars.push(byte);
                    }
                }
                keccak_gadget.digest_from_bytes(cs, &input_vars[..])?
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

    fn slice_to_ff<Fr: PrimeField>(input: &[u8]) -> Fr {
        assert_eq!(input.len(), 8);
        let (int_bytes, _) = input.split_at(std::mem::size_of::<u64>());
        let num = u64::from_le_bytes(int_bytes.try_into().unwrap());
        u64_to_ff(num)
    }

    fn keccak_gadget_test_template(is_const_test: bool) {
        const NUM_OF_BLOCKS: usize = 4;
        let mut rng = rand::thread_rng();

        let mut input = [0u8; 8 * KECCAK_RATE_WORDS_SIZE * NUM_OF_BLOCKS];
        for i in 0..(input.len() - 1) {
            input[i] = rng.gen();
        }
        *(input.last_mut().unwrap()) = 0b10000001 as u8;
        let mut output: [u8; DEFAULT_KECCAK_DIGEST_WORDS_SIZE * 8] =
            [0; DEFAULT_KECCAK_DIGEST_WORDS_SIZE * 8];

        Keccak::keccak256(&input[0..(input.len() - 1)], &mut output);

        let mut input_fr_arr = Vec::with_capacity(KECCAK_RATE_WORDS_SIZE * NUM_OF_BLOCKS);
        let mut output_fr_arr = [Fr::zero(); DEFAULT_KECCAK_DIGEST_WORDS_SIZE];

        for (_i, block) in input.chunks(8).enumerate() {
            input_fr_arr.push(slice_to_ff::<Fr>(block));
        }

        for (i, block) in output.chunks(8).enumerate() {
            output_fr_arr[i] = slice_to_ff::<Fr>(block);
        }

        let circuit = TestKeccakCircuit::<Bn256> {
            input: input_fr_arr,
            output: output_fr_arr,
            is_const_test,
            is_byte_test: false,
        };

        let mut assembly = TrivialAssembly::<
            Bn256,
            PlonkCsWidth4WithNextStepParams,
            Width4MainGateWithDNext,
        >::new();

        circuit.synthesize(&mut assembly).expect("must work");
        println!("Assembly contains {} gates", assembly.n());
        println!(
            "Total length of all tables: {}",
            assembly.total_length_of_all_tables
        );
        assert!(assembly.is_satisfied());
    }

    #[test]
    fn keccak_gadget_test() {
        keccak_gadget_test_template(false)
    }

    #[test]
    fn keccak_gadget_const_propagation_test() {
        keccak_gadget_test_template(true)
    }

    #[test]
    fn keccak_gadget_bytes_test() {
        keccak_gadget_bytes_test_impl::<777>();
    }

    #[test]
    fn keccak_gadget_short_bytes_test() {
        keccak_gadget_bytes_test_impl::<64>();
    }

    fn keccak_gadget_bytes_test_impl<const NUM_OF_BYTES: usize>() {
        const IS_CONST_TEST: bool = false;

        let mut rng = rand::thread_rng();
        let mut input = [0u8; NUM_OF_BYTES];
        for i in 0..NUM_OF_BYTES {
            input[i] = rng.gen();
        }

        let mut output: [u8; DEFAULT_KECCAK_DIGEST_WORDS_SIZE * 8] =
            [0; DEFAULT_KECCAK_DIGEST_WORDS_SIZE * 8];
        Keccak::keccak256(&input[0..input.len()], &mut output);

        let mut input_fr_arr: Vec<<Bn256 as ScalarEngine>::Fr> = Vec::with_capacity(NUM_OF_BYTES);
        let mut output_fr_arr = [Fr::zero(); DEFAULT_KECCAK_DIGEST_WORDS_SIZE];

        input_fr_arr.extend(
            input
                .iter()
                .map(|byte| u64_to_ff::<<Bn256 as ScalarEngine>::Fr>(*byte as u64)),
        );

        for (i, block) in output.chunks(8).enumerate() {
            output_fr_arr[i] = slice_to_ff::<Fr>(block);
        }

        let circuit = TestKeccakCircuit::<Bn256> {
            input: input_fr_arr,
            output: output_fr_arr,
            is_const_test: IS_CONST_TEST,
            is_byte_test: true,
        };

        let mut assembly = TrivialAssembly::<
            Bn256,
            PlonkCsWidth4WithNextStepParams,
            Width4MainGateWithDNext,
        >::new();

        circuit.synthesize(&mut assembly).expect("must work");
        println!("Assembly contains {} gates", assembly.n());
        println!(
            "Total length of all tables: {}",
            assembly.total_length_of_all_tables
        );
        assert!(assembly.is_satisfied());
    }

    struct TestKeccakRoundFunctionCircuit<E: Engine> {
        inputs: Vec<Vec<E::Fr>>,
        outputs: Vec<[E::Fr; DEFAULT_KECCAK_DIGEST_WORDS_SIZE]>,
    }

    impl<E: Engine> Circuit<E> for TestKeccakRoundFunctionCircuit<E> {
        type MainGate = Width4MainGateWithDNext;

        fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<E>>>, SynthesisError> {
            Ok(vec![Width4MainGateWithDNext::default().into_internal()])
        }

        fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
            let keccak_gadget = Keccak256Gadget::new(cs, None, None, None, None, false, "")?;
            let mut keccak_state = KeccakState::default();

            let input_chunks = self.inputs.iter().flat_map(|inner_vec| {
                inner_vec
                    .chunks(KECCAK_RATE_WORDS_SIZE)
                    .identify_first_last()
            });

            let mut is_initialized = false;
            let mut output_block_idx = 0;

            for (is_start_of_block, _is_end_of_block, in_chunk) in input_chunks {
                let mut elems_to_absorb = [Num::<E>::zero(); KECCAK_RATE_WORDS_SIZE];
                for (i, value) in in_chunk.iter().enumerate() {
                    let new_var = AllocatedNum::alloc(cs, || Ok(value.clone()))?;
                    elems_to_absorb[i] = Num::Variable(new_var);
                }

                if !is_initialized {
                    is_initialized = true;
                    keccak_state =
                        keccak_gadget.keccak_round_function_init(cs, &elems_to_absorb[..])?;
                } else {
                    let flag = Boolean::Is(AllocatedBit::alloc(cs, Some(is_start_of_block))?);
                    let (new_state, supposed_output_vars) = keccak_gadget.keccak_round_function(
                        cs,
                        keccak_state,
                        elems_to_absorb,
                        flag,
                    )?;
                    keccak_state = new_state;

                    if is_start_of_block {
                        let mut actual_output_vars =
                            Vec::with_capacity(DEFAULT_KECCAK_DIGEST_WORDS_SIZE);
                        for value in self.outputs[output_block_idx].iter() {
                            let new_var = AllocatedNum::alloc_input(cs, || Ok(value.clone()))?;
                            actual_output_vars.push(Num::Variable(new_var));
                        }

                        for (a, b) in supposed_output_vars
                            .iter()
                            .zip(actual_output_vars.into_iter())
                        {
                            a.enforce_equal(cs, &b)?;
                        }

                        output_block_idx += 1;
                    }
                }
            }

            // there is one output remaining_to_be_checked
            let elems_to_absorb = [Num::<E>::zero(); KECCAK_RATE_WORDS_SIZE];
            let flag = Boolean::constant(true);
            let (_new_state, supposed_output_vars) =
                keccak_gadget.keccak_round_function(cs, keccak_state, elems_to_absorb, flag)?;

            let mut actual_output_vars = Vec::with_capacity(DEFAULT_KECCAK_DIGEST_WORDS_SIZE);
            for value in self.outputs[output_block_idx].iter() {
                let new_var = AllocatedNum::alloc_input(cs, || Ok(value.clone()))?;
                actual_output_vars.push(Num::Variable(new_var));
            }

            for (a, b) in supposed_output_vars
                .iter()
                .zip(actual_output_vars.into_iter())
            {
                a.enforce_equal(cs, &b)?;
            }

            output_block_idx += 1;
            assert_eq!(output_block_idx, self.outputs.len());

            Ok(())
        }
    }

    #[test]
    fn keccak_round_function_test() {
        let mut rng = rand::thread_rng();

        // we test the following pattern:
        // 2 blocks || 1 block || 1 block || 3 blocks
        const BLOCK_SIZES: [usize; 3] = [1, 3, 1];
        let mut inputs = vec![];
        let mut outputs = vec![];

        for block_size in BLOCK_SIZES.iter() {
            let mut input: Vec<u8> = Vec::with_capacity(KECCAK_RATE_WORDS_SIZE * block_size * 8);
            for _i in 0..(KECCAK_RATE_WORDS_SIZE * block_size * 8) {
                input.push(rng.gen());
            }
            *(input.last_mut().unwrap()) = 0b10000001 as u8;
            let mut output: [u8; DEFAULT_KECCAK_DIGEST_WORDS_SIZE * 8] =
                [0; DEFAULT_KECCAK_DIGEST_WORDS_SIZE * 8];

            Keccak::keccak256(&input[0..(input.len() - 1)], &mut output);

            let mut input_fr_arr = Vec::with_capacity(KECCAK_RATE_WORDS_SIZE * block_size);
            let mut output_fr_arr = [Fr::zero(); DEFAULT_KECCAK_DIGEST_WORDS_SIZE];

            for (_i, block) in input.chunks(8).enumerate() {
                input_fr_arr.push(slice_to_ff::<Fr>(block));
            }

            for (i, block) in output.chunks(8).enumerate() {
                output_fr_arr[i] = slice_to_ff::<Fr>(block);
            }

            inputs.push(input_fr_arr);
            outputs.push(output_fr_arr);
        }

        let circuit = TestKeccakRoundFunctionCircuit::<Bn256> { inputs, outputs };

        let mut assembly = TrivialAssembly::<
            Bn256,
            PlonkCsWidth4WithNextStepParams,
            Width4MainGateWithDNext,
        >::new();

        circuit.synthesize(&mut assembly).expect("must work");
        println!("Assembly contains {} gates", assembly.n());
        println!(
            "Total length of all tables: {}",
            assembly.total_length_of_all_tables
        );
        assert!(assembly.is_satisfied());
    }

    #[test]
    fn test_keccak_on_real_prover() {
        const NUM_OF_BLOCKS: usize = 2;
        let mut rng = rand::thread_rng();

        let mut input = [0u8; 8 * KECCAK_RATE_WORDS_SIZE * NUM_OF_BLOCKS];
        for i in 0..(input.len() - 1) {
            input[i] = rng.gen();
        }
        *(input.last_mut().unwrap()) = 0b10000001 as u8;
        let mut output: [u8; DEFAULT_KECCAK_DIGEST_WORDS_SIZE * 8] =
            [0; DEFAULT_KECCAK_DIGEST_WORDS_SIZE * 8];

        Keccak::keccak256(&input[0..(input.len() - 1)], &mut output);

        let mut input_fr_arr = Vec::with_capacity(KECCAK_RATE_WORDS_SIZE * NUM_OF_BLOCKS);
        let mut output_fr_arr = [Fr::zero(); DEFAULT_KECCAK_DIGEST_WORDS_SIZE];

        for (_i, block) in input.chunks(8).enumerate() {
            input_fr_arr.push(slice_to_ff::<Fr>(block));
        }

        for (i, block) in output.chunks(8).enumerate() {
            output_fr_arr[i] = slice_to_ff::<Fr>(block);
        }

        let circuit = TestKeccakCircuit::<Bn256> {
            input: input_fr_arr,
            output: output_fr_arr,
            is_const_test: false,
            is_byte_test: false,
        };

        let mut assembly = TrivialAssembly::<
            Bn256,
            PlonkCsWidth4WithNextStepParams,
            Width4MainGateWithDNext,
        >::new();

        circuit.synthesize(&mut assembly).expect("must work");
        assembly.finalize();
        println!("Assembly contains {} gates", assembly.n());
        println!(
            "Total length of all tables: {}",
            assembly.total_length_of_all_tables
        );
        assert!(assembly.is_satisfied());

        use crate::bellman::kate_commitment::{Crs, CrsForMonomialForm};
        use crate::bellman::plonk::better_better_cs::setup::VerificationKey;
        use crate::bellman::plonk::better_better_cs::verifier::verify;
        use crate::bellman::plonk::commitments::transcript::keccak_transcript::RollingKeccakTranscript;
        use crate::bellman::worker::Worker;

        let worker = Worker::new();
        let required_size = assembly.n().next_power_of_two();
        let crs = Crs::<Bn256, CrsForMonomialForm>::dummy_crs(1 << 20);
        let setup = assembly
            .create_setup::<TestKeccakCircuit<Bn256>>(&worker)
            .unwrap();
        let vk = VerificationKey::from_setup(&setup, &worker, &crs).unwrap();

        let proof = assembly
            .create_proof::<_, RollingKeccakTranscript<Fr>>(&worker, &setup, &crs, None)
            .unwrap();

        // let valid = verify::<_, _, RollingKeccakTranscript<Fr>>(&vk, &proof, None).unwrap();
        // assert!(valid);
    }
}
