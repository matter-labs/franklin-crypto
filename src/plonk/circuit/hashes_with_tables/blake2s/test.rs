#[cfg(test)]
mod test {
    use crate::bellman::plonk::better_better_cs::cs::*;
    use crate::bellman::pairing::ff::*;
    use crate::bellman::SynthesisError;
    use crate::bellman::Engine;
    use crate::bellman::pairing::bn256::{Bn256, Fr};
    use crate::blake2::{Blake2s, Digest};
    use crate::plonk::circuit::allocated_num::{
        AllocatedNum,
        Num,
    };
    use crate::plonk::circuit::byte::{
        Byte,
    };

    use super::super::gadgets::*;
    use super::super::super::utils::*;
    use rand::{Rng, SeedableRng, StdRng};


    struct TestBlake2sCircuit<E:Engine>{
        input: Vec<E::Fr>,
        output: [E::Fr; 8],
        use_additional_tables: bool,
        is_const_test: bool,
        is_byte_test: bool,
    }

    impl<E: Engine> Circuit<E> for TestBlake2sCircuit<E> {
        type MainGate = Width4MainGateWithDNext;

        fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<E>>>, SynthesisError> {
            Ok(
                vec![
                    Width4MainGateWithDNext::default().into_internal(),
                ]
            )
        }

        fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> 
        {
            let mut input_vars = Vec::with_capacity(16);
            for value in self.input.iter() {
                let new_var = AllocatedNum::alloc(cs, || Ok(value.clone()))?;
                input_vars.push(Num::Variable(new_var));
            }

            let mut actual_output_vars = Vec::with_capacity(8);
            for value in self.output.iter() {
                let new_var = AllocatedNum::alloc_input(cs, || Ok(value.clone()))?;
                actual_output_vars.push(new_var);
            }

            let blake2s_gadget = Blake2sGadget::new(cs, self.use_additional_tables)?;

            let supposed_output_vars = if !self.is_byte_test {    
                let mut input_vars = Vec::with_capacity(self.input.len());
                for value in self.input.iter() {
                    if !self.is_const_test {
                        let new_var = AllocatedNum::alloc(cs, || Ok(value.clone()))?;
                        input_vars.push(Num::Variable(new_var));
                    }
                    else {
                        input_vars.push(Num::Constant(value.clone()));
                    }
                }
                sha256_gadget.sha256(cs, &input_vars[..])?
            }
            else {
                let mut input_vars = Vec::with_capacity(self.input.len());
                for value in self.input.iter() {
                    if !self.is_const_test {
                        let new_var = AllocatedNum::alloc(cs, || Ok(value.clone()))?;
                        let byte = Byte::from_num_unconstrained(cs, Num::Variable(new_var));
                        input_vars.push(byte);
                    }
                    else {
                        let byte = Byte::from_cnst(cs, value.clone());
                        input_vars.push(byte);
                    }
                }
                sha256_gadget.sha256_from_bytes(cs, &input_vars[..])?
            };




            for (a, b) in supposed_output_vars.iter().zip(actual_output_vars.into_iter()) {
                let a = match a {
                    Num::Variable(x) => x,
                    Num::Constant(_) => unreachable!(),
                };

                a.eq(cs, b)?;
            }

            Ok(())
        }
    }

    fn slice_to_ff<Fr: PrimeField>(slice: &[u8]) -> Fr {
        assert_eq!(slice.len(), 4);
        let mut repr : <Fr as PrimeField>::Repr = Fr::zero().into_repr();
        repr.as_mut()[0] = slice[0] as u64 + ((slice[1] as u64) << 8) + ((slice[2] as u64) << 16) + ((slice[3] as u64) << 24);
        Fr::from_repr(repr).expect("should parse")
    }

    #[test]
    fn blake2s_gadget_test() 
    {
        const NUM_OF_BLOCKS: usize = 3;
        const USE_ADDITIONAL_TABLES: bool = true;

        let seed: &[_] = &[1, 2, 3, 4, 5];
        let mut rng: StdRng = SeedableRng::from_seed(seed);

        let mut input = [0u8; 64 * NUM_OF_BLOCKS];
        for i in 0..(64 * NUM_OF_BLOCKS) {
            input[i] = rng.gen();
        }

        let mut hasher = Blake2s::new();
        hasher.update(&input[..]);
        let output = hasher.finalize();

        let mut input_fr_arr = Vec::with_capacity(16 * NUM_OF_BLOCKS);
        let mut output_fr_arr = [Fr::zero(); 8];

        for block in input.chunks(4) {
            input_fr_arr.push(slice_to_ff::<Fr>(block));
        }

        for (i, block) in output.chunks(4).enumerate() {
            output_fr_arr[i] = slice_to_ff::<Fr>(block);
        }
        
        let circuit = TestBlake2sCircuit::<Bn256>{
            input: input_fr_arr,
            output: output_fr_arr,
            use_additional_tables: USE_ADDITIONAL_TABLES,
        };

        let mut assembly = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

        circuit.synthesize(&mut assembly).expect("must work");
        println!("Assembly contains {} gates", assembly.n());
        println!("Total length of all tables: {}", assembly.total_length_of_all_tables);
        assert!(assembly.is_satisfied());
    }

    #[test]
    fn polished_sha256_gadget_bytes_test() 
    {
        const NUM_OF_BYTES: usize = 341;
        const IS_CONST_TEST: bool = false;

        let mut rng = rand::thread_rng();

        let mut input = [0u8; NUM_OF_BYTES];
        for i in 0..NUM_OF_BYTES {
            input[i] = rng.gen();
        }
    
        // create a Sha256 object
        let mut hasher = Sha256::new();
        // write input message
        hasher.input(&input[..]);
        // read hash digest and consume hasher
        let output = hasher.result();

        let mut input_fr_arr : Vec<<Bn256 as ScalarEngine>::Fr> = Vec::with_capacity(NUM_OF_BYTES);
        let mut output_fr_arr = [Fr::zero(); 8];

        input_fr_arr.extend(input.iter().map(|byte| u64_to_ff::<<Bn256 as ScalarEngine>::Fr>(*byte as u64)));
        
        for (i, block) in output.chunks(4).enumerate() {
            output_fr_arr[i] = slice_to_ff::<Fr>(block);
        }
        
        let circuit = TestSha256Circuit::<Bn256>{
            input: input_fr_arr,
            output: output_fr_arr,
            ch_base_num_of_chunks: None,
            maj_sheduler_base_num_of_chunks: None,
            is_const_test: IS_CONST_TEST,
            is_byte_test: true,
        };

        let mut assembly = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

        circuit.synthesize(&mut assembly).expect("must work");
        println!("Assembly contains {} gates", assembly.n());
        println!("Total length of all tables: {}", assembly.total_length_of_all_tables);
        assert!(assembly.is_satisfied());
    }
}