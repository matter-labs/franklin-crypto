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
            let mut actual_output_vars = Vec::with_capacity(8);
            for value in self.output.iter() {
                if !self.is_const_test {
                    let new_var = AllocatedNum::alloc_input(cs, || Ok(value.clone()))?;
                    actual_output_vars.push(Num::Variable(new_var));
                }
                else {
                    actual_output_vars.push(Num::Constant(value.clone()));
                }
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
                blake2s_gadget.digest(cs, &input_vars[..])?
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
                blake2s_gadget.digest_bytes(cs, &input_vars[..])?
            };

            for (a, b) in supposed_output_vars.iter().zip(actual_output_vars.into_iter()) {
                a.enforce_equal(cs, &b)?;
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

    fn blake2s_gadget_test_impl(num_of_blocks: usize, use_additional_tables: bool, is_const_test: bool, is_byte_test: bool) 
    {
        let seed: &[_] = &[1, 2, 3, 4, 5];
        let mut rng: StdRng = SeedableRng::from_seed(seed);

        let mut input = vec![0u8; 64 * num_of_blocks];
        for i in 0..(64 * num_of_blocks) {
            input[i] = rng.gen();
        }

        let mut hasher = Blake2s::new();
        hasher.update(&input[..]);
        let output = hasher.finalize();

        let mut input_fr_arr = Vec::with_capacity(16 * num_of_blocks);
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
            use_additional_tables,
            is_const_test,
            is_byte_test,
        };

        let mut assembly = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

        circuit.synthesize(&mut assembly).expect("must work");
        println!("Assembly contains {} gates", assembly.n());
        println!("Total length of all tables: {}", assembly.total_length_of_all_tables);
        assert!(assembly.is_satisfied());
    }

    #[test]
    fn blake2s_gadget_single_block_test() 
    {
        blake2s_gadget_test_impl(1, false, false, false) 
    }

    #[test]
    fn blake2s_gadget_multiple_blocks_test() 
    {
        blake2s_gadget_test_impl(3, false, false, false) 
    }

    #[test]
    fn blake2s_gadget_additional_tables_test() 
    {
        blake2s_gadget_test_impl(2, true, false, false) 
    }

    #[test]
    fn blake2s_gadget_additional_tables_const_test() 
    {
        blake2s_gadget_test_impl(2, true, true, false) 
    }

    #[test]
    fn blake2s_gadget_const_test() 
    {
        blake2s_gadget_test_impl(3, false, true, false) 
    }

    fn blake2s_gadget_byte_input_test() 
    {
        blake2s_gadget_test_impl(1, false, false, true) 
    }
}