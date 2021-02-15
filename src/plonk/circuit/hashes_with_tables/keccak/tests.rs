#[cfg(test)]
mod test {
    use crate::bellman::plonk::better_better_cs::cs::*;
    use crate::bellman::pairing::ff::*;
    use crate::bellman::SynthesisError;
    use crate::bellman::Engine;
    use crate::tiny_keccak::Keccak;
     use crate::plonk::circuit::allocated_num::{
        AllocatedNum,
        Num,
    };
    use crate::plonk::circuit::byte::{
        Byte,
    };

    use crate::bellman::pairing::bn256::{Bn256, Fr};

    use super::super::gadgets::*;
    use super::super::utils::*;
    use super::super::super::utils::*;
    
    use rand::{Rng, SeedableRng, StdRng};
    use std::convert::TryInto;


    struct TestKeccakCircuit<E:Engine>{
        input: Vec<E::Fr>,
        output: [E::Fr; DEFAULT_KECCAK_DIGEST_WORDS_SIZE],
    }

    impl<E: Engine> Circuit<E> for TestKeccakCircuit<E> {
        type MainGate = Width4MainGateWithDNext;

        fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<E>>>, SynthesisError> {
            Ok(
                vec![
                    Width4MainGateWithDNext::default().into_internal(),
                ]
            )
        }

        fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {

            let mut input_vars = Vec::with_capacity(self.input.len());
            for value in self.input.iter() {
                let new_var = AllocatedNum::alloc(cs, || Ok(value.clone()))?;
                input_vars.push(Num::Variable(new_var));
            }

            let mut actual_output_vars = Vec::with_capacity(DEFAULT_KECCAK_DIGEST_WORDS_SIZE);
            for value in self.output.iter() {
                let new_var = AllocatedNum::alloc_input(cs, || Ok(value.clone()))?;
                actual_output_vars.push(new_var);
            }

            let keccak_gadget = KeccakGadget::new(cs, None, None, None, None, false, "")?; 
            let supposed_output_vars = keccak_gadget.digest(cs, &input_vars[..])?;

            // for (a, b) in supposed_output_vars.iter().zip(actual_output_vars.into_iter()) {
            //     let a = match a {
            //         Num::Variable(x) => x,
            //         Num::Constant(_) => unreachable!(),
            //     };

            //     a.eq(cs, b)?;
            // }

            Ok(())
        }
    }

    fn slice_to_ff<Fr: PrimeField>(input: &[u8]) -> Fr {
        assert_eq!(input.len(), 8);
        let (int_bytes, _) = input.split_at(std::mem::size_of::<u64>());
        let num = u64::from_le_bytes(int_bytes.try_into().unwrap());
        u64_to_ff(num)
    }

    #[test]
    fn keccak_gadget_test() 
    {
        const NUM_OF_BLOCKS: usize = 1;
        let mut rng = rand::thread_rng();

        let mut input = [0u8; 8 * KECCAK_RATE_WORDS_SIZE * NUM_OF_BLOCKS];
        for i in 0..(input.len() - 1) {
            input[i] = rng.gen();
        }
        *(input.last_mut().unwrap()) = 0b10000001 as u8;

        let mut hasher = Keccak::new_sha3_256();
        hasher.update(&input[0..(input.len() - 1)]);

        let mut output: [u8; DEFAULT_KECCAK_DIGEST_WORDS_SIZE * 8] = [0; DEFAULT_KECCAK_DIGEST_WORDS_SIZE * 8];
        hasher.finalize(&mut output);
    
        let mut input_fr_arr = Vec::with_capacity(KECCAK_RATE_WORDS_SIZE * NUM_OF_BLOCKS);
        let mut output_fr_arr = [Fr::zero(); DEFAULT_KECCAK_DIGEST_WORDS_SIZE];

        for (i, block) in input.chunks(8).enumerate() {
            input_fr_arr.push(slice_to_ff::<Fr>(block));
        }

        for (i, block) in output.chunks(8).enumerate() {
            output_fr_arr[i] = slice_to_ff::<Fr>(block);
        }
        
        let circuit = TestKeccakCircuit::<Bn256>{
            input: input_fr_arr,
            output: output_fr_arr,
        };

        let mut assembly = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

        circuit.synthesize(&mut assembly).expect("must work");
        println!("Assembly contains {} gates", assembly.n());
        println!("Total length of all tables: {}", assembly.total_length_of_all_tables);
        assert!(assembly.is_satisfied());
    }
}



