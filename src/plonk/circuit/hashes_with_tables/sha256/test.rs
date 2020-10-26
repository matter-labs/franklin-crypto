#[cfg(test)]
mod test {
    use crate::bellman::plonk::better_better_cs::cs::*;
    use crate::bellman::pairing::ff::*;
    use crate::bellman::SynthesisError;
    use crate::bellman::Engine;
    use crate::sha2::{Sha256, Digest};
    use crate::plonk::circuit::allocated_num::{
        AllocatedNum,
        Num,
    };
    use crate::bellman::pairing::bn256::{Bn256, Fr};

    use super::super::gadgets::*;
    use rand::{Rng, SeedableRng, StdRng};


    struct TestSha256Circuit<E:Engine>{
        input: Vec<E::Fr>,
        output: [E::Fr; 8],
        ch_base_num_of_chunks: Option<usize>,
        maj_sheduler_base_num_of_chunks: Option<usize>,
        is_const_test: bool,
    }

    impl<E: Engine> Circuit<E> for TestSha256Circuit<E> {
        type MainGate = Width4MainGateWithDNext;

        fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<E>>>, SynthesisError> {
            Ok(
                vec![
                    Width4MainGateWithDNext::default().into_internal(),
                ]
            )
        }

        fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {

            let mut input_vars = Vec::with_capacity(16);
            for value in self.input.iter() {
                if !self.is_const_test {
                    let new_var = AllocatedNum::alloc(cs, || Ok(value.clone()))?;
                    input_vars.push(Num::Variable(new_var));
                }
                else {
                    input_vars.push(Num::Constant(value.clone()));
                }
            }

            let mut actual_output_vars = Vec::with_capacity(16);
            for value in self.output.iter() {
                if !self.is_const_test {
                    let new_var = AllocatedNum::alloc_input(cs, || Ok(value.clone()))?;
                    actual_output_vars.push(Num::Variable(new_var));
                }
                else {
                    actual_output_vars.push(Num::Constant(value.clone()));
                }
            }

            let sha256_gadget = Sha256Gadget::new(
                cs, self.ch_base_num_of_chunks, self.maj_sheduler_base_num_of_chunks, false, false, 0, "",
            )?;

            let supposed_output_vars = sha256_gadget.sha256(cs, &input_vars[..])?;

            for (a, b) in supposed_output_vars.iter().zip(actual_output_vars.into_iter()) {
                a.eq(cs, &b)?;
            }

            Ok(())
        }
    }

    fn slice_to_ff<Fr: PrimeField>(slice: &[u8]) -> Fr {
        assert_eq!(slice.len(), 4);
        let mut repr : <Fr as PrimeField>::Repr = Fr::zero().into_repr();
        repr.as_mut()[0] = slice[3] as u64 + ((slice[2] as u64) << 8) + ((slice[1] as u64) << 16) + ((slice[0] as u64) << 24);
        Fr::from_repr(repr).expect("should parse")
    }

    #[test]
    fn polished_sha256_gadget_single_block_test() 
    {
        // SHA256 Pre-processing (Padding):
        // begin with the original message of length L bits
        // append a single '1' bit
        // append K '0' bits, where K is the minimum number >= 0 such that L + 1 + K + 64 is a multiple of 512
        // append L as a 64-bit big-endian integer, making the total post-processed length a multiple of 512 bits
        let seed: &[_] = &[1, 2, 3, 4, 5];
        let mut rng: StdRng = SeedableRng::from_seed(seed);

        let mut input = [0u8; 64];
        for i in 0..55 {
            input[i] = rng.gen();
        }
        input[55] = 0b10000000;
        input[62] = 01;
        input[63] = 0xb8;

        // create a Sha256 object
        let mut hasher = Sha256::new();
        // write input message
        hasher.input(&input[0..55]);
        // read hash digest and consume hasher
        let output = hasher.result();

        let mut input_fr_arr = Vec::with_capacity(16);
        let mut output_fr_arr = [Fr::zero(); 8];

        for block in input.chunks(4) {
            input_fr_arr.push(slice_to_ff::<Fr>(block));
        }

        for (i, block) in output.chunks(4).enumerate() {
            output_fr_arr[i] = slice_to_ff::<Fr>(block);
        }
        
        let circuit = TestSha256Circuit::<Bn256>{
            input: input_fr_arr,
            output: output_fr_arr,
            ch_base_num_of_chunks: None,
            maj_sheduler_base_num_of_chunks: None,
            is_const_test: false,
        };

        let mut assembly = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

        circuit.synthesize(&mut assembly).expect("must work");
        println!("Assembly contains {} gates", assembly.n());
        println!("Total length of all tables: {}", assembly.total_length_of_all_tables);
        assert!(assembly.is_satisfied());
    }

    #[test]
    fn polished_sha256_gadget_multiple_blocks_test() 
    {
        const NUM_OF_BLOCKS: usize = 2;
        let mut rng = rand::thread_rng();

        let mut input = [0u8; 64 * NUM_OF_BLOCKS];
        for i in 0..(64 * (NUM_OF_BLOCKS-1) + 55) {
            input[i] = rng.gen();
        }
        input[64 * (NUM_OF_BLOCKS-1) + 55] = 0b10000000;
        
        let total_number_of_bits = (64 * (NUM_OF_BLOCKS-1) + 55) * 8;
        input[64 * (NUM_OF_BLOCKS-1) + 60] = (total_number_of_bits >> 24) as u8;
        input[64 * (NUM_OF_BLOCKS-1) + 61] = (total_number_of_bits >> 16) as u8;
        input[64 * (NUM_OF_BLOCKS-1) + 62] = (total_number_of_bits >> 8) as u8;
        input[64 * (NUM_OF_BLOCKS-1) + 63] = total_number_of_bits as u8;

        // create a Sha256 object
        let mut hasher = Sha256::new();
        // write input message
        hasher.input(&input[0..(64 * (NUM_OF_BLOCKS-1) + 55)]);
        // read hash digest and consume hasher
        let output = hasher.result();

        let mut input_fr_arr = Vec::with_capacity(16 * NUM_OF_BLOCKS);
        let mut output_fr_arr = [Fr::zero(); 8];

        for block in input.chunks(4) {
            input_fr_arr.push(slice_to_ff::<Fr>(block));
        }

        for (i, block) in output.chunks(4).enumerate() {
            output_fr_arr[i] = slice_to_ff::<Fr>(block);
        }
        
        let circuit = TestSha256Circuit::<Bn256>{
            input: input_fr_arr,
            output: output_fr_arr,
            ch_base_num_of_chunks: None,
            maj_sheduler_base_num_of_chunks: None,
            is_const_test: false,
        };

        let mut assembly = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

        circuit.synthesize(&mut assembly).expect("must work");
        println!("Assembly contains {} gates", assembly.n());
        println!("Total length of all tables: {}", assembly.total_length_of_all_tables);
        assert!(assembly.is_satisfied());
    }

    #[test]
    fn polished_sha256_gadget_const_propagation_test() 
    {
        const NUM_OF_BLOCKS: usize = 3;
        let mut rng = rand::thread_rng();

        let mut input = [0u8; 64 * NUM_OF_BLOCKS];
        for i in 0..(64 * (NUM_OF_BLOCKS-1) + 55) {
            input[i] = rng.gen();
        }
        input[64 * (NUM_OF_BLOCKS-1) + 55] = 0b10000000;
        
        let total_number_of_bits = (64 * (NUM_OF_BLOCKS-1) + 55) * 8;
        input[64 * (NUM_OF_BLOCKS-1) + 60] = (total_number_of_bits >> 24) as u8;
        input[64 * (NUM_OF_BLOCKS-1) + 61] = (total_number_of_bits >> 16) as u8;
        input[64 * (NUM_OF_BLOCKS-1) + 62] = (total_number_of_bits >> 8) as u8;
        input[64 * (NUM_OF_BLOCKS-1) + 63] = total_number_of_bits as u8;

        // create a Sha256 object
        let mut hasher = Sha256::new();
        // write input message
        hasher.input(&input[0..(64 * (NUM_OF_BLOCKS-1) + 55)]);
        // read hash digest and consume hasher
        let output = hasher.result();

        let mut input_fr_arr = Vec::with_capacity(16 * NUM_OF_BLOCKS);
        let mut output_fr_arr = [Fr::zero(); 8];

        for block in input.chunks(4) {
            input_fr_arr.push(slice_to_ff::<Fr>(block));
        }

        for (i, block) in output.chunks(4).enumerate() {
            output_fr_arr[i] = slice_to_ff::<Fr>(block);
        }
        
        let circuit = TestSha256Circuit::<Bn256>{
            input: input_fr_arr,
            output: output_fr_arr,
            ch_base_num_of_chunks: None,
            maj_sheduler_base_num_of_chunks: None,
            is_const_test: true,
        };

        let mut assembly = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

        circuit.synthesize(&mut assembly).expect("must work");
        println!("Assembly contains {} gates", assembly.n());
        println!("Total length of all tables: {}", assembly.total_length_of_all_tables);
        assert!(assembly.is_satisfied());
    }

    // fn polished_sha256_from_bytes_test()
    // {

    // }
}