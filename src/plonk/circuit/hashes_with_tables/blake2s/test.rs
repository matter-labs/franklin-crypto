#[cfg(test)]
mod test {
    use crate::plonk::better_better_cs::cs::*;
    use crate::pairing::ff::*;
    use crate::SynthesisError;
    use crate::Engine;
    use blake2::{Blake2s, Digest};
    use crate::plonk::better_better_cs::gadgets::num::{
        AllocatedNum,
        Num,
    };
    use crate::pairing::bn256::{Bn256, Fr};

    use super::super::gadgets::*;
    use super::super::optimized_gadgets::*;
    use super::super::utils::*;
    use rand::{Rng, SeedableRng, StdRng};


    struct TestBlake2sCircuit<E:Engine, G: Blake2sGadget<E>>{
        input: Vec<E::Fr>,
        output: [E::Fr; 8],
        _gadget_marker: std::marker::PhantomData<G>,
    }

    impl<E: Engine, G: Blake2sGadget<E>> Circuit<E> for TestBlake2sCircuit<E, G> {
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
                input_vars.push(Num::Allocated(new_var));
            }

            let mut actual_output_vars = Vec::with_capacity(8);
            for value in self.output.iter() {
                let new_var = AllocatedNum::alloc_input(cs, || Ok(value.clone()))?;
                actual_output_vars.push(new_var);
            }

            let blake2s_gadget = G::new(cs)?;

            let supposed_output_vars = blake2s_gadget.digest(cs, &input_vars[..])?;

            for (a, b) in supposed_output_vars.iter().zip(actual_output_vars.into_iter()) {
                let a = match a {
                    Num::Allocated(x) => x,
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

    fn blake2s_gadget_test_impl<G: Blake2sGadget<Bn256>>() 
    {
        const NUM_OF_BLOCKS: usize = 1;
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
        
        let circuit = TestBlake2sCircuit::<Bn256, G>{
            input: input_fr_arr,
            output: output_fr_arr,
            _gadget_marker : std::marker::PhantomData::<G>,
        };

        let mut assembly = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

        circuit.synthesize(&mut assembly).expect("must work");
        println!("Assembly contains {} gates", assembly.n());
        println!("Total length of all tables: {}", assembly.total_length_of_all_tables);
        assert!(assembly.is_satisfied());
    }

    #[test]
    fn naive_blake2s_gadget_test() {
        blake2s_gadget_test_impl::<NaiveBlake2sGadget<Bn256>>()
    }

    #[test]
    fn optimized_blake2s_gadget_test() {
        blake2s_gadget_test_impl::<OptimizedBlake2sGadget<Bn256>>()
    }  
}