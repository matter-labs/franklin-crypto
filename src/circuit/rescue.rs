use bellman::pairing::{Engine,};
use bellman::pairing::ff::{Field, PrimeField};
use bellman::{ConstraintSystem, SynthesisError};
use super::boolean::{Boolean};
use super::num::{Num, AllocatedNum};
use super::Assignment;
use super::super::rescue::*;

pub trait CsSBox<E: Engine>: SBox<E> {
    fn apply_constraints<CS: ConstraintSystem<E>>(&self, cs: CS, element: &AllocatedNum<E>) -> Result<AllocatedNum<E>, SynthesisError>;
    fn apply_constraints_on_lc<CS: ConstraintSystem<E>>(&self, cs: CS, element: Num<E>) -> Result<Num<E>, SynthesisError>;
    fn apply_constraints_for_set<CS: ConstraintSystem<E>>(
        &self, 
        mut cs: CS, 
        elements: &[AllocatedNum<E>]
    ) -> Result<Vec<AllocatedNum<E>>, SynthesisError> {
        let mut results = Vec::with_capacity(elements.len());
        for (i, el) in elements.iter().enumerate() {
            let result = self.apply_constraints(
                cs.namespace(|| format!("apply sbox for word {}", i)), 
                &el
            )?;

            results.push(result);
        }

        Ok(results)
    }

    fn apply_constraints_on_lc_for_set<CS: ConstraintSystem<E>>(
        &self, 
        mut cs: CS, 
        elements: Vec<Num<E>>
    ) -> Result<Vec<Num<E>>, SynthesisError> {
        let mut results = Vec::with_capacity(elements.len());
        for (i, el) in elements.into_iter().enumerate() {
            if el.is_empty() {
                results.push(el);
            } else {
                let applied = self.apply_constraints_on_lc(
                    cs.namespace(|| format!("actually apply sbox for word {}", i)),
                    el
                )?;
                results.push(applied)
            }
        }

        Ok(results)
    }
}

impl<E: Engine> CsSBox<E> for QuinticSBox<E> {
    fn apply_constraints<CS: ConstraintSystem<E>>(
        &self, 
        mut cs: CS,
        el: &AllocatedNum<E>,
    ) -> Result<AllocatedNum<E>, SynthesisError> {        
        let sq = el.square(
            cs.namespace(|| "make 2nd power term")
        )?;

        let qd = sq.square(
            cs.namespace(|| "make 4th power term")
        )?;

        let res = el.mul(
            cs.namespace(|| "make 5th power term"),
            &qd
        )?;

        Ok(res)
    }

    fn apply_constraints_on_lc<CS: ConstraintSystem<E>>(
        &self, 
        mut cs: CS, 
        el: Num<E>
    ) -> Result<Num<E>, SynthesisError>
    {
        let sq = AllocatedNum::alloc(
            cs.namespace(|| "make 2nd power term"), 
            || {
                let mut val = *el.get_value().get()?;
                val.square();

                Ok(val)
            }
        )?;

        cs.enforce(
            || "enforce 2nd power term",
            |_| el.lc(E::Fr::one()),
            |_| el.lc(E::Fr::one()),
            |lc| lc + sq.get_variable()
        );

        let qd = sq.square(
            cs.namespace(|| "make 4th power term")
        )?;
            
        let res = AllocatedNum::alloc(
            cs.namespace(|| "make 5th power term"), 
            || {
                let mut val = *qd.get_value().get()?;
                let other = *el.get_value().get()?;
                val.mul_assign(&other);

                Ok(val)
            }
        )?;

        cs.enforce(
            || "enforce 5th power term",
            |_| el.lc(E::Fr::one()),
            |lc| lc + qd.get_variable(),
            |lc| lc + res.get_variable()
        );

        let res = Num::<E>::from(res);

        Ok(res)
    }
}

impl<E: Engine> CsSBox<E> for PowerSBox<E> {
    fn apply_constraints<CS: ConstraintSystem<E>>(
        &self,
        cs: CS,
        el: &AllocatedNum<E>,
    ) -> Result<AllocatedNum<E>, SynthesisError> {       
        if self.inv == 5u64 {
            self.apply_constraints_inv_quint(cs, el)
        } else {
            unimplemented!()
        }
    }

    fn apply_constraints_on_lc<CS: ConstraintSystem<E>>(
        &self,
        cs: CS,
        el: Num<E>,
    ) -> Result<Num<E>, SynthesisError> {       
        if self.inv == 5u64 {
            self.apply_constraints_inv_quint_on_lc(cs, el)
        } else {
            unimplemented!()
        }
    }
}

impl<E: Engine> PowerSBox<E> {
    fn apply_constraints_inv_quint<CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
        el: &AllocatedNum<E>,
    ) -> Result<AllocatedNum<E>, SynthesisError> {     
        // we do powering and prove the inverse relationship
        let power = self.power;
        let f = AllocatedNum::alloc(
            cs.namespace(|| "allocate final state"), 
            || {
                let v = *el.get_value().get()?;
                let s = v.pow(&power);

                Ok(s)
            }
        )?;
        
        let dummy_quintic_box = QuinticSBox::<E> { _marker: std::marker::PhantomData };
        let fifth = dummy_quintic_box.apply_constraints(
            cs.namespace(|| "apply quintic sbox for powering sbox"),
            &f
        )?;


        // // now constraint a chain that final^5 = state
        // let mut squares = Vec::with_capacity(state.len());
        // for (i, el) in final_states.iter().enumerate() {
        //     let sq = el.square(
        //         cs.namespace(|| format!("make 2nd power term for word {}", i))
        //     )?;
        //     squares.push(sq);
        // }

        // let mut quads = Vec::with_capacity(state.len());
        // for (i, el) in squares.iter().enumerate() {
        //     let qd = el.square(
        //         cs.namespace(|| format!("make 4th power term for word {}", i))
        //     )?;
        //     quads.push(qd);
        // }

        // let mut fifth = Vec::with_capacity(state.len());
        // for (i, (el, st)) in quads.iter().zip(final_states.iter()).enumerate() {
        //     let res = el.mul(
        //         cs.namespace(|| format!("make 5th power term for word {}", i)),
        //         &st
        //     )?;
        //     fifth.push(res);
        // }

        cs.enforce(
            || "enforce inverse box", 
            |lc| lc + el.get_variable() - fifth.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc
        );

        Ok(f)
    }

    fn apply_constraints_inv_quint_on_lc<CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
        el: Num<E>,
    ) -> Result<Num<E>, SynthesisError> {     
        // we do powering and prove the inverse relationship
        let power = self.power;
        let f = AllocatedNum::alloc(
            cs.namespace(|| "allocate final state"), 
            || {
                let v = *el.get_value().get()?;
                let s = v.pow(&power);

                Ok(s)
            }
        )?;

        let dummy_quintic_box = QuinticSBox::<E> { _marker: std::marker::PhantomData};
        let fifth = dummy_quintic_box.apply_constraints(
            cs.namespace(|| "apply quintic sbox for powering sbox"),
            &f
        )?;

        cs.enforce(
            || "enforce inverse box for LC", 
            |_| el.lc(E::Fr::one()) - fifth.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc
        );

        let f = Num::<E>::from(f);

        Ok(f)
    }
}

pub fn rescue_hash<E: RescueEngine, CS>(
    mut cs: CS,
    input: &[AllocatedNum<E>],
    params: &E::Params
) -> Result<Vec<AllocatedNum<E>>, SynthesisError>
    where <<E as RescueEngine>::Params as RescueHashParams<E>>::SBox0: CsSBox<E>, 
    <<E as RescueEngine>::Params as RescueHashParams<E>>::SBox1: CsSBox<E>,
    CS: ConstraintSystem<E>
{
    let output_len = params.output_len() as usize;
    let absorbtion_len = params.rate() as usize;
    let t = params.state_width();
    let rate = params.rate();

    let mut absorbtion_cycles = input.len() / absorbtion_len;
    if input.len() % absorbtion_len != 0 {
        absorbtion_cycles += 1;
    }
    
    // convert input into Nums
    let mut input = input.to_vec();
    input.resize(absorbtion_cycles * absorbtion_len, AllocatedNum::one::<CS>());

    let mut it = input.into_iter();

    // unroll first round manually
    let mut state = {
        let mut state = Vec::with_capacity(t as usize);
        for _ in 0..rate {
            let as_num = Num::<E>::from(it.next().unwrap());
            state.push(as_num);
        }
        for _ in rate..t {
            state.push(Num::<E>::zero());
        }

        debug_assert_eq!(state.len(), t as usize);

        rescue_mimc_over_lcs(
            cs.namespace(|| "rescue mimc for absorbtion round 0"),
            &state,
            params
        )?
    };

    for i in 1..absorbtion_cycles {
        for word in 0..rate {
            state[word as usize].add_assign_number_with_coeff(
                &it.next().unwrap(),
                E::Fr::one(),
            );
        }

        state = rescue_mimc_over_lcs(
            cs.namespace(|| format!("rescue mimc for absorbtion round {}", i)),
            &state,
            params
        )?;
    }

    debug_assert!(it.next().is_none());

    let mut result = vec![];

    for (i, num) in state[..output_len].iter().enumerate() {
        let allocated = num.clone().into_allocated_num(
            cs.namespace(|| format!("collapse output word {}", i)),
        )?;

        result.push(allocated);
    }

    Ok(result)
}

// pub fn rescue_mimc<E: RescueEngine, CS>(
//     mut cs: CS,
//     input: &[AllocatedNum<E>],
//     params: &E::Params
// ) -> Result<Vec<AllocatedNum<E>>, SynthesisError>
//     where <<E as RescueEngine>::Params as RescueHashParams<E>>::SBox0: CsSBox<E>, 
//     <<E as RescueEngine>::Params as RescueHashParams<E>>::SBox1: CsSBox<E>,
//     CS: ConstraintSystem<E>
// {
//     let state_len = params.state_width() as usize;

//     assert_eq!(input.len(), state_len); 

//     let mut state: Vec<AllocatedNum<E>> = Vec::with_capacity(input.len());
//     for (i, (c, &constant)) in input.iter() 
//                         .zip(params.round_constants(0).iter())
//                         .enumerate()
//     {
//         let with_constant = c.add_constant(
//             cs.namespace(|| format!("rescue add first round constant for word {}", i)),
//             constant
//         )?;

//         state.push(with_constant);
//     }

//     let mut linear_transformation_results_scratch = Vec::with_capacity(state_len);

//     // parameters use number of rounds that is number of invocations of each SBox,
//     // so we double
//     for round_num in 0..(2*params.num_rounds()) {
//         // apply corresponding sbox
//         let state = if round_num & 1u32 == 0 {
//             params.sbox_0().apply_constraints(
//                 cs.namespace(|| format!("apply SBox for round {}", round_num)),
//                 &state
//             )?
//         } else {
//             params.sbox_1().apply_constraints(
//                 cs.namespace(|| format!("apply SBox for round {}", round_num)),
//                 &state
//             )?
//         };

//         // apply multiplication by MDS


//         let round_constants = params.round_constants(round_num + 1);
//         for row_idx in 0..state_len {
//             let row = params.mds_matrix_row(row_idx as u32);
//             let linear_applied = scalar_product(&state[..], row);
//             let with_round_constant = linear_applied.add_constant(
//                 CS::one(), 
//                 round_constants[row_idx]
//             );
//             let collapsed = with_round_constant.into_allocated_num(
//                 cs.namespace(|| format!("collapse after MDS and round constant for word {}", row_idx))
//             )?;
//             linear_transformation_results_scratch.push(collapsed);
//         }

//         state.clone_from_slice(&linear_transformation_results_scratch);
//         linear_transformation_results_scratch.truncate(0);
//     }

//     Ok(state)
// }

pub fn rescue_mimc_over_lcs<E: RescueEngine, CS>(
    mut cs: CS,
    input: &[Num<E>],
    params: &E::Params
) -> Result<Vec<Num<E>>, SynthesisError>
    where <<E as RescueEngine>::Params as RescueHashParams<E>>::SBox0: CsSBox<E>, 
    <<E as RescueEngine>::Params as RescueHashParams<E>>::SBox1: CsSBox<E>,
    CS: ConstraintSystem<E>
{
    let state_len = params.state_width() as usize;

    assert_eq!(input.len(), state_len); 

    let mut state: Vec<Num<E>> = Vec::with_capacity(input.len());
    for (i, (c, &constant)) in input.iter().cloned()
                        .zip(params.round_constants(0).iter())
                        .enumerate()
    {
        let with_constant = c.add_constant(
            CS::one(),
            constant
        );

        state.push(with_constant);
    }

    let mut state = Some(state);

    // parameters use number of rounds that is number of invocations of each SBox,
    // so we double
    for round_num in 0..(2*params.num_rounds()) {
        // apply corresponding sbox
        let tmp = if round_num & 1u32 == 0 {
            params.sbox_0().apply_constraints_on_lc_for_set(
                cs.namespace(|| format!("apply SBox_0 for round {}", round_num)),
                state.take().unwrap()
            )?
        } else {
            params.sbox_1().apply_constraints_on_lc_for_set(
                cs.namespace(|| format!("apply SBox_1 for round {}", round_num)),
                state.take().unwrap()
            )?
        };


        // apply multiplication by MDS

        let mut linear_transformation_results_scratch = Vec::with_capacity(state_len);

        let round_constants = params.round_constants(round_num + 1);
        for row_idx in 0..state_len {
            let row = params.mds_matrix_row(row_idx as u32);
            let linear_applied = scalar_product_over_lc_of_length_one(&tmp[..], row);
            let with_round_constant = linear_applied.add_constant(
                CS::one(), 
                round_constants[row_idx]
            );
            linear_transformation_results_scratch.push(with_round_constant);
            // let collapsed = with_round_constant.into_allocated_num(
            //     cs.namespace(|| format!("collapse after MDS and round constant for word {}", row_idx))
            // )?;
            // linear_transformation_results_scratch.push(collapsed);
        }

        state = Some(linear_transformation_results_scratch);

        // state.clone_from_slice(&linear_transformation_results_scratch);
        // linear_transformation_results_scratch.truncate(0);
    }

    Ok(state.unwrap())
}

fn scalar_product<E: Engine> (input: &[AllocatedNum<E>], by: &[E::Fr]) -> Num<E> {
    assert!(input.len() == by.len());
    let mut result = Num::zero();
    for (a, b) in input.iter().zip(by.iter()) {
        result = result.add_number_with_coeff(a, *b);
    }

    result
}

fn scalar_product_over_lc_of_length_one<E: Engine> (input: &[Num<E>], by: &[E::Fr]) -> Num<E> {
    assert!(input.len() == by.len());
    let mut result = Num::zero();
    for (a, b) in input.iter().zip(by.iter()) {
        if a.is_empty() {
            continue;
        }
        let var = a.unwrap_as_allocated_num();
        result.add_assign_number_with_coeff(&var, *b);
    }

    result
}

fn print_lc<E: Engine>(input: &[Num<E>]) {
    for el in input.iter() {
        println!("{}", el.get_value().unwrap());
    }
}

fn print_nums<E: Engine>(input: &[AllocatedNum<E>]) {
    for el in input.iter() {
        println!("{}", el.get_value().unwrap());
    }
}

#[cfg(test)]
mod test {
    use rand::{SeedableRng, Rng, XorShiftRng};
    use super::*;
    use ::circuit::test::*;
    use bellman::pairing::bn256::{Bn256, Fr};
    use bellman::pairing::ff::PrimeField;
    use crate::rescue;
    use crate::group_hash::BlakeHasher;

    #[test]
    fn test_rescue_mimc_gadget() {
        use crate::rescue::bn256::*;
        let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        let params = Bn256RescueParams::new_2_into_1::<BlakeHasher>();
        let input: Vec<Fr> = (0..params.state_width()).map(|_| rng.gen()).collect();
        let expected = rescue::rescue_mimc::<Bn256>(&params, &input[..]);

        {
            let mut cs = TestConstraintSystem::<Bn256>::new();

            let input_words: Vec<Num<Bn256>> = input.iter().enumerate().map(|(i, b)| {
                let v = AllocatedNum::alloc(
                    cs.namespace(|| format!("input {}", i)),
                    || {
                        Ok(*b)
                    }).unwrap();

                Num::<Bn256>::from(v)
            }).collect();


            let res = rescue_mimc_over_lcs(
                cs.namespace(|| "rescue mimc"),
                &input_words,
                &params
            ).unwrap();

            let unsatisfied = cs.which_is_unsatisfied();
            if let Some(s) = unsatisfied {
                println!("Unsatisfied at {}", s);
            }

            assert!(cs.is_satisfied());
            assert!(res.len() == (params.state_width() as usize));

            assert_eq!(res[0].get_value().unwrap(), expected[0]);
        }
    }

    #[test]
    fn test_rescue_hash_gadget() {
        use crate::rescue::bn256::*;
        let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        let params = Bn256RescueParams::new_2_into_1::<BlakeHasher>();
        // let input: Vec<Fr> = (0..(params.rate()*2)).map(|_| rng.gen()).collect();
        let input: Vec<Fr> = (0..params.rate()).map(|_| rng.gen()).collect();
        let expected = rescue::rescue_hash::<Bn256>(&params, &input[..]);

        {
            let mut cs = TestConstraintSystem::<Bn256>::new();

            let input_words: Vec<AllocatedNum<Bn256>> = input.iter().enumerate().map(|(i, b)| {
                AllocatedNum::alloc(
                    cs.namespace(|| format!("input {}", i)),
                    || {
                        Ok(*b)
                    }).unwrap()
            }).collect();

            let res = rescue_hash(
                cs.namespace(|| "rescue hash"),
                &input_words,
                &params
            ).unwrap();

            assert!(cs.is_satisfied());
            assert!(res.len() == 1);
            println!("Rescue hash {} to {} taken {} constraints", input.len(), res.len(), cs.num_constraints());

            assert_eq!(res[0].get_value().unwrap(), expected[0]);
        }
    }

    #[test]
    fn test_rescue_hash_gadget_3_into_1() {
        use crate::rescue::bn256::*;
        let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        let params = Bn256RescueParams::new_3_into_1::<BlakeHasher>();
        // let input: Vec<Fr> = (0..(params.rate()*2)).map(|_| rng.gen()).collect();
        let input: Vec<Fr> = (0..params.rate()).map(|_| rng.gen()).collect();
        let expected = rescue::rescue_hash::<Bn256>(&params, &input[..]);

        {
            let mut cs = TestConstraintSystem::<Bn256>::new();

            let input_words: Vec<AllocatedNum<Bn256>> = input.iter().enumerate().map(|(i, b)| {
                AllocatedNum::alloc(
                    cs.namespace(|| format!("input {}", i)),
                    || {
                        Ok(*b)
                    }).unwrap()
            }).collect();

            let res = rescue_hash(
                cs.namespace(|| "rescue hash"),
                &input_words,
                &params
            ).unwrap();

            assert!(cs.is_satisfied());
            assert!(res.len() == 1);
            println!("Rescue hash {} to {} taken {} constraints", input.len(), res.len(), cs.num_constraints());

            assert_eq!(res[0].get_value().unwrap(), expected[0]);
        }
    }

    #[test]
    fn test_transpile_rescue_hash_gadget() {
        use crate::rescue::bn256::*;
        let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        let params = Bn256RescueParams::new_2_into_1::<BlakeHasher>();
        // let input: Vec<Fr> = (0..(params.rate()*2)).map(|_| rng.gen()).collect();
        let input: Vec<Fr> = (0..params.rate()).map(|_| rng.gen()).collect();
        let expected = rescue::rescue_hash::<Bn256>(&params, &input[..]);

        #[derive(Clone)]
        struct RescueTester<E: RescueEngine> {
            num_duplicates: usize,
            input: Vec<E::Fr>,
            params: E::Params,
        }

        impl<E: RescueEngine> crate::bellman::Circuit<E> for RescueTester<E> 
        where <<E as RescueEngine>::Params as RescueHashParams<E>>::SBox0: CsSBox<E>, 
            <<E as RescueEngine>::Params as RescueHashParams<E>>::SBox1: CsSBox<E>
        {
            fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
                for _ in 0..self.num_duplicates {
                    let mut input_words = vec![];
                    for (i, inp) in self.input.iter().enumerate() {
                        let v = AllocatedNum::alloc(
                            cs.namespace(|| format!("hash input {}", i)),
                            || {
                                Ok(*inp)
                            }
                        )?;

                        input_words.push(v);
                    }

                    let mut res = rescue_hash(
                        cs.namespace(|| "rescue hash"),
                        &input_words,
                        &self.params
                    )?;

                    let res = res.pop().unwrap();

                    res.inputize(
                        cs.namespace(|| "make input")
                    )?;
                
                }

                Ok(())
            }
        }

        use crate::bellman::plonk::*;
        use crate::bellman::worker::Worker;

        // let mut transpiler = Transpiler::new();

        let dupls: usize = 1024;

        let c = RescueTester::<Bn256> {
            num_duplicates: dupls,
            input: input,
            params: params
        };


        let hints = transpile::<Bn256, _>(c.clone()).expect("transpilation is successful");

        let mut hints_hist = std::collections::HashMap::new();
        hints_hist.insert("into addition gate".to_owned(), 0);
        hints_hist.insert("merge LC".to_owned(), 0);
        hints_hist.insert("into quadratic gate".to_owned(), 0);
        hints_hist.insert("into multiplication gate".to_owned(), 0);

        use crate::bellman::plonk::better_cs::adaptor::TranspilationVariant;

        for (_, h) in hints.iter() {
            match h {
                TranspilationVariant::IntoQuadraticGate => {
                    *hints_hist.get_mut(&"into quadratic gate".to_owned()).unwrap() += 1;
                },
                TranspilationVariant::MergeLinearCombinations(..) => {
                    *hints_hist.get_mut(&"merge LC".to_owned()).unwrap() += 1;
                },
                TranspilationVariant::IntoAdditionGate(..) => {
                    *hints_hist.get_mut(&"into addition gate".to_owned()).unwrap() += 1;
                },
                TranspilationVariant::IntoMultiplicationGate(..) => {
                    *hints_hist.get_mut(&"into multiplication gate".to_owned()).unwrap() += 1;
                }
            }
        }

        println!("Transpilation hist = {:?}", hints_hist);

        println!("Done transpiling");

        is_satisfied_using_one_shot_check(c.clone(), &hints).expect("must validate");

        println!("Done checking if satisfied using one-shot");

        is_satisfied(c.clone(), &hints).expect("must validate");

        println!("Done checking if satisfied");

        let setup = setup(c.clone(), &hints).expect("must make setup");

        println!("Made {} invocations into {} gates", dupls, setup.n);
    }
}