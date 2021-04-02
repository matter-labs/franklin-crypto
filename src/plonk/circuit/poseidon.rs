use crate::bellman::pairing::{
    Engine,
};

use crate::bellman::pairing::ff::{
    Field,
    PrimeField,
    PrimeFieldRepr,
    BitIterator
};

use crate::bellman::{
    SynthesisError,
};

use crate::bellman::plonk::better_better_cs::cs::{
    Variable, 
    ConstraintSystem,
    ArithmeticTerm,
    MainGateTerm,
    PlonkConstraintSystemParams
};

use crate::plonk::circuit::Assignment;

use super::allocated_num::{
    AllocatedNum,
    Num
};

use super::linear_combination::{
    LinearCombination
};

use poseidon_hash::{
    PoseidonEngine, PoseidonHashParams, SBox, QuinticSBox, PowerSBox
};

use super::custom_rescue_gate::apply_5th_power;

pub trait PoseidonCsSBox<E: Engine>: SBox<E> {
    const SHOULD_APPLY_FORWARD: bool;
    fn apply_constraints<CS: ConstraintSystem<E>>(&self, cs: &mut CS, element: &Num<E>, force_no_custom_gates: bool) -> Result<Num<E>, SynthesisError>;
    fn apply_constraints_in_reverse<CS: ConstraintSystem<E>>(&self, cs: &mut CS, element: &Num<E>, force_no_custom_gates: bool) -> Result<Num<E>, SynthesisError>;
}

impl<E: Engine> PoseidonCsSBox<E> for QuinticSBox<E> {
    const SHOULD_APPLY_FORWARD: bool = true;

    fn apply_constraints<CS: ConstraintSystem<E>>(
        &self, 
        cs: &mut CS,
        el: &Num<E>,
        force_no_custom_gates: bool
    ) -> Result<Num<E>, SynthesisError> {        
        match el {
            Num::Constant(constant) => {
                let mut result = *constant;
                result.square();
                result.square();
                result.mul_assign(constant);

                Ok(Num::Constant(result))
            },
            Num::Variable(el) => {
                // we take a value and make 5th power from it
                if force_no_custom_gates == false && CS::Params::HAS_CUSTOM_GATES == true && CS::Params::STATE_WIDTH >= 4 {
                    let out = apply_5th_power(cs, el, None)?;

                    return Ok(Num::Variable(out));
                }
                
                let square = el.mul(cs, el)?;
                let quad = square.mul(cs, &square)?;
                let fifth = el.mul(cs, &quad)?;

                Ok(Num::Variable(fifth))
            }
        }
    }

    fn apply_constraints_in_reverse<CS: ConstraintSystem<E>>(
        &self, 
        cs: &mut CS,
        el: &Num<E>,
        force_no_custom_gates: bool
    ) -> Result<Num<E>, SynthesisError> {     
        unimplemented!("Making 5th power can only be used in straight order")
    }
}

enum OpMode<E: PoseidonEngine> {
    AccumulatingToAbsorb(Vec<Num<E>>),
    SqueezedInto(Vec<LinearCombination<E>>)
}

pub struct StatefulPoseidonGadget<E: PoseidonEngine> {
    internal_state: Vec<LinearCombination<E>>,
    mode: OpMode<E>
}

impl<E: PoseidonEngine> StatefulPoseidonGadget<E> 
    where <<E as PoseidonEngine>::Params as PoseidonHashParams<E>>::SBox: PoseidonCsSBox<E>
{
    pub fn new(
        params: &E::Params
    ) -> Self {
        let op = OpMode::AccumulatingToAbsorb(Vec::with_capacity(params.rate() as usize));

        Self {
            internal_state: vec![LinearCombination::<E>::zero(); params.state_width() as usize],
            mode: op
        }
    }

    fn mimc_over_lcs<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        state: &[LinearCombination<E>],
        params: &E::Params
    ) -> Result<Vec<LinearCombination<E>>, SynthesisError> {
        let state_len = state.len();
        assert_eq!(state_len, params.state_width() as usize);
        let mut state = Some(state.to_vec());

        let last_state_idx = state_len - 1;

        assert!(params.num_full_rounds() % 2 == 0);
        let half_full_rounds = params.num_full_rounds() / 2;

        for round in 0..half_full_rounds {
            let round_constants = params.round_constants(round);

            for (idx, s) in state.as_mut().unwrap().iter_mut().enumerate() {
                s.add_assign_constant(round_constants[idx]);
            }

            let mut after_nonlin = Vec::with_capacity(state_len);

            for s in state.take().unwrap().into_iter() {
                let input = s.into_num(cs)?;
                let sbox = params.sbox();
                let output = if <<<E as PoseidonEngine>::Params as PoseidonHashParams<E>>::SBox as PoseidonCsSBox<E>>::SHOULD_APPLY_FORWARD {
                    sbox.apply_constraints(cs, &input, false)?
                } else {
                    sbox.apply_constraints_in_reverse(cs, &input, false)?
                };

                after_nonlin.push(output);
            }

            // apply MDS

            let mut new_state = Vec::with_capacity(state_len);

            for i in 0..state_len {
                let mut lc = LinearCombination::<E>::zero();
                let mds_row = params.mds_matrix_row(i as u32);

                for (s, coeff) in after_nonlin.iter().zip(mds_row.iter()){
                    lc.add_assign_number_with_coeff(s, *coeff);
                }

                new_state.push(lc);
            }

            state = Some(new_state);
        }

        for round in half_full_rounds..(params.num_partial_rounds() + half_full_rounds) {
            let round_constants = params.round_constants(round);

            for (idx, s) in state.as_mut().unwrap().iter_mut().enumerate() {
                s.add_assign_constant(round_constants[idx]);
            }

            let mut after_nonlin = Vec::with_capacity(state_len);

            let mut st = state.take().unwrap();

            let no_application: Vec<_> = st.drain(..last_state_idx).collect();

            for s in no_application.into_iter() {
                let s = s.into_num(cs)?;

                after_nonlin.push(s);
            }

            // after_nonlin.extend(no_application);

            for s in st.into_iter() {
                let input = s.into_num(cs)?;
                let sbox = params.sbox();
                let output = if <<<E as PoseidonEngine>::Params as PoseidonHashParams<E>>::SBox as PoseidonCsSBox<E>>::SHOULD_APPLY_FORWARD {
                    sbox.apply_constraints(cs, &input, false)?
                } else {
                    sbox.apply_constraints_in_reverse(cs, &input, false)?
                };

                after_nonlin.push(output);

                // let mut lc = LinearCombination::<E>::zero(); 
                // lc.add_assign_number_with_coeff(&output, E::Fr::one());

                // after_nonlin.push(lc);
            }

            assert_eq!(after_nonlin.len(), state_len);

            // apply MDS and round constants

            let mut new_state = Vec::with_capacity(state_len);

            for i in 0..state_len {
                let mut lc = LinearCombination::<E>::zero();
                let mds_row = params.mds_matrix_row(i as u32);

                for (s, coeff) in after_nonlin.iter().zip(mds_row.iter()){
                    lc.add_assign_number_with_coeff(s, *coeff);
                }

                // for (s, coeff) in after_nonlin.iter().zip(mds_row.iter()){
                //     lc.add_assign_scaled(&s, *coeff);
                // }

                new_state.push(lc);
            }

            state = Some(new_state);
        }

        for round in (params.num_partial_rounds() + half_full_rounds)..(params.num_partial_rounds() + params.num_full_rounds()) {
            let round_constants = params.round_constants(round);

            for (idx, s) in state.as_mut().unwrap().iter_mut().enumerate() {
                s.add_assign_constant(round_constants[idx]);
            }

            let mut after_nonlin = Vec::with_capacity(state_len);

            for s in state.take().unwrap().into_iter() {
                let input = s.into_num(cs)?;
                let sbox = params.sbox();
                let output = if <<<E as PoseidonEngine>::Params as PoseidonHashParams<E>>::SBox as PoseidonCsSBox<E>>::SHOULD_APPLY_FORWARD {
                    sbox.apply_constraints(cs, &input, false)?
                } else {
                    sbox.apply_constraints_in_reverse(cs, &input, false)?
                };

                after_nonlin.push(output);
            }

            // apply MDS and round constants

            let mut new_state = Vec::with_capacity(state_len);

            for i in 0..state_len {
                let mut lc = LinearCombination::<E>::zero();
                let mds_row = params.mds_matrix_row(i as u32);

                for (s, coeff) in after_nonlin.iter().zip(mds_row.iter()){
                    lc.add_assign_number_with_coeff(s, *coeff);
                }

                new_state.push(lc);
            }

            state = Some(new_state);
        }

        Ok(state.unwrap())
    }

    pub fn absorb_single_value<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        value: Num<E>,
        params: &E::Params
    ) -> Result<(), SynthesisError> {
        match self.mode {
            OpMode::AccumulatingToAbsorb(ref mut into) => {
                // two cases
                // either we have accumulated enough already and should to 
                // a mimc round before accumulating more, or just accumulate more
                let rate = params.rate() as usize;
                if into.len() < rate {
                    into.push(value);
                } else {
                    for i in 0..rate {
                        self.internal_state[i].add_assign_number_with_coeff(&into[i], E::Fr::one());
                    }

                    self.internal_state = Self::mimc_over_lcs(
                        cs,
                        &self.internal_state, 
                        &params
                    )?;

                    into.truncate(0);
                    into.push(value.clone());
                }
            },
            OpMode::SqueezedInto(_) => {
                // we don't need anything from the output, so it's dropped

                let mut s = Vec::with_capacity(params.rate() as usize);
                s.push(value);

                let op = OpMode::AccumulatingToAbsorb(s);
                self.mode = op;
            }
        }

        Ok(())
    }

    pub fn absorb<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        input: &[AllocatedNum<E>],
        params: &E::Params
    ) -> Result<(), SynthesisError>{
        let absorbtion_len = params.rate() as usize;
        let t = params.state_width();
        let rate = params.rate();
    
        let mut absorbtion_cycles = input.len() / absorbtion_len;
        if input.len() % absorbtion_len != 0 {
            absorbtion_cycles += 1;
        }

        let mut input: Vec<_> = input.iter().map(|el| Num::Variable(el.clone())).collect();
        input.resize(absorbtion_cycles * absorbtion_len, Num::Constant(E::Fr::one()));
    
        let it = input.into_iter();
        
        for (idx, val) in it.enumerate() {
            self.absorb_single_value(
                cs,
                val,
                &params
            )?;
        }

        Ok(())
    }

    pub fn squeeze_out_single<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        params: &E::Params
    ) -> Result<LinearCombination<E>, SynthesisError> {
        match self.mode {
            OpMode::AccumulatingToAbsorb(ref mut into) => {
                let rate = params.rate() as usize;
                assert_eq!(into.len(), rate, "padding was necessary!");
                // two cases
                // either we have accumulated enough already and should to 
                // a mimc round before accumulating more, or just accumulate more
                for i in 0..rate {
                    self.internal_state[i].add_assign_number_with_coeff(&into[i], E::Fr::one());
                }

                self.internal_state = Self::mimc_over_lcs(
                    cs,
                    &self.internal_state, 
                    &params
                )?;

                // we don't take full internal state, but only the rate
                let mut sponge_output = self.internal_state[0..rate].to_vec();
                let output = sponge_output.drain(0..1).next().expect("squeezed sponge must contain some data left");

                let op = OpMode::SqueezedInto(sponge_output);
                self.mode = op;

                return Ok(output);
            },
            OpMode::SqueezedInto(ref mut into) => {
                assert!(into.len() > 0, "squeezed state is depleted!");
                let output = into.drain(0..1).next().expect("squeezed sponge must contain some data left");

                return Ok(output);
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use rand::{SeedableRng, Rng, XorShiftRng};
    use super::*;
    use bellman::pairing::bn256::{Bn256, Fr};
    use bellman::pairing::ff::PrimeField;
    use poseidon_hash::{poseidon_hash, StatefulSponge};
    use poseidon_hash::bn256::Bn256PoseidonParams;
    use crate::bellman::plonk::better_better_cs::cs::{
        TrivialAssembly, 
        PlonkCsWidth4WithNextStepParams, 
        Width4MainGateWithDNext
    };

    use crate::plonk::circuit::Width4WithCustomGates;

    #[test]
    fn test_poseidon_hash_plonk_gadget() {
        let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        let params = Bn256PoseidonParams::new_checked_2_into_1();
        let input: Vec<Fr> = (0..(params.rate())).map(|_| rng.gen()).collect();
        // let input: Vec<Fr> = (0..(params.rate()+1)).map(|_| rng.gen()).collect();
        let expected = poseidon_hash::<Bn256>(&params, &input[..]);

        {
            let mut cs = TrivialAssembly::<Bn256, 
                Width4WithCustomGates,
                Width4MainGateWithDNext
            >::new();

            let input_words: Vec<AllocatedNum<Bn256>> = input.iter().enumerate().map(|(i, b)| {
                AllocatedNum::alloc(
                    &mut cs,
                    || {
                        Ok(*b)
                    }).unwrap()
            }).collect();

            let mut rescue_gadget = StatefulPoseidonGadget::<Bn256>::new(
                &params
            );

            rescue_gadget.absorb(
                &mut cs,
                &input_words, 
                &params
            ).unwrap();

            let res_0 = rescue_gadget.squeeze_out_single(
                &mut cs,
                &params
            ).unwrap();

            assert_eq!(res_0.get_value().unwrap(), expected[0]);
            println!("Rescue stateful hash of {} elements taken {} constraints", input.len(), cs.n());

            let res_1 = rescue_gadget.squeeze_out_single(
                &mut cs,
                &params
            ).unwrap();

            let mut stateful_hasher = StatefulSponge::<Bn256>::new(
                &params
            );

            stateful_hasher.absorb(&input);

            let r0 = stateful_hasher.squeeze_out_single();
            let r1 = stateful_hasher.squeeze_out_single();

            assert_eq!(res_0.get_value().unwrap(), r0);
            assert_eq!(res_1.get_value().unwrap(), r1);

            cs.finalize();
            assert!(cs.is_satisfied());
        }
    }

    // #[test]
    // fn test_poseidon_hash_redshift_gadget() {
    //     use crate::bellman::plonk::better_better_cs::cs::{ConstraintSystem, Circuit};
    //     use crate::bellman::{SynthesisError};

    //     struct TestCircuit;

    //     const DEPTH: usize = 160*16;
    //     // const DEPTH: usize = 1;

    //     impl Circuit<Bn256> for TestCircuit {
    //         fn synthesize<CS: ConstraintSystem<Bn256>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
    //             let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
    //             let params = Bn256PoseidonParams::new_checked_2_into_1();
    //             let input: Vec<Fr> = (0..(params.rate())).map(|_| rng.gen()).collect();

    //             for _ in 0..DEPTH {
    //                 let input_words: Vec<AllocatedNum<Bn256>> = input.iter().enumerate().map(|(i, b)| {
    //                     AllocatedNum::alloc(
    //                         cs,
    //                         || {
    //                             Ok(*b)
    //                         }).unwrap()
    //                 }).collect();
        
    //                 let mut rescue_gadget = StatefulPoseidonGadget::<Bn256>::new(
    //                     &params
    //                 );
        
    //                 rescue_gadget.absorb(
    //                     cs,
    //                     &input_words, 
    //                     &params
    //                 )?;
        
    //                 let res_0 = rescue_gadget.squeeze_out_single(
    //                     cs,
    //                     &params
    //                 )?;

    //                 let res_1 = rescue_gadget.squeeze_out_single(
    //                     cs,
    //                     &params
    //                 )?;
    //             }

    //             Ok(())
    //         }
    //     }

    //     use crate::bellman::plonk::better_better_cs::cs_old::{prove_with_poseidon_bn256, prove_with_hash_counting_bn256};

    //     // let _ = prove_with_poseidon_bn256::<
    //     //     Width4WithCustomGates,
    //     //     Width4MainGateWithDNext,
    //     //     _
    //     // >(&TestCircuit).unwrap();

    //     let _ = prove_with_hash_counting_bn256::<
    //         Width4WithCustomGates,
    //         Width4MainGateWithDNext,
    //         _
    //     >(&TestCircuit).unwrap();
    // }
}