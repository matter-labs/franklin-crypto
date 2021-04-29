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

use super::boolean::{
    Boolean
};

use super::allocated_num::{
    AllocatedNum,
    Num
};

use super::linear_combination::{
    LinearCombination
};

use crate::rescue::{RescueEngine, RescueHashParams, RescueParamsInternal, SBox, QuinticSBox, PowerSBox};

use super::custom_rescue_gate::*;

use std::sync::atomic::{AtomicUsize, Ordering};

pub(crate) static RESCUE_COUNTER: AtomicUsize = AtomicUsize::new(0);

pub fn reset_counter() {
    RESCUE_COUNTER.store(0, Ordering::Relaxed);
}

pub fn increment_counter() {
    RESCUE_COUNTER.fetch_add(1, Ordering::SeqCst);
}

pub fn increment_counter_by(val: usize) {
    RESCUE_COUNTER.fetch_add(val, Ordering::SeqCst);
}

pub fn output_counter() -> usize {
    RESCUE_COUNTER.load(Ordering::Relaxed)
}

pub trait PlonkCsSBox<E: Engine>: SBox<E> {
    const SHOULD_APPLY_FORWARD: bool;
    fn apply_constraints<CS: ConstraintSystem<E>>(&self, cs: &mut CS, element: &Num<E>, force_no_custom_gates: bool) -> Result<Num<E>, SynthesisError>;
    fn apply_constraints_in_reverse<CS: ConstraintSystem<E>>(&self, cs: &mut CS, element: &Num<E>, force_no_custom_gates: bool) -> Result<Num<E>, SynthesisError>;
    // fn apply_constraints_assuming_next_row_placement<CS: ConstraintSystem<E>>(&self, cs: CS, element: &AllocatedNum<E>, force_no_custom_gates: bool) -> Result<AllocatedNum<E>, SynthesisError>;
}

impl<E: Engine> PlonkCsSBox<E> for QuinticSBox<E> {
    const SHOULD_APPLY_FORWARD: bool = true;

    fn apply_constraints<CS: ConstraintSystem<E>>(
        &self, 
        cs: &mut CS,
        el: &Num<E>,
        force_no_custom_gates: bool
    ) -> Result<Num<E>, SynthesisError> {        
        // we need state width of 4 to make custom gate
        if force_no_custom_gates == false && CS::Params::HAS_CUSTOM_GATES == true && CS::Params::STATE_WIDTH >= 4 {
            return self.apply_custom_gate(cs, el);
        }

        let ret = match el {
            Num::Constant(constant) => {
                let mut result = *constant;
                result.square();
                result.square();
                result.mul_assign(constant);

                Ok(Num::Constant(result))
            },
            Num::Variable(el) => {
                // we take a value and make 5th power from it
                let square = el.square(cs)?;
                let quad = square.square(cs)?;
                let fifth = quad.mul(cs, &el)?;

                Ok(Num::Variable(fifth))
            }
        };

        ret
    }

    fn apply_constraints_in_reverse<CS: ConstraintSystem<E>>(
        &self, 
        _cs: &mut CS,
        _el: &Num<E>,
        _force_no_custom_gates: bool
    ) -> Result<Num<E>, SynthesisError> {     
        unimplemented!("Making 5th power can only be used in straight order")
    }
}

impl<E: Engine> QuinticSBox<E> {
    fn apply_custom_gate<CS: ConstraintSystem<E>>(
        &self, 
        cs: &mut CS,
        el: &Num<E>,
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
                let out = apply_5th_power(cs, el, None)?;

                Ok(Num::Variable(out))
            }
        }
    }
}

impl<E: Engine> PlonkCsSBox<E> for PowerSBox<E> {
    const SHOULD_APPLY_FORWARD: bool = false;

    fn apply_constraints_in_reverse<CS: ConstraintSystem<E>>(
        &self, 
        cs: &mut CS,
        el: &Num<E>,
        force_no_custom_gates: bool
    ) -> Result<Num<E>, SynthesisError> {        
        // we need state width of 4 to make custom gate
        if force_no_custom_gates == false && CS::Params::HAS_CUSTOM_GATES == true && CS::Params::STATE_WIDTH >= 4 {
            return self.apply_custom_gate(cs, el);
        }

        let ret = match el {
            Num::Constant(constant) => {
                let result = constant.pow(&self.power);

                Ok(Num::Constant(result))
            },
            Num::Variable(el) => {
                let out = AllocatedNum::<E>::alloc(
                    cs,
                    || {
                        let base = *el.get_value().get()?;
                        let result = base.pow(&self.power);

                        Ok(result)
                    }
                )?;

                // we take a value and make 5th power from it
                let square = out.square(cs)?;
                let quad = square.square(cs)?;

                let mut term = MainGateTerm::<E>::new();
                let fifth_term = ArithmeticTerm::from_variable(quad.get_variable()).mul_by_variable(out.get_variable());
                let el_term = ArithmeticTerm::from_variable(el.get_variable());
                term.add_assign(fifth_term);
                term.sub_assign(el_term);
                cs.allocate_main_gate(term)?;

                Ok(Num::Variable(out))
            }
        };

        ret
    }

    fn apply_constraints<CS: ConstraintSystem<E>>(
        &self, 
        _cs: &mut CS,
        _el: &Num<E>,
        _force_no_custom_gates: bool
    ) -> Result<Num<E>, SynthesisError> {     
        unimplemented!("Making inverse of 5th power can only be used in backward mode")
    }
}

impl<E: Engine> PowerSBox<E> {
    fn apply_custom_gate<CS: ConstraintSystem<E>>(
        &self, 
        cs: &mut CS,
        el: &Num<E>,
    ) -> Result<Num<E>, SynthesisError> {
        match el {
            Num::Constant(constant) => {
                let result = constant.pow(&self.power);

                Ok(Num::Constant(result))
            },
            Num::Variable(el) => {
                // manually make a large power
                let out = AllocatedNum::<E>::alloc(
                    cs,
                    || {
                        let base = *el.get_value().get()?;
                        let result = base.pow(&self.power);

                        Ok(result)
                    }
                )?;
                
                // now we need to make sure that 5th power of base is equal to 
                // the original value
                let _ = apply_5th_power(cs, &out, Some(el.clone()))?;

                Ok(Num::Variable(out))
            }
        }
    }
}

#[derive(Clone, Debug)]
enum RescueOpMode<E: RescueEngine> {
    AccumulatingToAbsorb(Vec<Num<E>>),
    SqueezedInto(Vec<LinearCombination<E>>)
}

#[derive(Clone, Debug)]
pub struct StatefulRescueGadget<E: RescueEngine> {
    internal_state: Vec<LinearCombination<E>>,
    mode: RescueOpMode<E>
}

pub fn rescue_hash<E: RescueEngine, CS: ConstraintSystem<E>>(cs: &mut CS, params: &E::Params, input: &[Num<E>]) -> Result<Vec<Num<E>>, SynthesisError> 
   where <<E as RescueEngine>::Params as RescueHashParams<E>>::SBox0: PlonkCsSBox<E>, 
    <<E as RescueEngine>::Params as RescueHashParams<E>>::SBox1: PlonkCsSBox<E>
{
    let before = cs.get_current_step_number();
    let mut rescue_gadget = StatefulRescueGadget::<E>::new(
        &params
    );

    rescue_gadget.specizalize(input.len() as u8);

    rescue_gadget.absorb_nums(
        cs,
        &input, 
        &params
    )?;

    rescue_gadget.pad_if_necessary(&params)?;

    let mut result = vec![];
    for _ in 0..params.rate() {
        let res_lc = rescue_gadget.squeeze_out_single(
            cs,
            &params
        )?;

        let res = res_lc.into_num(cs)?;

        result.push(res);
    }

    increment_counter_by(cs.get_current_step_number() - before);

    Ok(result)
}

impl<E: RescueEngine> StatefulRescueGadget<E> 
    where <<E as RescueEngine>::Params as RescueHashParams<E>>::SBox0: PlonkCsSBox<E>, 
    <<E as RescueEngine>::Params as RescueHashParams<E>>::SBox1: PlonkCsSBox<E>
{
    pub fn new(
        params: &E::Params
    ) -> Self {
        let op = RescueOpMode::AccumulatingToAbsorb(Vec::with_capacity(params.rate() as usize));

        Self {
            internal_state: vec![LinearCombination::<E>::zero(); params.state_width() as usize],
            mode: op
        }
    }

    // pub fn conditionally_select<CS: ConstraintSystem<E>>(
    //     cs: &mut CS,
    //     flag: &Boolean,
    //     first: &Self,
    //     second: &Self,
    //     params: &E::Params
    // ) -> Result<Self, SynthesisError> {
    //     unreachable!("Not yet valid");
    //     match (&first.mode, &second.mode) {
    //         (RescueOpMode::AccumulatingToAbsorb(first_buffer), RescueOpMode::AccumulatingToAbsorb(second_buffer)) => {
    //             let mut first_buffer = first_buffer.clone();
    //             let mut second_buffer = second_buffer.clone();
    //             let padding_element = Num::Constant(E::Fr::one());

    //             first_buffer.resize(params.rate() as usize, padding_element.clone());
    //             second_buffer.resize(params.rate() as usize, padding_element.clone());

    //             let mut selected_buffer = vec![];
    //             for i in 0..(params.rate() as usize) {
    //                 let selected = Num::conditionally_select(cs, flag, &first_buffer[i], &second_buffer[i])?;
    //                 selected_buffer.push(selected);
    //             }

    //             let selected_internal_state = vec![];
    //             for (a, b) in first.internal_state.iter().zip(second.internal_state.iter()) {
    //                 let a = a.into_num(cs)?;
    //                 let b = b.into_num(cs)?;
    //                 let selected = Num::conditionally_select(cs, flag, &a, &b)?;
    //                 let mut lc = LinearCombination::zero();
    //                 lc.add_assign_number_with_coeff(&selected, E::Fr::one());
    //                 selected_internal_state.push(lc);
    //             }

    //             let selected = Self {
    //                 internal_state: selected_internal_state,
    //                 mode: RescueOpMode::AccumulatingToAbsorb(selected_buffer)
    //             };

    //             Ok(selected)
    //         }
    //         (RescueOpMode::SqueezedInto(..), RescueOpMode::SqueezedInto(..)) => {
    //             todo!();
    //         },
    //         _ => {
    //             assert!(false, "opmodes are different");
    //         }
    //     }
    // }


    pub fn rescue_mimc_over_nums<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        state: &[Num<E>],
        params: &E::Params
    ) -> Result<Vec<Num<E>>, SynthesisError> {
        let state: Vec<_> = state.iter().map(|el| LinearCombination::from(*el)).collect();
        let out_lcs = Self::rescue_mimc_over_lcs(
            cs,
            &state,
            &params
        )?;
        let mut out = vec![];
        for lc in out_lcs.into_iter() {
            let as_num = lc.into_num(cs)?;
            out.push(as_num);
        }

        Ok(out)
    }

    pub fn rescue_mimc_over_lcs<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        state: &[LinearCombination<E>],
        params: &E::Params
    ) -> Result<Vec<LinearCombination<E>>, SynthesisError> {
        let state_len = state.len();
        assert_eq!(state_len, params.state_width() as usize);
        let mut state = Some(state.to_vec());
        // unwrap first round manually
        let round_constants = params.round_constants(0);
        for (idx, s) in state.as_mut().unwrap().iter_mut().enumerate() {
            s.add_assign_constant(round_constants[idx]);
        }

        let force_no_custom_gates = !params.can_use_custom_gates();

        for round in 0..(params.num_rounds() * 2) {
            let mut after_nonlin = Vec::with_capacity(state_len);

            for (_idx, s) in state.take().unwrap().into_iter().enumerate() {
                let input = s.into_num(cs)?;
                let state_output = if round & 1 == 0 {
                    let sbox = params.sbox_0();
                    let output = if <<<E as RescueEngine>::Params as RescueHashParams<E>>::SBox0 as PlonkCsSBox<E>>::SHOULD_APPLY_FORWARD {
                        sbox.apply_constraints(cs, &input, force_no_custom_gates)?
                    } else {
                        sbox.apply_constraints_in_reverse(cs, &input, force_no_custom_gates)?
                    };

                    output
                } else {
                    let sbox = params.sbox_1();
                    let output = if <<<E as RescueEngine>::Params as RescueHashParams<E>>::SBox1 as PlonkCsSBox<E>>::SHOULD_APPLY_FORWARD {
                        sbox.apply_constraints(cs, &input, force_no_custom_gates)?
                    } else {
                        sbox.apply_constraints_in_reverse(cs, &input, force_no_custom_gates)?
                    };

                    output
                };

                after_nonlin.push(state_output);
            }

            // apply MDS and round constants

            let mut new_state = Vec::with_capacity(state_len);

            let round_constants = params.round_constants(round + 1u32);
            for i in 0..state_len {
                let mut lc = LinearCombination::<E>::zero();
                let mds_row = params.mds_matrix_row(i as u32);

                for (s, coeff) in after_nonlin.iter().zip(mds_row.iter()){
                    lc.add_assign_number_with_coeff(s, *coeff);
                }
                lc.add_assign_constant(round_constants[i]);

                new_state.push(lc);
            }

            state = Some(new_state);
        }

        Ok(state.unwrap())
    }

    #[track_caller]
    pub fn specizalize(
        &mut self,
        dst: u8
    ) {
        assert!(dst > 0);
        match self.mode {
            RescueOpMode::AccumulatingToAbsorb(ref into) => {
                assert_eq!(into.len(), 0, "can not specialize sponge that absorbed something")
            },
            _ => {
                panic!("can not specialized sponge in squeezing state");
            }
        }
        let dst = dst as u64;
        let mut repr = <E::Fr as PrimeField>::Repr::default();
        repr.as_mut()[0] = dst;
        let as_fe = <E::Fr as PrimeField>::from_repr(repr).unwrap();
        let last_state_elem_idx = self.internal_state.len() - 1;
        self.internal_state[last_state_elem_idx].add_assign_constant(as_fe)
    }

    pub fn absorb_single_value<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        value: Num<E>,
        params: &E::Params
    ) -> Result<(), SynthesisError> {
        let before = cs.get_current_step_number();

        match self.mode {
            RescueOpMode::AccumulatingToAbsorb(ref mut into) => {
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

                    self.internal_state = Self::rescue_mimc_over_lcs(
                        cs,
                        &self.internal_state, 
                        &params
                    )?;

                    into.truncate(0);
                    into.push(value.clone());
                }
            },
            RescueOpMode::SqueezedInto(_) => {
                // we don't need anything from the output, so it's dropped

                let mut s = Vec::with_capacity(params.rate() as usize);
                s.push(value);

                let op = RescueOpMode::AccumulatingToAbsorb(s);
                self.mode = op;
            }
        }

        increment_counter_by(cs.get_current_step_number() - before);

        Ok(())
    }

    pub fn absorb<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        input: &[AllocatedNum<E>],
        params: &E::Params
    ) -> Result<(), SynthesisError>{
        let before = cs.get_current_step_number();

        let absorbtion_len = params.rate() as usize;
    
        assert!(input.len() > 0);
        let mut absorbtion_cycles = input.len() / absorbtion_len;
        if input.len() % absorbtion_len != 0 {
            absorbtion_cycles += 1;
        }

        let mut input: Vec<_> = input.iter().map(|el| Num::Variable(el.clone())).collect();
        input.resize(absorbtion_cycles * absorbtion_len, Num::Constant(E::Fr::one()));
    
        let it = input.into_iter();
        
        for (_idx, val) in it.enumerate() {
            self.absorb_single_value(
                cs,
                val,
                &params
            )?;
        }

        increment_counter_by(cs.get_current_step_number() - before);

        Ok(())
    }

    pub fn absorb_nums<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        input: &[Num<E>],
        params: &E::Params
    ) -> Result<(), SynthesisError>{
        let before = cs.get_current_step_number();

        let absorbtion_len = params.rate() as usize;
    
        assert!(input.len() > 0);
        let mut absorbtion_cycles = input.len() / absorbtion_len;
        if input.len() % absorbtion_len != 0 {
            absorbtion_cycles += 1;
        }

        let mut input: Vec<_> = input.to_vec();
        input.resize(absorbtion_cycles * absorbtion_len, Num::Constant(E::Fr::one()));
    
        let it = input.into_iter();
        
        for (_idx, val) in it.enumerate() {
            self.absorb_single_value(
                cs,
                val,
                &params
            )?;
        }

        increment_counter_by(cs.get_current_step_number() - before);

        Ok(())
    }

    pub fn squeeze_out_single<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        params: &E::Params
    ) -> Result<LinearCombination<E>, SynthesisError> {
        let before = cs.get_current_step_number();
        
        match self.mode {
            RescueOpMode::AccumulatingToAbsorb(ref mut into) => {
                let rate = params.rate() as usize;
                assert_eq!(into.len(), rate, "padding was necessary!");
                // two cases
                // either we have accumulated enough already and should to 
                // a mimc round before accumulating more, or just accumulate more
                for i in 0..rate {
                    self.internal_state[i].add_assign_number_with_coeff(&into[i], E::Fr::one());
                }

                self.internal_state = Self::rescue_mimc_over_lcs(
                    cs,
                    &self.internal_state, 
                    &params
                )?;

                // we don't take full internal state, but only the rate
                let mut sponge_output = self.internal_state[0..rate].to_vec();
                let output = sponge_output.drain(0..1).next().expect("squeezed sponge must contain some data left");

                let op = RescueOpMode::SqueezedInto(sponge_output);
                self.mode = op;

                increment_counter_by(cs.get_current_step_number() - before);

                return Ok(output);
            },
            RescueOpMode::SqueezedInto(ref mut into) => {
                assert!(into.len() > 0, "squeezed state is depleted!");
                let output = into.drain(0..1).next().expect("squeezed sponge must contain some data left");

                increment_counter_by(cs.get_current_step_number() - before);
                
                return Ok(output);
            }
        }
    }

    pub fn pad_if_necessary(
        &mut self,
        params: &E::Params
    ) -> Result<(), SynthesisError> {
        match self.mode {
            RescueOpMode::AccumulatingToAbsorb(ref mut into) => {
                let rate = params.rate() as usize;
                if into.len() != rate {
                    into.resize(rate, Num::Constant(E::Fr::one()));
                };
            },
            RescueOpMode::SqueezedInto(..) => {
                // do nothing
                // panic!("Can not call padding on a squeezed sponge");
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use rand::{SeedableRng, Rng, XorShiftRng};
    use super::*;
    use bellman::pairing::bn256::{Bn256, Fr};
    use bellman::pairing::ff::PrimeField;
    use crate::rescue;
    use crate::bellman::plonk::better_better_cs::cs::{
        TrivialAssembly, 
        PlonkCsWidth4WithNextStepParams, 
        Width4MainGateWithDNext
    };

    use crate::plonk::circuit::Width4WithCustomGates;

    #[test]
    fn test_rescue_hash_plonk_gadget() {
        use crate::rescue::bn256::*;
        let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        let params = Bn256RescueParams::new_checked_2_into_1();
        let input: Vec<Fr> = (0..(params.rate())).map(|_| rng.gen()).collect();
        // let input: Vec<Fr> = (0..(params.rate()+1)).map(|_| rng.gen()).collect();
        let expected = rescue::rescue_hash::<Bn256>(&params, &input[..]);

        {
            let mut cs = TrivialAssembly::<Bn256, 
                Width4WithCustomGates,
                Width4MainGateWithDNext
            >::new();

            let input_words: Vec<AllocatedNum<Bn256>> = input.iter().enumerate().map(|(_i, b)| {
                AllocatedNum::alloc(
                    &mut cs,
                    || {
                        Ok(*b)
                    }).unwrap()
            }).collect();

            let mut rescue_gadget = StatefulRescueGadget::<Bn256>::new(
                &params
            );

            rescue_gadget.specizalize(input_words.len() as u8);

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

            let mut stateful_hasher = rescue::StatefulRescue::<Bn256>::new(
                &params
            );

            stateful_hasher.specialize(input.len() as u8);

            stateful_hasher.absorb(&input);

            let r0 = stateful_hasher.squeeze_out_single();
            let r1 = stateful_hasher.squeeze_out_single();

            assert_eq!(res_0.get_value().unwrap(), r0);
            assert_eq!(res_1.get_value().unwrap(), r1);

            cs.finalize();
            assert!(cs.is_satisfied());
        }
    }

    #[test]
    fn test_rescue_hash_plonk_no_custom_gates() {
        use crate::rescue::bn256::*;
        let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        let params = Bn256RescueParams::new_checked_2_into_1();
        let input: Vec<Fr> = (0..(params.rate())).map(|_| rng.gen()).collect();
        // let input: Vec<Fr> = (0..(params.rate()+1)).map(|_| rng.gen()).collect();
        let expected = rescue::rescue_hash::<Bn256>(&params, &input[..]);

        {
            let mut cs = TrivialAssembly::<Bn256, 
                PlonkCsWidth4WithNextStepParams,
                Width4MainGateWithDNext
            >::new();

            let input_words: Vec<AllocatedNum<Bn256>> = input.iter().enumerate().map(|(_i, b)| {
                AllocatedNum::alloc(
                    &mut cs,
                    || {
                        Ok(*b)
                    }).unwrap()
            }).collect();

            let mut rescue_gadget = StatefulRescueGadget::<Bn256>::new(
                &params
            );

            rescue_gadget.specizalize(input_words.len() as u8);

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

            let mut stateful_hasher = rescue::StatefulRescue::<Bn256>::new(
                &params
            );

            stateful_hasher.specialize(input.len() as u8);

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
    // fn test_rescue_hash_redshift_gadget() {
    //     use crate::rescue::bn256::*;
    //     use crate::bellman::plonk::better_better_cs::cs::{ConstraintSystem, Circuit};
    //     use crate::bellman::{SynthesisError};

    //     struct TestCircuit;

    //     const DEPTH: usize = 32;

    //     impl Circuit<Bn256> for TestCircuit {
    //         fn synthesize<CS: ConstraintSystem<Bn256>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
    //             let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
    //             let params = Bn256RescueParams::new_checked_2_into_1();
    //             let input: Vec<Fr> = (0..(params.rate())).map(|_| rng.gen()).collect();

    //             for _ in 0..DEPTH {
    //                 let input_words: Vec<AllocatedNum<Bn256>> = input.iter().enumerate().map(|(i, b)| {
    //                     AllocatedNum::alloc(
    //                         cs,
    //                         || {
    //                             Ok(*b)
    //                         }).unwrap()
    //                 }).collect();
        
    //                 let mut rescue_gadget = StatefulRescueGadget::<Bn256>::new(
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

    //     use crate::bellman::plonk::better_better_cs::cs::prove_with_rescue_bn256;

    //     let _ = prove_with_rescue_bn256::<
    //         Width4WithCustomGates,
    //         Width4MainGateWithDNext,
    //         _
    //     >(&TestCircuit).unwrap();
    // }
}