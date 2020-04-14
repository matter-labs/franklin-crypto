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

use crate::circuit::{
    Assignment
};

use super::allocated_num::{
    AllocatedNum,
    Num
};

use super::linear_combination::{
    LinearCombination
};

use crate::rescue::*;

use super::custom_rescue_gate::*;

pub trait PlonkCsSBox<E: Engine>: SBox<E> {
    const SHOULD_APPLY_FORWARD: bool;
    fn apply_constraints<CS: ConstraintSystem<E>>(&self, cs: &mut CS, element: &AllocatedNum<E>, force_no_custom_gates: bool) -> Result<AllocatedNum<E>, SynthesisError>;
    fn apply_constraints_in_reverse<CS: ConstraintSystem<E>>(&self, cs: &mut CS, element: &AllocatedNum<E>, force_no_custom_gates: bool) -> Result<AllocatedNum<E>, SynthesisError>;
    // fn apply_constraints_assuming_next_row_placement<CS: ConstraintSystem<E>>(&self, cs: CS, element: &AllocatedNum<E>, force_no_custom_gates: bool) -> Result<AllocatedNum<E>, SynthesisError>;
}

impl<E: Engine> PlonkCsSBox<E> for QuinticSBox<E> {
    const SHOULD_APPLY_FORWARD: bool = true;

    fn apply_constraints<CS: ConstraintSystem<E>>(
        &self, 
        cs: &mut CS,
        el: &AllocatedNum<E>,
        force_no_custom_gates: bool
    ) -> Result<AllocatedNum<E>, SynthesisError> {        
        // we need state width of 4 to make custom gate
        if force_no_custom_gates == false && CS::Params::HAS_CUSTOM_GATES == true && CS::Params::STATE_WIDTH >= 4 {
            return self.apply_custom_gate(cs, el);
        }

        unimplemented!()
    }

    fn apply_constraints_in_reverse<CS: ConstraintSystem<E>>(
        &self, 
        cs: &mut CS,
        el: &AllocatedNum<E>,
        force_no_custom_gates: bool
    ) -> Result<AllocatedNum<E>, SynthesisError> {     
        unimplemented!("Making 5th power can only be used in straight order")
    }
}

impl<E: Engine> QuinticSBox<E> {
    fn apply_custom_gate<CS: ConstraintSystem<E>>(
        &self, 
        cs: &mut CS,
        el: &AllocatedNum<E>,
    ) -> Result<AllocatedNum<E>, SynthesisError> {
        // we take a value and make 5th power from it
        apply_5th_power(cs, el, None)
    }
}

impl<E: Engine> PlonkCsSBox<E> for PowerSBox<E> {
    const SHOULD_APPLY_FORWARD: bool = false;

    fn apply_constraints_in_reverse<CS: ConstraintSystem<E>>(
        &self, 
        cs: &mut CS,
        el: &AllocatedNum<E>,
        force_no_custom_gates: bool
    ) -> Result<AllocatedNum<E>, SynthesisError> {        
        // we need state width of 4 to make custom gate
        if force_no_custom_gates == false && CS::Params::HAS_CUSTOM_GATES == true && CS::Params::STATE_WIDTH >= 4 {
            return self.apply_custom_gate(cs, el);
        }

        unimplemented!()
    }

    fn apply_constraints<CS: ConstraintSystem<E>>(
        &self, 
        cs: &mut CS,
        el: &AllocatedNum<E>,
        force_no_custom_gates: bool
    ) -> Result<AllocatedNum<E>, SynthesisError> {     
        unimplemented!("Making inverse of 5th power can only be used in backward mode")
    }
}

impl<E: Engine> PowerSBox<E> {
    fn apply_custom_gate<CS: ConstraintSystem<E>>(
        &self, 
        cs: &mut CS,
        el: &AllocatedNum<E>,
    ) -> Result<AllocatedNum<E>, SynthesisError> {
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

        Ok(out)
    }
}


enum RescueOpMode<E: RescueEngine> {
    AccumulatingToAbsorb(Vec<Num<E>>),
    SqueezedInto(Vec<LinearCombination<E>>)
}

pub struct StatefulRescueGadget<E: RescueEngine> {
    internal_state: Vec<LinearCombination<E>>,
    mode: RescueOpMode<E>
}

impl<E: RescueEngine> StatefulRescueGadget<E> {
    pub fn new(
        params: &E::Params
    ) -> Self {
        let op = RescueOpMode::AccumulatingToAbsorb(Vec::with_capacity(params.rate() as usize));

        Self {
            internal_state: vec![LinearCombination::<E>::zero(); params.state_width() as usize],
            mode: op
        }
    }

    fn rescue_mimc_over_lcs<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        state: &[LinearCombination<E>],
        params: &E::Params
    ) -> Result<Vec<LinearCombination<E>>, SynthesisError> {
        Err(SynthesisError::AssignmentMissing)
    }

    fn absorb_single_value<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        value: Num<E>,
        params: &E::Params
    ) -> Result<(), SynthesisError> {
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

                return Ok(output);
            },
            RescueOpMode::SqueezedInto(ref mut into) => {
                assert!(into.len() > 0, "squeezed state is depleted!");
                let output = into.drain(0..1).next().expect("squeezed sponge must contain some data left");

                return Ok(output);
            }
        }
    }
}