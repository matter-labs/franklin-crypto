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
    MainGateTerm
};

use crate::circuit::{
    Assignment
};

use super::allocated_num::{
    AllocatedNum
};

#[derive(Debug)]
pub struct LinearCombination<E: Engine> {
    pub(crate) value: Option<E::Fr>,
    pub(crate) terms: Vec<(E::Fr, Variable)>,
    pub(crate) constant: E::Fr
}

impl<E: Engine> From<AllocatedNum<E>> for LinearCombination<E> {
    fn from(num: AllocatedNum<E>) -> LinearCombination<E> {
        Self {
            value: num.value,
            terms: vec![(E::Fr::one(), num.variable)],
            constant: E::Fr::zero()
        }
    }
}

impl<E: Engine> Clone for LinearCombination<E> {
    fn clone(&self) -> Self {
        Self {
            value: self.value,
            terms: self.terms.clone(),
            constant: self.constant,
        }
    }
}

impl<E: Engine> LinearCombination<E> {
    pub fn zero() -> Self {
        Self {
            value: Some(E::Fr::zero()),
            terms: vec![],
            constant: E::Fr::zero(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.terms.len() == 0
    }

    pub fn len(&self) -> usize {
        self.terms.len()
    }

    pub fn get_value(&self) -> Option<E::Fr> {
        self.value
    }

    pub fn scale(
        &mut self,
        coeff: &E::Fr
    ) {
        if let Some(ref val) = self.value.as_mut() {
            val.mul_assign(&coeff);
        }

        for (c, _) in self.terms.iter_mut() {
            c.mul_assign(&coeff);
        }

        self.constant.mul_assign(&coeff);
    }

    // pub fn add_number_with_coeff(
    //     self,
    //     variable: &AllocatedNum<E>,
    //     coeff: E::Fr
    // ) -> Self
    // {
    //     let newval = match (self.value, variable.get_value()) {
    //         (Some(mut curval), Some(val)) => {
    //             let mut tmp = val;
    //             tmp.mul_assign(&coeff);

    //             curval.add_assign(&tmp);

    //             Some(curval)
    //         },
    //         _ => None
    //     };

    //     let mut terms = self.terms;

    //     terms.push((coeff, variable.variable));

    //     Self {
    //         value: newval,
    //         terms,
    //         constant: self.constant
    //     }
    // }

    pub fn add_assign_number_with_coeff(
        &mut self,
        variable: &AllocatedNum<E>,
        coeff: E::Fr
    )
    {
        let newval = match (self.value, variable.get_value()) {
            (Some(mut curval), Some(val)) => {
                let mut tmp = val;
                tmp.mul_assign(&coeff);

                curval.add_assign(&tmp);

                Some(curval)
            },
            _ => None
        };

        self.value = newval;
        self.terms.push((coeff, variable.variable));
    }
   
    // pub fn add_assign_bool_with_coeff(
    //     self,
    //     bit: &Boolean,
    //     coeff: E::Fr
    // ) -> Self
    // {
    //     let newval = match (self.value, bit.get_value()) {
    //         (Some(mut curval), Some(bval)) => {
    //             if bval {
    //                 curval.add_assign(&coeff);
    //             }

    //             Some(curval)
    //         },
    //         _ => None
    //     };

    //     Num {
    //         value: newval,
    //         lc: self.lc + &bit.lc(one, coeff)
    //     }
    // }

    pub fn add_assign_constant(
        &mut self,
        coeff: E::Fr
    )
    {
        let newval = match self.value {
            Some(mut curval) => {
                curval.add_assign(&coeff);

                Some(curval)
            },
            _ => None
        };

        self.constant.add_assign(&coeff);
    }

    pub fn into_allocated_num<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS
    ) -> Result<AllocatedNum<E>, SynthesisError> {
        let may_be_trivial = self.unwrap_as_allocated_num();
        if may_be_trivial.is_ok() {
            return may_be_trivial;
        }

        // manually transpile into chain of gates

        let final_var = AllocatedNum::alloc(
            cs,
            || {
                Ok(*self.value.get()?)
            }
        )?;

        let mut minus_one = E::Fr::one();
        minus_one.negate();

        let mut terms = self.terms;
        terms.push((minus_one, final_var.variable));

        // we do this to 
        let terms = Self::deduplicate_stable(terms);

        // do the chunking

        use crate::bellman::plonk::better_better_cs::cs::PlonkConstraintSystemParams;

        if CS::Params::CAN_ACCESS_NEXT_TRACE_STEP {

        } else {
            unimplemented!()
        }

        Ok(final_var)
    }

    fn deduplicate_stable(
        terms: Vec<(E::Fr, Variable)>,
    ) -> Vec<(E::Fr, Variable)> {
        use std::collections::HashMap;

        if terms.len() <= 1 {
            return terms;
        }

        let mut scratch: HashMap<Variable, usize> = HashMap::with_capacity(terms.len());
    
        let mut deduped_vec: Vec<(E::Fr, Variable)> = Vec::with_capacity(terms.len());
    
        for (coeff, var) in terms.into_iter() {
            if let Some(existing_index) = scratch.get(&var) {
                let (c, _) = &mut deduped_vec[*existing_index];
                c.add_assign(&coeff);
            } else {
                let new_idx = deduped_vec.len();
                deduped_vec.push((coeff, var));
                scratch.insert(var, new_idx);
            }
        }
    
        deduped_vec = deduped_vec.into_iter().filter(|(coeff, _)| !coeff.is_zero()).collect();
    
        deduped_vec
    }

    fn inscribe_using_next_step<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        mut terms: Vec<(E::Fr, Variable)>,
        constant_term: E::Fr
    ) -> Result<(), SynthesisError> {
        // we assume that terms are deduplicated

        let zero_fr = E::Fr::zero();
        let one_fr = E::Fr::one();
        let mut minus_one_fr = E::Fr::one();
        minus_one_fr.negate();

        // trivial case - single variable

        assert!(terms.len() > 0);

        let num_terms = terms.len();

        // we have two options: 
        // - fit everything into a single gate (in case of number terms in the linear combination
        // smaller than a width of the state)
        // - make a required number of extra variables and chain it

        use crate::bellman::plonk::better_better_cs::cs::PlonkConstraintSystemParams;
        
        if num_terms <= CS::Params::STATE_WIDTH {
            // we can just make a single gate

            let mut gate_term = MainGateTerm::new();

            for (c, var) in terms.into_iter() {
                let t = ArithmeticTerm::from_variable_and_coeff(var, c);
                gate_term.add_assign(t);
            }

            let t = ArithmeticTerm::constant(constant_term);
            gate_term.add_assign(t);

            cs.allocate_main_gate(gate_term)?;

            return Ok(());
        } else {
            // we can take:
            // - STATE_WIDTH variables to form the first gate and place their sum into the last wire of the next gate
            // - every time take STATE_WIDTH-1 variables and place their sum + last wire into the next gate last wire

            // we have also made a final variable already, so there is NO difference
            let cycles = ((terms.len() - CS::Params::STATE_WIDTH) + (CS::Params::STATE_WIDTH - 2)) / (CS::Params::STATE_WIDTH - 1); // ceil 
            let mut it = terms.into_iter();

            // this is a placeholder variable that must go into the 
            // corresponding trace polynomial at the NEXT time step 
            let mut next_step_var_in_chain = {



                scratch_space.scratch_space_for_vars.resize(P::STATE_WIDTH, cs.get_dummy_variable());
                scratch_space.scratch_space_for_booleans.resize(P::STATE_WIDTH, false);
                scratch_space.scratch_space_for_coeffs.resize(P::STATE_WIDTH, zero_fr);
        
                // we can consume and never have leftovers
        
                let mut idx = 0;
                for (var, coeff) in &mut it {
                    if scratch_space.scratch_space_for_booleans[idx] == false {
                        scratch_space.scratch_space_for_booleans[idx] = true;
                        scratch_space.scratch_space_for_coeffs[idx] = coeff;
                        scratch_space.scratch_space_for_vars[idx] = convert_variable(var);
                        idx += 1;
                        if idx == P::STATE_WIDTH {
                            break;
                        }
                    }
                }

                // for a P::STATE_WIDTH variables we make a corresponding LC
                // ~ a + b + c + d + constant. That will be equal to d_next
                let may_be_new_intermediate_value = evaluate_over_plonk_variables_and_coeffs::<E, P, CS>(
                    &*cs,
                    &*scratch_space.scratch_space_for_vars,
                    &*scratch_space.scratch_space_for_coeffs, 
                    free_term_constant
                );

                // we manually allocate the new variable
                let new_intermediate_var = cs.alloc(|| {
                    may_be_new_intermediate_value
                })?;

                // no multiplication coefficient,
                // but -1 to link to the next trace step (we enforce == 0)
                scratch_space.scratch_space_for_coeffs.push(zero_fr); // no multiplication
                scratch_space.scratch_space_for_coeffs.push(free_term_constant); // add constant
                scratch_space.scratch_space_for_coeffs.push(minus_one_fr); // -1 for a d_next

                allocate_into_cs(
                    cs, 
                    true, 
                    &*scratch_space.scratch_space_for_vars, 
                    &*scratch_space.scratch_space_for_coeffs
                )?;

                scratch_space.clear();

                new_intermediate_var
            };

            // run over the rest

            // we can only take one less cause 
            // we've already used one of the variable
            let consume_from_lc = CS::Params::STATE_WIDTH - 1; 
            for _ in 0..(cycles-1) {
                scratch_space.scratch_space_for_vars.resize(consume_from_lc, cs.get_dummy_variable());
                scratch_space.scratch_space_for_booleans.resize(consume_from_lc, false);
                scratch_space.scratch_space_for_coeffs.resize(consume_from_lc, zero_fr);
        
                // we can consume and never have leftovers
        
                let mut idx = 0;
                for (var, coeff) in &mut it {
                    if scratch_space.scratch_space_for_booleans[idx] == false {
                        scratch_space.scratch_space_for_booleans[idx] = true;
                        scratch_space.scratch_space_for_coeffs[idx] = coeff;
                        scratch_space.scratch_space_for_vars[idx] = convert_variable(var);
                        idx += 1;
                        if idx == consume_from_lc {
                            break;
                        }
                    }
                }

                // push +1 and the allocated variable from the previous step

                scratch_space.scratch_space_for_coeffs.push(one_fr);
                scratch_space.scratch_space_for_vars.push(next_step_var_in_chain);

                let may_be_new_intermediate_value = evaluate_over_plonk_variables_and_coeffs::<E, P, CS>(
                    &*cs,
                    &*scratch_space.scratch_space_for_vars,
                    &*scratch_space.scratch_space_for_coeffs, 
                    zero_fr
                );

                let new_intermediate_var = cs.alloc(|| {
                    may_be_new_intermediate_value
                })?;

                // no multiplication coefficient and no constant now,
                // but -1 to link to the next trace step
                scratch_space.scratch_space_for_coeffs.push(zero_fr);
                scratch_space.scratch_space_for_coeffs.push(zero_fr);
                scratch_space.scratch_space_for_coeffs.push(minus_one_fr);

                allocate_into_cs(
                    cs, 
                    true, 
                    &*scratch_space.scratch_space_for_vars, 
                    &*scratch_space.scratch_space_for_coeffs
                )?;

                scratch_space.clear();

                next_step_var_in_chain = new_intermediate_var;
            }

            // final step - we just make a single gate, last one
            {
                scratch_space.scratch_space_for_vars.resize(P::STATE_WIDTH-1, cs.get_dummy_variable());
                scratch_space.scratch_space_for_booleans.resize(P::STATE_WIDTH-1, false);
                scratch_space.scratch_space_for_coeffs.resize(P::STATE_WIDTH-1, zero_fr);
        
                // we can consume and never have leftovers
        
                let mut idx = 0;
                for (var, coeff) in &mut it {
                    if scratch_space.scratch_space_for_booleans[idx] == false {
                        scratch_space.scratch_space_for_booleans[idx] = true;
                        scratch_space.scratch_space_for_coeffs[idx] = coeff;
                        scratch_space.scratch_space_for_vars[idx] = convert_variable(var);
                        idx += 1;
                    }
                }

                assert!(idx < P::STATE_WIDTH);
                // append d_next
                scratch_space.scratch_space_for_vars.push(next_step_var_in_chain);
                scratch_space.scratch_space_for_coeffs.push(one_fr);

                // no multiplication coefficient, no constant, no next step
                scratch_space.scratch_space_for_coeffs.push(zero_fr);
                scratch_space.scratch_space_for_coeffs.push(zero_fr);
                scratch_space.scratch_space_for_coeffs.push(zero_fr);

                allocate_into_cs(
                    cs, 
                    false, 
                    &*scratch_space.scratch_space_for_vars, 
                    &*scratch_space.scratch_space_for_coeffs
                )?;

                scratch_space.clear();
            }

            assert!(it.next().is_none());
        
    }

    pub fn unwrap_as_allocated_num(
        &self,
    ) -> Result<AllocatedNum<E>, SynthesisError> {
        if self.constant.is_zero() == false {
            return Err(SynthesisError::Unsatisfiable);
        }
        if self.terms.len() == 1 && self.terms[0].0 == E::Fr::one() {
            let var = (&self.terms[0].1).clone();
            let var = AllocatedNum {
                value: self.value,
                variable: var
            };

            return Ok(var);
        }

        return Err(SynthesisError::Unsatisfiable);
    }
}