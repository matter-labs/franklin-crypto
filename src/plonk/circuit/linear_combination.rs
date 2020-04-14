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
    AllocatedNum,
    Num
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
        if let Some(ref mut val) = self.value.as_mut() {
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
        number: &Num<E>,
        coeff: E::Fr
    ) {
        match number {
            Num::Variable(ref allocated_number) => {
                self.add_assign_variable_with_coeff(allocated_number, coeff);
            },
            Num::Constant(constant) => {
                let mut res = coeff;
                res.mul_assign(&constant);

                self.add_assign_constant(res);
            } 
        }
    }

    pub fn add_assign_variable_with_coeff(
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
            None => {
                Some(coeff)
            }
            // _ => None
        };

        self.value = newval;
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
            Self::inscribe_using_next_step(
                cs,
                terms,
                self.constant
            )?;
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

    fn evaluate_term_value<CS: ConstraintSystem<E>>(
        cs: &CS,
        terms: &[(E::Fr, Variable)],
        constant: E::Fr,
    ) -> Result<E::Fr, SynthesisError> {
        let mut result = constant;
        for (c, v) in terms.iter() {
            let mut tmp = cs.get_value(*v)?;
            tmp.mul_assign(&c);
            result.add_assign(&tmp);
        }

        Ok(result)
    }

    fn inscribe_using_next_step<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        terms: Vec<(E::Fr, Variable)>,
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
        } else {
            // we can take:
            // - STATE_WIDTH variables to form the first gate and place their sum into the last wire of the next gate
            // - every time take STATE_WIDTH-1 variables and place their sum + last wire into the next gate last wire

            // we have also made a final variable already, so there is NO difference
            let cycles = ((terms.len() - CS::Params::STATE_WIDTH) + (CS::Params::STATE_WIDTH - 2)) / (CS::Params::STATE_WIDTH - 1); // ceil 
            let mut it = terms.into_iter();

            use crate::bellman::plonk::better_better_cs::cs::{GateEquation, MainGateEquation};

            let next_term_range = CS::MainGate::range_of_next_step_linear_terms();

            // this is a placeholder variable that must go into the 
            // corresponding trace polynomial at the NEXT time step 
            let mut next_step_var_in_chain = {
                let chunk: Vec<_> = (&mut it).take(CS::Params::STATE_WIDTH).collect();
                let may_be_new_intermediate_value = Self::evaluate_term_value(
                    &*cs, 
                    &chunk, 
                    constant_term
                );

                // we manually allocate the new variable
                let new_intermediate_var = cs.alloc(|| {
                    may_be_new_intermediate_value
                })?;

                let mut gate_term = MainGateTerm::<E>::new();

                for (c, var) in chunk.into_iter() {
                    let t = ArithmeticTerm::from_variable_and_coeff(var, c);
                    gate_term.add_assign(t);
                }

                let t = ArithmeticTerm::constant(constant_term);
                gate_term.add_assign(t);

                let dummy = CS::get_dummy_variable();

                let (vars, mut coeffs) = CS::MainGate::format_term(gate_term, dummy)?;
                let idx = next_term_range.clone().next().expect("must give at least one index");
                coeffs[idx] = minus_one_fr;

                cs.new_single_gate_for_trace_step(
                    CS::MainGate::static_description(), 
                    &coeffs, 
                    &vars,
                    &[]
                )?;

                new_intermediate_var
            };

            // run over the rest

            // we can only take one less cause 
            // we've already used one of the variable
            let consume_from_lc = CS::Params::STATE_WIDTH - 1; 
            for _ in 0..(cycles-1) {
                let chunk: Vec<_> = (&mut it).take(CS::Params::STATE_WIDTH - 1).collect();
                let may_be_new_intermediate_value = Self::evaluate_term_value(
                    &*cs, 
                    &chunk, 
                    E::Fr::zero()
                );

                // we manually allocate the new variable
                let new_intermediate_var = cs.alloc(|| {
                    may_be_new_intermediate_value
                })?;

                let mut gate_term = MainGateTerm::<E>::new();

                for (c, var) in chunk.into_iter() {
                    let t = ArithmeticTerm::from_variable_and_coeff(var, c);
                    gate_term.add_assign(t);
                }

                let t = ArithmeticTerm::from_variable_and_coeff(next_step_var_in_chain, one_fr);
                gate_term.add_assign(t);

                let dummy = CS::get_dummy_variable();

                let (vars, mut coeffs) = CS::MainGate::format_term(gate_term, dummy)?;
                let idx = next_term_range.clone().next().expect("must give at least one index");
                coeffs[idx] = minus_one_fr;

                cs.new_single_gate_for_trace_step(
                    CS::MainGate::static_description(), 
                    &coeffs, 
                    &vars,
                    &[]
                )?;

                next_step_var_in_chain = new_intermediate_var;
            }

            // final step - we just make a single gate, last one
            {
                let chunk: Vec<_> = (&mut it).collect();
                assert!(chunk.len() <= CS::Params::STATE_WIDTH - 1);

                let mut gate_term = MainGateTerm::new();

                for (c, var) in chunk.into_iter() {
                    let t = ArithmeticTerm::from_variable_and_coeff(var, c);
                    gate_term.add_assign(t);
                }

                let t = ArithmeticTerm::from_variable_and_coeff(next_step_var_in_chain, one_fr);
                gate_term.add_assign(t);

                cs.allocate_main_gate(gate_term)?;
            }
            assert!(it.next().is_none());
        }

        Ok(())
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

#[cfg(test)]
mod test {
    use super::*;
    use crate::bellman::plonk::better_better_cs::cs::*;

    #[test]
    fn test_inscribe_linear_combination() {
        use crate::bellman::pairing::bn256::{Bn256, Fr};

        let mut assembly = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNextEquation>::new();
        let before = assembly.n;

        let variables: Vec<_> = (0..9).map(|_| AllocatedNum::alloc(
            &mut assembly, 
            || {
                Ok(Fr::one())
            }
        ).unwrap()).collect();

        let mut lc = LinearCombination::<Bn256>::zero();
        lc.add_assign_constant(Fr::one());
        let mut current = Fr::one();
        for v in variables.iter() {
            lc.add_assign_variable_with_coeff(v, current);
            current.double();
        }

        let result = lc.into_allocated_num(&mut assembly).unwrap();
        println!("result = {}", result.get_value().unwrap());

        assert!(assembly.constraints.len() == 1);
        assert_eq!(assembly.n, 3);
        // let num_gates = assembly.n - before;
        // println!("Single rescue r = 2, c = 1, alpha = 5 invocation takes {} gates", num_gates);

        // for (gate, density) in assembly.gate_density.0.into_iter() {
        //     println!("Custom gate {:?} selector = {:?}", gate, density);
        // }

        println!("Assembly state polys = {:?}", assembly.storage.state_map);

        println!("Assembly setup polys = {:?}", assembly.storage.setup_map);
    }
}