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

use super::boolean::{
    AllocatedBit,
    Boolean
};

use super::simple_term::Term;

pub struct LinearCombination<E: Engine> {
    pub(crate) value: Option<E::Fr>,
    pub(crate) terms: Vec<(E::Fr, Variable)>,
    pub(crate) constant: E::Fr
}

impl<E: Engine> std::fmt::Debug for LinearCombination<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LinearCombination")
            .field("value", &self.value)
            .field("number of terms", &self.terms.len())
            .field("terms", &self.terms)
            .field("constant", &self.constant)
            .finish()
    }
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
        if coeff.is_zero() {
            self.terms.truncate(0);
            self.constant = E::Fr::zero();
            self.value = Some(E::Fr::zero());
            return;
        }

        if let Some(ref mut val) = self.value.as_mut() {
            val.mul_assign(&coeff);
        }

        for (c, _) in self.terms.iter_mut() {
            c.mul_assign(&coeff);
        }

        self.constant.mul_assign(&coeff);
    }

    pub fn add_assign(
        &mut self,
        other: &Self,
    ) {
        let new_value = match (self.value, other.value) {
            (Some(this), Some(other)) => {
                let mut tmp = this;
                tmp.add_assign(&other);

                Some(tmp)
            },
            _ => None
        };
        self.value = new_value;

        self.terms.extend_from_slice(&other.terms);

        let terms = std::mem::replace(&mut self.terms, vec![]);

        self.terms = Self::deduplicate_stable(terms);

        self.constant.add_assign(&other.constant);
    }

    pub fn add_assign_scaled(
        &mut self,
        other: &Self,
        scale: E::Fr
    ) {
        let mut other_scaled = other.clone();
        other_scaled.scale(&scale);

        self.add_assign(&other_scaled);
    }

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
        if coeff.is_zero() {
            return;
        }

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

    pub fn add_assign_term(
        &mut self,
        term: &Term<E>
    )
    {
        if term.is_constant() {
            self.add_assign_constant(term.get_constant_value());
            return;
        }

        // otherwise add constant and scaled num separately
        self.add_assign_constant(term.constant_term);
        self.add_assign_number_with_coeff(&term.num, term.coeff);
    }
   
    pub fn add_assign_boolean_with_coeff(
        &mut self,
        bit: &Boolean,
        coeff: E::Fr
    )
    {
        if coeff.is_zero() {
            return;
        }

        let new_value = match (self.value, bit.get_value()) {
            (Some(mut val), Some(bit_value)) => {
                if bit_value {
                    val.add_assign(&coeff);
                }

                Some(val)
            },
            _ => None
        };
        self.value = new_value;

        match bit {
            &Boolean::Constant(c) => {
                if c {
                    self.constant.add_assign(&coeff);
                }
            },
            &Boolean::Is(ref v) => {
                self.terms.push((coeff, v.get_variable()));
            },
            &Boolean::Not(ref v) => {
                let mut coeff_negated = coeff;
                coeff_negated.negate();
                self.terms.push((coeff_negated, v.get_variable()));

                self.constant.add_assign(&coeff);
            }
        }
    }

    pub fn add_assign_bit_with_coeff(
        &mut self,
        bit: &AllocatedBit,
        coeff: E::Fr
    )
    {
        if coeff.is_zero() {
            return;
        }

        let new_value = match (self.value, bit.get_value()) {
            (Some(mut val), Some(bit_value)) => {
                if bit_value {
                    val.add_assign(&coeff);
                }

                Some(val)
            },
            _ => None
        };

        self.value = new_value;
        self.terms.push((coeff, bit.get_variable()))
    }

    pub fn add_assign_constant(
        &mut self,
        coeff: E::Fr
    )
    {
        if coeff.is_zero() {
            return;
        }

        let newval = match self.value {
            Some(mut curval) => {
                curval.add_assign(&coeff);

                Some(curval)
            },
            None => {
                None
            }
        };

        self.value = newval;
        self.constant.add_assign(&coeff);
    }

    pub fn sub_assign_constant(
        &mut self,
        coeff: E::Fr
    )
    {
        let mut c = coeff;
        c.negate();

        self.add_assign_constant(c);
    }

    pub fn into_num<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS
    ) -> Result<Num<E>, SynthesisError> {
        if self.terms.len() == 0 {
            return Ok(Num::Constant(self.constant));
        }

        let allocated = self.into_allocated_num(cs)?;

        Ok(Num::Variable(allocated))
    }

    #[track_caller]
    pub fn enforce_zero<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS
    ) -> Result<(), SynthesisError> {
        if let Some(value) = self.get_value() {
            assert!(value.is_zero(), "LC is not actually zero with value {}", value);
        }
        use crate::bellman::plonk::better_better_cs::cs::PlonkConstraintSystemParams;

        if CS::Params::CAN_ACCESS_NEXT_TRACE_STEP {
            Self::enforce_zero_using_next_step(
                cs,
                self.terms,
                self.constant
            )
        } else {
            unimplemented!()
        }
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
            Self::enforce_zero_using_next_step(
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

    fn enforce_zero_using_next_step<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        terms: Vec<(E::Fr, Variable)>,
        constant_term: E::Fr
    ) -> Result<(), SynthesisError> {
        // we assume that terms are deduplicated

        let one_fr = E::Fr::one();
        let mut minus_one_fr = E::Fr::one();
        minus_one_fr.negate();

        // trivial case - single variable

        assert!(terms.len() > 0);

        let num_terms = terms.len();

        let mg = CS::MainGate::default();

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

            use crate::bellman::plonk::better_better_cs::cs::{Gate, MainGate};

            let mut next_term_range = CS::MainGate::range_of_next_step_linear_terms();
            assert_eq!(next_term_range.len(), 1, "for now works only if only one variable is accessible on the next step");
            let next_step_coeff_idx = next_term_range.next().expect("must give at least one index");

            // this is a placeholder variable that must go into the 
            // corresponding trace polynomial at the NEXT time step 
            let (mut next_step_var_in_chain, mut next_step_var_in_chain_value) = {
                let chunk: Vec<_> = (&mut it).take(CS::Params::STATE_WIDTH).collect();
                let may_be_new_intermediate_value = Self::evaluate_term_value(
                    &*cs, 
                    &chunk, 
                    constant_term
                );

                let some_value = match &may_be_new_intermediate_value {
                    Ok(val) => Some(*val),
                    Err(_) => None
                };

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
                coeffs[next_step_coeff_idx] = minus_one_fr;

                cs.new_single_gate_for_trace_step(
                    &mg, 
                    &coeffs, 
                    &vars,
                    &[]
                )?;

                (new_intermediate_var, some_value)
            };

            // run over the rest

            // we can only take one less cause 
            // we've already used one of the variable
            let consume_from_lc = CS::Params::STATE_WIDTH - 1; 
            for _ in 0..(cycles-1) {
                // we need to keep in mind that last term of the linear combination is taken
                // so we have to fill only CS::Params::STATE_WIDTH - 1 and then manually 
                // place the next_step_var_in_chain 
                let chunk: Vec<_> = (&mut it).take(consume_from_lc).collect();
                
                // this is a sum of new terms
                let may_be_new_intermediate_value = Self::evaluate_term_value(
                    &*cs, 
                    &chunk, 
                    E::Fr::zero()
                ).map(|val| {
                    // and 
                    let mut tmp = val;
                    tmp.add_assign(next_step_var_in_chain_value.as_ref().expect("value must be known"));

                    tmp
                });

                let some_value = match &may_be_new_intermediate_value {
                    Ok(val) => Some(*val),
                    Err(_) => None
                };

                // we manually allocate the new variable
                // and also add value of one in a chain
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
                coeffs[next_step_coeff_idx] = minus_one_fr;

                cs.new_single_gate_for_trace_step(
                    &mg, 
                    &coeffs, 
                    &vars,
                    &[]
                )?;

                next_step_var_in_chain = new_intermediate_var;
                next_step_var_in_chain_value = some_value;
            }

            // final step - we just make a single gate, last one
            // we also make sure that chained variable only goes into the last term
            {
                let chunk: Vec<_> = (&mut it).collect();
                assert!(chunk.len() <= CS::Params::STATE_WIDTH - 1);

                let mut gate_term = MainGateTerm::<E>::new();

                for (c, var) in chunk.into_iter() {
                    let t = ArithmeticTerm::from_variable_and_coeff(var, c);
                    gate_term.add_assign(t);
                }

                let dummy = CS::get_dummy_variable();

                let range_of_linear_terms = CS::MainGate::range_of_linear_terms();
                let idx_of_last_linear_term = range_of_linear_terms.last().expect("must have an index");

                let (mut vars, mut coeffs) = CS::MainGate::format_term(gate_term, dummy)?;

                *vars.last_mut().unwrap() = next_step_var_in_chain;
                coeffs[idx_of_last_linear_term] = one_fr;

                cs.new_single_gate_for_trace_step(
                    &mg, 
                    &coeffs, 
                    &vars,
                    &[]
                )?;
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

    pub fn uniquely_pack_le_booleans_into_single_num<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        bools: &[Boolean],
    ) -> Result<Num<E>, SynthesisError> {
        Self::uniquely_pack_booleans_into_single_num(cs, bools)
    }

    pub fn uniquely_pack_booleans_into_single_num<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        bools: &[Boolean],
    ) -> Result<Num<E>, SynthesisError> {
        assert!(bools.len() <= E::Fr::CAPACITY as usize);

        let mut lc = Self::zero();
        let mut coeff = E::Fr::one();
        for b in bools.iter() {
            lc.add_assign_boolean_with_coeff(b, coeff);
            coeff.double();
        }

        let num = lc.into_num(cs)?;

        Ok(num)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::bellman::plonk::better_better_cs::cs::*;

    #[test]
    fn test_inscribe_linear_combination() {
        use crate::bellman::pairing::bn256::{Bn256, Fr};

        let mut assembly = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();
        let before = assembly.n();

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

        assert!(assembly.gates.len() == 1);
        assert_eq!(assembly.n(), 3);
        // let num_gates = assembly.n - before;
        // println!("Single rescue r = 2, c = 1, alpha = 5 invocation takes {} gates", num_gates);

        // for (gate, density) in assembly.gate_density.0.into_iter() {
        //     println!("Custom gate {:?} selector = {:?}", gate, density);
        // }

        assert!(assembly.is_satisfied());
    }

    #[test]
    fn test_inscribe_linear_combination_of_two_gates() {
        use crate::bellman::pairing::bn256::{Bn256, Fr};

        let mut assembly = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();
        let before = assembly.n();

        let variables: Vec<_> = (0..5).map(|_| AllocatedNum::alloc(
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

        assert!(assembly.gates.len() == 1);
        assert_eq!(assembly.n(), 2);

        assert!(assembly.is_satisfied());
    }

    #[test]
    fn check_terms_summing() {
        use crate::bellman::pairing::bn256::{Bn256, Fr};
        use crate::bellman::plonk::better_better_cs::cs::*;
        use crate::plonk::circuit::linear_combination::*;
        use crate::plonk::circuit::allocated_num::*;
        use crate::plonk::circuit::simple_term::*;

        struct Tester;

        impl Circuit<Bn256> for Tester {
            type MainGate = Width4MainGateWithDNext;

            fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<Bn256>>>, SynthesisError> {
                Ok(
                    vec![
                        Self::MainGate::default().into_internal(),
                    ]
                )
            }
            fn synthesize<CS: ConstraintSystem<Bn256>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
                for len in vec![3,4,5] {
                    let mut terms = vec![];
                    for i in 1..=len {
                        let coeff = Fr::from_str(&i.to_string()).unwrap();
                        let value = Fr::from_str(&i.to_string()).unwrap();

                        let var = AllocatedNum::alloc(
                            cs, 
                            || {
                                Ok(value)
                            }
                        )?;
                        let mut term = Term::<Bn256>::from_allocated_num(var);

                        term.scale(&coeff);
                        term.add_constant(&value);

                        terms.push(term);
                    }
                    
                    let (first, other) = terms.split_first().unwrap();

                    let _ = first.add_multiple(cs, &other)?;
                }
                
                Ok(())
            }
        }

        let mut assembly = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

        let circuit = Tester;
        circuit.synthesize(&mut assembly).unwrap();
        assert!(assembly.is_satisfied());

        assembly.finalize();

        use crate::bellman::worker::Worker;

        let worker = Worker::new();

        let setup = assembly.create_setup::<Tester>(&worker).unwrap();

        use crate::bellman::kate_commitment::*;
        use crate::bellman::plonk::commitments::transcript::{*, keccak_transcript::RollingKeccakTranscript};

        let crs_mons =
            Crs::<Bn256, CrsForMonomialForm>::crs_42(setup.permutation_monomials[0].size(), &worker);

        let proof = assembly.create_proof::<_, RollingKeccakTranscript<Fr>>(
            &worker, 
            &setup, 
            &crs_mons,
            None
        ).unwrap();
    }
}