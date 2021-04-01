pub mod utils;
pub mod tables;
pub mod sha256;
pub mod blake2s;
pub mod keccak;


use crate::bellman::SynthesisError;
use crate::bellman::Engine;
use crate::bellman::pairing::ff::*;
use crate::bellman::pairing::ff::{PrimeField, PrimeFieldRepr};
use crate::bellman::plonk::better_better_cs::cs::*;
use crate::plonk::circuit::allocated_num::{
    AllocatedNum,
    Num,
    STATE_WIDTH
};
use crate::circuit::{
    Assignment
};
use std::iter;


trait NumExtension<E: Engine> : Sized
{
    fn lc_impl<CS : ConstraintSystem<E>>(
        cs: &mut CS, input_coeffs: &[E::Fr], inputs: &[Self], use_d_next: bool
    ) -> Result<Self, SynthesisError>;
    
    fn lc<CS: ConstraintSystem<E>>(cs: &mut CS, input_coeffs: &[E::Fr], inputs: &[Self]) -> Result<Self, SynthesisError>;
    fn lc_with_d_next<CS: ConstraintSystem<E>>(cs: &mut CS, input_coeffs: &[E::Fr], inputs: &[Self]) -> Result<Self, SynthesisError>;
    fn sum<CS: ConstraintSystem<E>>(cs: &mut CS, nums: &[Self]) -> Result<Self, SynthesisError>;
    fn sum_with_d_next<CS: ConstraintSystem<E>>(cs: &mut CS, nums: &[Self]) -> Result<Self, SynthesisError>;
    fn long_weighted_sum<CS: ConstraintSystem<E>>(cs: &mut CS, vars: &[Self], base: &E::Fr) -> Result<Self, SynthesisError>;
} 


impl<E: Engine> NumExtension<E> for Num<E> 
{
    fn lc_impl<CS>(cs: &mut CS, input_coeffs: &[E::Fr], inputs: &[Num<E>], use_d_next: bool) -> Result<Self, SynthesisError>
    where CS: ConstraintSystem<E>
    {
        assert_eq!(input_coeffs.len(), inputs.len());

        // corner case: all our values are actually constants
        if inputs.iter().all(| x | x.is_constant()) {
            let value = inputs.iter().zip(input_coeffs.iter()).fold(E::Fr::zero(), |acc, (x, coef)| {
                let mut temp = x.get_value().unwrap();
                temp.mul_assign(&coef);
                temp.add_assign(&acc);
                temp
            });

            return Ok(Num::Constant(value));
        }

        let res_var = AllocatedNum::alloc(cs, || {
            let mut cur = E::Fr::zero();
            for (elem, coef) in inputs.iter().zip(input_coeffs.iter()) {
                let mut tmp = elem.get_value().grab()?;
                tmp.mul_assign(coef);
                cur.add_assign(&tmp);
            }
            Ok(cur)
        })?;

        // okay, from now one we may be sure that we have at least one allocated term
        let mut constant_term = E::Fr::zero();
        let mut vars = Vec::with_capacity(STATE_WIDTH);
        let mut coeffs = Vec::with_capacity(STATE_WIDTH);

        // Note: the whole thing may be a little more efficient with the use of custom gates
        // exploiting (d_next)
        let mut minus_one = E::Fr::one();
        minus_one.negate();
        let dummy = AllocatedNum::zero(cs);

        for (x, coef) in inputs.iter().zip(input_coeffs.iter()) {
            match x {
                Num::Constant(x) => {
                    let mut temp = x.clone();
                    temp.mul_assign(&coef);
                    constant_term.add_assign(&temp);
                },
                Num::Variable(x) => {
                    if vars.len() < STATE_WIDTH
                    {
                        vars.push(x.clone());
                        coeffs.push(coef.clone());
                    }
                    else {
                        coeffs.reverse();
                        vars.reverse();
                        let tmp = AllocatedNum::quartic_lc_with_cnst(cs, &coeffs[..], &vars[..], &constant_term)?;

                        constant_term = E::Fr::zero();
                        vars = vec![tmp, x.clone()];
                        coeffs = vec![E::Fr::one(), coef.clone()];
                    }
                }
            }
        }

        if vars.len() == STATE_WIDTH {
            coeffs.reverse();
            vars.reverse();

            match use_d_next {
                true => {
                    AllocatedNum::quartic_lc_eq_with_cnst(cs, &coeffs[..], &vars[..], &res_var, &constant_term)?;
                    return Ok(Num::Variable(res_var))
                },
                false => {
                    let temp = AllocatedNum::quartic_lc_with_cnst(cs, &coeffs[..], &vars[..], &constant_term)?;
                    constant_term = E::Fr::zero();
                    vars = vec![temp];
                    coeffs = vec![E::Fr::one()];
                }
            }
        }

        // pad with dummy variables
        for _i in vars.len()..(STATE_WIDTH-1) {
            vars.push(AllocatedNum::zero(cs));
            coeffs.push(E::Fr::zero());
        }

        vars.push(res_var.clone());
        coeffs.push(minus_one);
        coeffs.reverse();
        vars.reverse();
        
        AllocatedNum::general_lc_gate(cs, &coeffs[..], &vars[..], &constant_term, &E::Fr::zero(), &dummy)?;
        Ok(Num::Variable(res_var))
    }

    fn lc<CS: ConstraintSystem<E>>(cs: &mut CS, input_coeffs: &[E::Fr], inputs: &[Num<E>]) -> Result<Self, SynthesisError>
    {
        Self::lc_impl(cs, input_coeffs, inputs, false)
    }

    fn lc_with_d_next<CS>(cs: &mut CS, input_coeffs: &[E::Fr], inputs: &[Num<E>]) -> Result<Self, SynthesisError>
    where CS: ConstraintSystem<E>
    {
        Self::lc_impl(cs, input_coeffs, inputs, true)
    }

    // same as lc but with all the coefficients set to be 1
    fn sum<CS: ConstraintSystem<E>>(cs: &mut CS, nums: &[Num<E>]) -> Result<Self, SynthesisError>
    {
        let coeffs = vec![E::Fr::one(); nums.len()];
        Self::lc(cs, &coeffs[..], &nums[..])
    }

    fn sum_with_d_next<CS: ConstraintSystem<E>>(cs: &mut CS, nums: &[Num<E>]) -> Result<Self, SynthesisError>
    {
        let coeffs = vec![E::Fr::one(); nums.len()];
        Self::lc_with_d_next(cs, &coeffs[..], &nums[..])
    }

    // for given array of slices : [x0, x1, x2, ..., xn] of arbitrary length, base n and total accumulated x
    // validates that x = x0 + x1 * base + x2 * base^2 + ... + xn * base^n
    fn long_weighted_sum<CS>(cs: &mut CS, vars: &[Self], base: &E::Fr) -> Result<Self, SynthesisError>
    where CS: ConstraintSystem<E>
    {
        let mut coeffs = Vec::with_capacity(vars.len());
        let mut acc = E::Fr::one();

        for _ in 0..vars.len() {
            coeffs.push(acc.clone());
            acc.mul_assign(&base);
        }

        Self::lc(cs, &coeffs[..], vars)
    }
}


trait AllocatedNumExtension<E: Engine> : Sized
{
    fn alloc_from_lc<CS: ConstraintSystem<E>>(
        cs: &mut CS, 
        coefs: &[E::Fr],
        vars: &[Self],
        cnst: &E::Fr
    ) -> Result<Self, SynthesisError>;

    fn alloc_sum<CS: ConstraintSystem<E>>(
        cs: &mut CS, 
        vars: &[Self],
    ) -> Result<Self, SynthesisError>; 

    fn general_lc_gate<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        coefs: &[E::Fr],
        vars: &[Self],
        cnst: &E::Fr,
        next_row_coef: &E::Fr,
        next_row_var: &Self,
    ) -> Result<(), SynthesisError>;

    fn quartic_lc<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        coefs: &[E::Fr],
        vars: &[Self],
    ) -> Result<Self, SynthesisError>;

    fn quartic_lc_with_cnst<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        coefs: &[E::Fr],
        vars: &[Self],
        cnst: &E::Fr,
    ) -> Result<Self, SynthesisError>;
   
    fn ternary_lc_eq<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        coefs: &[E::Fr],
        vars: &[Self],
        total: &Self,
    ) -> Result<(), SynthesisError>;

    fn quartic_lc_eq<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        coefs: &[E::Fr],
        vars: &[Self],
        total: &Self,
    ) -> Result<(), SynthesisError>;

    fn quartic_lc_eq_with_cnst<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        coefs: &[E::Fr],
        vars: &[Self],
        total: &Self,
        cnst: &E::Fr,
    ) -> Result<(), SynthesisError>;

    fn ternary_lc_with_cnst<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        coefs: &[E::Fr],
        vars: &[Self],
        cnst: &E::Fr,
    ) -> Result<Self, SynthesisError>;

    fn long_lc_eq<CS: ConstraintSystem<E>>(
        cs: &mut CS, 
        vars: &[Self], 
        coefs: &[E::Fr], 
        total: &Self, 
        use_d_next: bool
    ) -> Result<bool, SynthesisError>;

    fn long_weighted_sum_eq<CS: ConstraintSystem<E>>(
        cs: &mut CS, 
        vars: &[Self], 
        base: &E::Fr, 
        total: &Self, 
        use_d_next: bool
    ) -> Result<bool, SynthesisError>;
}



impl<E: Engine> AllocatedNumExtension<E> for AllocatedNum<E>
{ 
    fn alloc_from_lc<CS: ConstraintSystem<E>>(
        cs: &mut CS, 
        coefs: &[E::Fr],
        vars: &[Self],
        cnst: &E::Fr
    ) -> Result<Self, SynthesisError>
    {
        assert_eq!(coefs.len(), vars.len());
        
        let new_value = match vars.iter().all(|x| x.get_value().is_some()) {
            false => None,
            true => {
                let mut res = cnst.clone();
                for (var, coef) in vars.iter().zip(coefs.iter()) {
                    let mut tmp = var.get_value().unwrap();
                    tmp.mul_assign(coef);
                    res.add_assign(&tmp);
                }
                Some(res)
            },
        };

        Self::alloc(cs, || new_value.grab())
    }

    fn alloc_sum<CS: ConstraintSystem<E>>(
        cs: &mut CS, 
        vars: &[Self],
    ) -> Result<Self, SynthesisError> 
    {
        let mut coefs = Vec::with_capacity(vars.len());
        coefs.extend(iter::repeat(E::Fr::one()).take(vars.len()));
        Self::alloc_from_lc(cs, &coefs[..], vars, &E::Fr::zero())
    }

    // given vector of coefs: [c0, c1, c2, c3],
    // vector of vars: [var0, var1, var2, var3],
    // next row var and coef: c4 and var4
    // and additional constant: cnst
    // constrcut the gate asserting that: 
    // c0 * var0 + c1 * var1 + c2 * var3 + c4 * var4 + cnst = 0
    // here the state is [var0, var1, var2, var3]
    // and var4 should be placed on the next row with the help of d_next
    fn general_lc_gate<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        coefs: &[E::Fr],
        vars: &[Self],
        cnst: &E::Fr,
        next_row_coef: &E::Fr,
        next_row_var: &Self,
    ) -> Result<(), SynthesisError>
    {
        assert_eq!(coefs.len(), vars.len());
        assert_eq!(coefs.len(), STATE_WIDTH);
        
        // check if equality indeed holds
        // TODO: do it only in debug mde!
        match (vars[0].get_value(), vars[1].get_value(), vars[2].get_value(), vars[3].get_value(), next_row_var.get_value()) {
            (Some(val0), Some(val1), Some(val2), Some(val3), Some(val4)) => {
                let mut running_sum = val0;
                running_sum.mul_assign(&coefs[0]);

                let mut tmp = val1;
                tmp.mul_assign(&coefs[1]);
                running_sum.add_assign(&tmp);

                let mut tmp = val2;
                tmp.mul_assign(&coefs[2]);
                running_sum.add_assign(&tmp);

                let mut tmp = val3;
                tmp.mul_assign(&coefs[3]);
                running_sum.add_assign(&tmp);

                let mut tmp = val4;
                tmp.mul_assign(&next_row_coef);
                running_sum.add_assign(&tmp);

                running_sum.add_assign(&cnst);
                assert_eq!(running_sum, E::Fr::zero())
            }
            _ => {},
        };

        let dummy = Self::zero(cs);
        let range_of_linear_terms = CS::MainGate::range_of_linear_terms();
        let gate_term = MainGateTerm::new();
        let (_, mut local_coeffs) = CS::MainGate::format_term(gate_term, dummy.variable)?;
        for (i, idx) in range_of_linear_terms.enumerate() {
            local_coeffs[idx] = coefs[i].clone();
        }
  
        let cnst_index = CS::MainGate::index_for_constant_term();
        local_coeffs[cnst_index] = *cnst;

        let next_row_term_idx = CS::MainGate::range_of_next_step_linear_terms().last().unwrap();
        local_coeffs[next_row_term_idx] = next_row_coef.clone();

        let mg = CS::MainGate::default();
        let local_vars = vec![vars[0].get_variable(), vars[1].get_variable(), vars[2].get_variable(), vars[3].get_variable()];

        cs.new_single_gate_for_trace_step(
            &mg,
            &local_coeffs,
            &local_vars,
            &[]
        )?;

        Ok(())
    }

    // given vector of coefs: [c0, c1, c2, c3],
    // vector of vars: [var0, var1, var2, var3, var4],
    // and additional constant: cnst
    // allocate new variable res equal to c0 * var0 + c1 * var1 + c2 * var2 + c3 * var3
    // assuming res is placed in d register of the next row
    fn quartic_lc_with_cnst<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        coefs: &[E::Fr],
        vars: &[Self],
        cnst: &E::Fr,
    ) -> Result<Self, SynthesisError>
    {
        let res = AllocatedNum::alloc_from_lc(cs, coefs, vars, cnst)?;
        let mut minus_one = E::Fr::one();
        minus_one.negate();

        AllocatedNum::general_lc_gate(cs, coefs, vars, cnst, &minus_one, &res)?;
        Ok(res)
    }

    fn quartic_lc<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        coefs: &[E::Fr],
        vars: &[Self],
    ) -> Result<Self, SynthesisError>
    {
        let zero = E::Fr::zero();
        let res = AllocatedNum::alloc_from_lc(cs, coefs, vars, &zero)?;
        let mut minus_one = E::Fr::one();
        minus_one.negate();

        AllocatedNum::general_lc_gate(cs, coefs, vars, &zero, &minus_one, &res)?;
        Ok(res)
    }

    fn quartic_lc_eq<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        coefs: &[E::Fr],
        vars: &[Self],
        total: &Self,
    ) -> Result<(), SynthesisError>
    {
        let mut minus_one = E::Fr::one();
        minus_one.negate();
        AllocatedNum::general_lc_gate(cs, coefs, vars, &E::Fr::zero(), &minus_one, &total)
    }

    fn quartic_lc_eq_with_cnst<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        coefs: &[E::Fr],
        vars: &[Self],
        total: &Self,
        cnst: &E::Fr,
    ) -> Result<(), SynthesisError>
    {
        let mut minus_one = E::Fr::one();
        minus_one.negate();
        AllocatedNum::general_lc_gate(cs, coefs, vars, cnst, &minus_one, &total)
    }

    fn ternary_lc_eq<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        coefs: &[E::Fr],
        vars: &[Self],
        total: &Self,
    ) -> Result<(), SynthesisError>
    {
        assert_eq!(coefs.len(), vars.len());
        assert_eq!(coefs.len(), STATE_WIDTH-1);

        let mut minus_one = E::Fr::one();
        minus_one.negate();

        let mut local_coefs = vec![];
        local_coefs.extend_from_slice(coefs);
        local_coefs.push(minus_one);
        
        let mut local_vars = vec![];
        local_vars.extend_from_slice(vars);
        local_vars.push(total.clone());

        let dummy = AllocatedNum::zero(cs);
        AllocatedNum::general_lc_gate(
            cs, &local_coefs[..], &local_vars[..], &E::Fr::zero(), &E::Fr::zero(), &dummy,
        )
    }

    fn ternary_lc_with_cnst<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        coefs: &[E::Fr],
        vars: &[Self],
        cnst: &E::Fr,
    ) -> Result<Self, SynthesisError>
    {
        assert_eq!(coefs.len(), vars.len());
        assert_eq!(coefs.len(), STATE_WIDTH-1);

        let res = AllocatedNum::alloc_from_lc(cs, coefs, vars, cnst)?;
        let mut minus_one = E::Fr::one();
        minus_one.negate();

        let mut local_coefs = vec![];
        local_coefs.extend_from_slice(coefs);
        local_coefs.push(minus_one);

        let mut local_vars = vec![];
        local_vars.extend_from_slice(vars);
        local_vars.push(res.clone());

        let dummy = AllocatedNum::zero(cs);
        AllocatedNum::general_lc_gate(
            cs, &local_coefs[..], &local_vars[..], &E::Fr::zero(), &E::Fr::zero(), &dummy
        )?;

        Ok(res)
    }

    fn long_lc_eq<CS: ConstraintSystem<E>>(
        cs: &mut CS, 
        vars: &[Self], 
        coefs: &[E::Fr], 
        total: &Self, 
        use_d_next: bool
    ) -> Result<bool, SynthesisError>
    {
        let mut loc_coefs = Vec::with_capacity(STATE_WIDTH);
        let mut loc_vars = Vec::with_capacity(STATE_WIDTH);
        
        let mut minus_one = E::Fr::one();
        minus_one.negate();
        let dummy = AllocatedNum::zero(cs);

        for (var, coef) in vars.iter().zip(coefs.iter()) {
            if loc_vars.len() < STATE_WIDTH {
                loc_coefs.push(coef.clone());
                loc_vars.push(var.clone());
            }
            else {
                // we have filled in the whole vector!
                loc_coefs.reverse();
                loc_vars.reverse();

                let temp = AllocatedNum::quartic_lc(cs, &loc_coefs[..], &loc_vars[..])?;
                loc_coefs = vec![E::Fr::one(), coef.clone()];
                loc_vars = vec![temp, var.clone()];
            }
        }

        if loc_vars.len() == STATE_WIDTH {
            loc_coefs.reverse();
            loc_vars.reverse();
            
            match use_d_next {
                true => {
                    AllocatedNum::quartic_lc_eq(cs, &loc_coefs[..], &loc_vars[..], &total)?;
                    return Ok(true)
                },
                false => {
                    // we have filled in the whole vector again!
                    let temp = AllocatedNum::quartic_lc(cs, &loc_coefs[..], &loc_vars[..])?;
                    loc_coefs = vec![E::Fr::one()];
                    loc_vars = vec![temp];
                }
            }

        }
        
        // pad with dummy variables
        for _i in loc_vars.len()..(STATE_WIDTH-1) {
            loc_vars.push(dummy.clone());
            loc_coefs.push(E::Fr::zero());
        }

        loc_vars.push(total.clone());
        loc_coefs.push(minus_one);
        loc_coefs.reverse();
        loc_vars.reverse();

        AllocatedNum::general_lc_gate(cs, &loc_coefs[..], &loc_vars[..], &E::Fr::zero(), &E::Fr::zero(), &dummy)?;
        Ok(false)
    }

    // for given array of slices : [x0, x1, x2, ..., xn] of arbitrary length, base n and total accumulated x
    // validates that x = x0 + x1 * base + x2 * base^2 + ... + xn * base^n
    // use_d_next flag allows to place total on the next row, without expicitely constraiting it and leaving
    // is as a job for the next gate allocation.
    fn long_weighted_sum_eq<CS: ConstraintSystem<E>>(
        cs: &mut CS, 
        vars: &[Self], 
        base: &E::Fr, 
        total: &Self, 
        use_d_next: bool
    ) -> Result<bool, SynthesisError>
    {
        let mut acc_fr = E::Fr::one();
        let mut loc_coefs = Vec::with_capacity(STATE_WIDTH);
        let mut loc_vars = Vec::with_capacity(STATE_WIDTH);
        
        let mut minus_one = E::Fr::one();
        minus_one.negate();
        let dummy = AllocatedNum::zero(cs);

        for var in vars.iter() {
            if loc_vars.len() < STATE_WIDTH {
                loc_coefs.push(acc_fr.clone());
                acc_fr.mul_assign(&base);
                loc_vars.push(var.clone());
            }
            else {
                // we have filled in the whole vector!
                loc_coefs.reverse();
                loc_vars.reverse();

                let temp = AllocatedNum::quartic_lc(cs, &loc_coefs[..], &loc_vars[..])?;
                loc_coefs = vec![E::Fr::one(), acc_fr.clone()];
                loc_vars = vec![temp, var.clone()];
                
                acc_fr.mul_assign(&base);
            }
        }

        if loc_vars.len() == STATE_WIDTH {
            loc_coefs.reverse();
            loc_vars.reverse();
            
            match use_d_next {
                true => {
                    AllocatedNum::quartic_lc_eq(cs, &loc_coefs[..], &loc_vars[..], &total)?;
                    return Ok(true)
                },
                false => {
                    // we have filled in the whole vector again!
                    let temp = AllocatedNum::quartic_lc(cs, &loc_coefs[..], &loc_vars[..])?;
                    loc_coefs = vec![E::Fr::one()];
                    loc_vars = vec![temp];
                }
            }

        }
        
        // pad with dummy variables
        for _i in loc_vars.len()..(STATE_WIDTH-1) {
            loc_vars.push(dummy.clone());
            loc_coefs.push(E::Fr::zero());
        }

        loc_vars.push(total.clone());
        loc_coefs.push(minus_one);
        loc_coefs.reverse();
        loc_vars.reverse();

        AllocatedNum::general_lc_gate(cs, &loc_coefs[..], &loc_vars[..], &E::Fr::zero(), &E::Fr::zero(), &dummy)?;
        Ok(false)
    }
}