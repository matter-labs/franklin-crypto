use std::unimplemented;

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
    MainGate,
};

use super::utils::is_selector_specialized_gate;

use super::boolean::{self, AllocatedBit, Boolean};
use super::linear_combination::*;

use crate::plonk::circuit::Assignment;

pub const STATE_WIDTH : usize = 4;

pub mod stats {
    use std::sync::atomic::*;

    pub static COUNTER: AtomicUsize = AtomicUsize::new(0);

    pub fn reset_counter() {
        COUNTER.store(0, Ordering::Relaxed);
    }

    pub fn increment_counter() {
        COUNTER.fetch_add(1, Ordering::SeqCst);
    }

    pub fn increment_counter_by(val: usize) {
        COUNTER.fetch_add(val, Ordering::SeqCst);
    }

    pub fn output_counter() -> usize {
        COUNTER.load(Ordering::Relaxed)
    }
}

#[derive(Debug)]
pub enum Num<E: Engine> {
    Variable(AllocatedNum<E>),
    Constant(E::Fr)
}

impl<E: Engine> Clone for Num<E> {
    fn clone(&self) -> Self {
        match &self {
            Num::Variable(ref var) => Num::Variable(*var),
            Num::Constant(ref constant) => Num::Constant(*constant)
        }
    }
}

impl<E: Engine> Copy for Num<E> {}

impl<E: Engine> Default for Num<E> {
    fn default() -> Self {
        Num::Constant(E::Fr::zero())
    }
}

impl<E: Engine> std::fmt::Display for Num<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Num {{ ")?;
        match self {
            Num::Variable(v) => {
                write!(f, "Variable({:?})", v.get_variable())?;
            },
            Num::Constant(c) => {
                write!(f, "Constant({}), ", c)?;
            }
        }
        writeln!(f, "}}")
    }
}

impl<E: Engine> Num<E> {
    pub fn zero() -> Self {
        Num::Constant(E::Fr::zero())
    }

    pub fn one() -> Self {
        Num::Constant(E::Fr::one())
    }

    pub fn alloc<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        witness: Option<E::Fr>
    ) -> Result<Self, SynthesisError> {
        let new = Num::Variable(
            AllocatedNum::alloc(cs, || Ok(*witness.get()?))?
        );

        Ok(new)
    }
    
    pub fn get_value(&self) -> Option<E::Fr> {
        match self {
            Num::Variable(v) => v.get_value(),
            Num::Constant(c) => Some(*c)
        }
    }

    pub fn is_zero<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Boolean, SynthesisError> {
        let flag = match self {
            Num::Constant(c) => Ok(Boolean::constant(c.is_zero())),
            Num::Variable(var) => var.is_zero(cs),
        };

        flag
    }

    pub fn is_constant(&self) -> bool {
        match self {
            Num::Variable(..) => false,
            Num::Constant(..) => true
        }
    }

    #[track_caller]
    pub fn get_constant_value(&self) -> E::Fr {
        match self {
            Num::Variable(..) => panic!("this Num is not a constant"),
            Num::Constant(c) => *c
        }
    }

    #[track_caller]
    pub fn get_variable(&self) -> AllocatedNum<E> {
        match self {
            Num::Constant(..) => {
                panic!("this Num is not a variable")
            },
            Num::Variable(v) => {
                v.clone()
            }
        }
    }

    #[track_caller]
    pub fn enforce_equal<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        b: &Self
    ) -> Result<(), SynthesisError> {
        match (self, b) {
            (Num::Variable(ref a), Num::Variable(ref b)) => {
                a.enforce_equal(cs, b)
            },
            (Num::Variable(ref var), Num::Constant(constant)) | 
            (Num::Constant(constant), Num::Variable(ref var)) => {
                var.assert_equal_to_constant(cs, *constant)
            },
            (Num::Constant(a), Num::Constant(b)) => {
                assert_eq!(a, b);

                Ok(())
            }
        }
    }

    #[track_caller]
    pub fn conditionally_enforce_equal<CS>(cs: &mut CS, cond: &Boolean, a: &Self, b: &Self) -> Result<(), SynthesisError>
    where CS: ConstraintSystem<E>
    {
        let masked_a = Num::mask(cs, &a, &cond)?;
        let masked_b = Num::mask(cs, &b, &cond)?;
        masked_a.enforce_equal(cs, &masked_b)
    }

    /// Takes two allocated numbers (a, b) and returns
    /// (b, a) if the condition is true, and (a, b)
    /// otherwise.
    pub fn conditionally_reverse<CS>(
        cs: &mut CS,
        a: &Self,
        b: &Self,
        condition: &Boolean
    ) -> Result<(Self, Self), SynthesisError>
        where CS: ConstraintSystem<E>
    {
        if condition.is_constant() {
            let swap = condition.get_value().expect("must get a value of the constant");

            if swap {
                return Ok((b.clone(), a.clone()))
            } else {
                return Ok((a.clone(), b.clone()))
            }
        }

        if is_selector_specialized_gate::<E, CS>() {
            let c = Num::conditionally_select(cs, &condition, &b, &a)?;
            let d = Num::conditionally_select(cs, &condition, &a, &b)?;

            return Ok((c, d));
        }

        match (a, b) {
            (Num::Variable(a), Num::Variable(b)) => {
                let (c, d) = AllocatedNum::conditionally_reverse(cs, a, b, condition)?;
                return Ok((Num::Variable(c), Num::Variable(d)));
            },
            _ =>{}
        }

        let c = AllocatedNum::alloc(
            cs,
            || {
                if *condition.get_value().get()? {
                    Ok(*b.get_value().get()?)
                } else {
                    Ok(*a.get_value().get()?)
                }
            }
        )?;

        let d = AllocatedNum::alloc(
            cs,
            || {
                if *condition.get_value().get()? {
                    Ok(*a.get_value().get()?)
                } else {
                    Ok(*b.get_value().get()?)
                }
            }
        )?;

        let c = Num::Variable(c);
        let d = Num::Variable(d);

        // (a - b) * condition = a - c
        // (b - a) * condition = b - d 
        // if condition == 0, then a == c, b == d
        // if condition == 1, then b == c, a == d

        match (condition, a, b) {
            (Boolean::Constant(..), _, _) => {
                unreachable!("constant is already handles")
            },
            (Boolean::Is(condition_var), Num::Constant(a), Num::Constant(b)) => {
                // (a - b) * condition = a - c
                // (b - a) * condition = b - d 
                // if condition == 0, then a == c, b == d
                // if condition == 1, then b == c, a == d

                // (a-b) * condition - a + c = 0
                // -(a-b) * condition - b + d = 0

                let mut a_minus_b = *a;
                a_minus_b.sub_assign(&b);
                let mut ab_condition_term = ArithmeticTerm::from_variable(condition_var.get_variable());
                ab_condition_term.scale(&a_minus_b);
                let a_term = ArithmeticTerm::constant(*a);
                let b_term = ArithmeticTerm::constant(*b);
                let c_term = ArithmeticTerm::from_variable(c.get_variable().get_variable());
                let d_term = ArithmeticTerm::from_variable(d.get_variable().get_variable());

                let mut ac_term = MainGateTerm::new();
                ac_term.add_assign(ab_condition_term.clone());
                ac_term.sub_assign(a_term);
                ac_term.add_assign(c_term);

                cs.allocate_main_gate(ac_term)?;

                let mut bd_term = MainGateTerm::new();
                bd_term.sub_assign(ab_condition_term);
                bd_term.sub_assign(b_term);
                bd_term.add_assign(d_term);

                cs.allocate_main_gate(bd_term)?;
            },
            (Boolean::Is(condition_var), Num::Variable(..), Num::Constant(b_const)) => {
                // (a - b) * condition = a - c
                // (b - a) * condition = b - d 
                // if condition == 0, then a == c, b == d
                // if condition == 1, then b == c, a == d

                // (a-b) * condition - a + c = 0
                // -(a-b) * condition - b + d = 0

                let a_minus_b = a.sub(cs, &b)?;
                let ab_condition_term = ArithmeticTerm::from_variable(a_minus_b.get_variable().get_variable()).mul_by_variable(condition_var.get_variable());
                let a_term = ArithmeticTerm::from_variable(a.get_variable().get_variable());
                let b_term = ArithmeticTerm::constant(*b_const);
                let c_term = ArithmeticTerm::from_variable(c.get_variable().get_variable());
                let d_term = ArithmeticTerm::from_variable(d.get_variable().get_variable());

                let mut ac_term = MainGateTerm::new();
                ac_term.add_assign(ab_condition_term.clone());
                ac_term.sub_assign(a_term);
                ac_term.add_assign(c_term);

                cs.allocate_main_gate(ac_term)?;

                let mut bd_term = MainGateTerm::new();
                bd_term.sub_assign(ab_condition_term);
                bd_term.sub_assign(b_term);
                bd_term.add_assign(d_term);

                cs.allocate_main_gate(bd_term)?;
            },
            (Boolean::Is(condition_var), Num::Constant(a_const), Num::Variable(..)) => {
                // (a - b) * condition = a - c
                // (b - a) * condition = b - d 
                // if condition == 0, then a == c, b == d
                // if condition == 1, then b == c, a == d

                // (a-b) * condition - a + c = 0
                // -(a-b) * condition - b + d = 0

                let a_minus_b = a.sub(cs, &b)?;
                let ab_condition_term = ArithmeticTerm::from_variable(a_minus_b.get_variable().get_variable()).mul_by_variable(condition_var.get_variable());
                let a_term = ArithmeticTerm::constant(*a_const);
                let b_term = ArithmeticTerm::from_variable(b.get_variable().get_variable());
                let c_term = ArithmeticTerm::from_variable(c.get_variable().get_variable());
                let d_term = ArithmeticTerm::from_variable(d.get_variable().get_variable());

                let mut ac_term = MainGateTerm::new();
                ac_term.add_assign(ab_condition_term.clone());
                ac_term.sub_assign(a_term);
                ac_term.add_assign(c_term);

                cs.allocate_main_gate(ac_term)?;

                let mut bd_term = MainGateTerm::new();
                bd_term.sub_assign(ab_condition_term);
                bd_term.sub_assign(b_term);
                bd_term.add_assign(d_term);

                cs.allocate_main_gate(bd_term)?;
            },
            _ => {
                unimplemented!()
            }
        }

        Ok((c, d))
    }

    pub fn equals<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        a: &Self,
        b: &Self
    ) -> Result<Boolean, SynthesisError> {
        match (a, b) {
            (Num::Variable(ref a), Num::Variable(ref b)) => {
                AllocatedNum::equals(cs, a, b)
            },
            (Num::Variable(ref var), Num::Constant(constant)) | 
            (Num::Constant(constant), Num::Variable(ref var)) => {
                let delta = var.sub_constant(cs, *constant)?;

                delta.is_zero(cs)
            },
            (Num::Constant(a), Num::Constant(b)) => {
                let is_equal = a == b;
                Ok(Boolean::Constant(is_equal))
            }
        }
    }

    pub fn add<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        other: &Self,
    ) -> Result<Self, SynthesisError> {
        match (self, other) {
            (Num::Variable(ref a), Num::Variable(ref b)) => {
                let new = a.add(cs, b)?;

                Ok(Num::Variable(new))
            },
            (Num::Variable(ref var), Num::Constant(constant)) | 
            (Num::Constant(constant), Num::Variable(ref var)) => {
                let new = var.add_constant(cs, *constant)?;

                Ok(Num::Variable(new))
            },
            (Num::Constant(a), Num::Constant(b)) => {
                let mut result = *a;
                result.add_assign(&b);

                Ok(Num::Constant(result))
            }
        }
    }

    pub fn sub<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        other: &Self,
    ) -> Result<Self, SynthesisError> {
        match (self, other) {
            (Num::Variable(ref a), Num::Variable(ref b)) => {
                let new = a.sub(cs, b)?;

                Ok(Num::Variable(new))
            },
            (Num::Variable(ref var), Num::Constant(constant)) => {
                let new = var.sub_constant(cs, *constant)?;

                Ok(Num::Variable(new))
            },
            (Num::Constant(constant), Num::Variable(ref var)) => {
                use crate::plonk::circuit::simple_term::Term;
                let mut term = Term::<E>::from_allocated_num(var.clone());
                term.negate();
                term.add_constant(constant);

                let new = term.collapse_into_num(cs)?;

                Ok(new)
            },
            (Num::Constant(a), Num::Constant(b)) => {
                let mut result = *a;
                result.sub_assign(&b);

                Ok(Num::Constant(result))
            }
        }
    }

    pub fn mask_by_boolean_into_accumulator<CS: ConstraintSystem<E>>(&self, cs: &mut CS, boolean: &Boolean, accumulator: &Self) -> Result<Self, SynthesisError>
    {   
        match (self, accumulator, boolean) {
            (Num::Variable(self_var), Num::Variable(accumulator_var), _) => {
                let accumulated = self_var.mask_by_boolean_into_accumulator(cs, boolean, accumulator_var)?;

                Ok(Num::Variable(accumulated))
            },
            (Num::Constant(self_value), Num::Constant(accumulator_value), _) => {
                let mut lc = LinearCombination::zero();
                lc.add_assign_constant(*accumulator_value);
                lc.add_assign_boolean_with_coeff(boolean, *self_value);

                lc.into_num(cs)
            },
            (Num::Constant(self_value), accumulator @ Num::Variable(..), _) => {
                let mut lc = LinearCombination::zero();
                lc.add_assign_number_with_coeff(accumulator, E::Fr::one());
                lc.add_assign_boolean_with_coeff(boolean, *self_value);

                lc.into_num(cs)
            },
            (self_value @ Num::Variable(..), accumulator @ Num::Constant(..), Boolean::Constant(flag)) => {
                let res = if *flag {
                   accumulator.add(cs, &self_value)?
                }
                else {
                    accumulator.clone()
                };
                Ok(res)
            }
            (Num::Variable(self_value), Num::Constant(accumulator), Boolean::Is(bit)) => {
                let mut value = None;
                let result = cs.alloc(|| {
                    let mut tmp = self_value.value.grab()?;
                    let bit_value = bit.get_value().grab()?;
                    if !bit_value {
                        tmp = E::Fr::zero();
                    }

                    tmp.add_assign(accumulator);
                    value = Some(tmp); 
                    Ok(tmp)
                })?;

                let allocated_res = AllocatedNum {
                    value: value,
                    variable: result
                };

                let self_term = ArithmeticTerm::from_variable(
                    self_value.get_variable()).mul_by_variable(bit.get_variable()
                );
                let other_term = ArithmeticTerm::constant(accumulator.clone());
                let result_term = ArithmeticTerm::from_variable(result);
                
                let mut term = MainGateTerm::new();
                term.add_assign(self_term);
                term.add_assign(other_term);
                term.sub_assign(result_term);
        
                cs.allocate_main_gate(term)?;

                Ok(Num::Variable(allocated_res))
            }
            (_, _, _) => {
                unimplemented!();
            }
        }
    }

    pub fn add_two<CS: ConstraintSystem<E>>(&self, cs: &mut CS, first: &Self, second: &Self) -> Result<Self, SynthesisError>
    {
        let res = match (self, first, second) {
            (Num::Constant(x), Num::Constant(y), Num::Constant(z)) => {
                let mut temp = *x;
                temp.add_assign(y);
                temp.add_assign(z);
                Num::Constant(temp)
            },
            (Num::Variable(var), Num::Constant(cnst1), Num::Constant(cnst2)) | 
            (Num::Constant(cnst1), Num::Variable(var), Num::Constant(cnst2)) |
            (Num::Constant(cnst1), Num::Constant(cnst2), Num::Variable(var)) => {
                let mut value = None;

                let addition_result = cs.alloc(|| {
                    let mut tmp = *var.value.get()?;
                    tmp.add_assign(&cnst1);
                    tmp.add_assign(&cnst2);
                    value = Some(tmp);
                    Ok(tmp)
                })?;

                let self_term = ArithmeticTerm::from_variable(var.variable);
                let mut constant = *cnst1;
                constant.add_assign(cnst2);
                let other_term = ArithmeticTerm::constant(constant);
                let result_term = ArithmeticTerm::from_variable(addition_result);
                let mut term = MainGateTerm::new();
                term.add_assign(self_term);
                term.add_assign(other_term);
                term.sub_assign(result_term);

                cs.allocate_main_gate(term)?;

                Num::Variable(AllocatedNum {
                    value: value,
                    variable: addition_result
                })
            },
            (Num::Variable(var1), Num::Variable(var2), Num::Constant(constant)) |
            (Num::Variable(var1), Num::Constant(constant), Num::Variable(var2)) |
            (Num::Constant(constant), Num::Variable(var1), Num::Variable(var2)) => {
                let mut value = None;

                let addition_result = cs.alloc(|| {
                    let mut tmp = *var1.value.get()?;
                    let tmp2 = *var2.value.get()?;
                    tmp.add_assign(&tmp2);
                    tmp.add_assign(constant);
                    value = Some(tmp);
                    Ok(tmp)
                })?;

                let self_term = ArithmeticTerm::from_variable(var1.variable);
                let other_term = ArithmeticTerm::from_variable(var2.variable);
                let constant_term = ArithmeticTerm::constant(*constant);
                let result_term = ArithmeticTerm::from_variable(addition_result);
                let mut term = MainGateTerm::new();
                term.add_assign(self_term);
                term.add_assign(other_term);
                term.add_assign(constant_term);
                term.sub_assign(result_term);

                cs.allocate_main_gate(term)?;

                Num::Variable(AllocatedNum {
                    value: value,
                    variable: addition_result
                })
            },
            (Num::Variable(var1), Num::Variable(var2), Num::Variable(var3)) => {
                let mut value = None;

                let addition_result = cs.alloc(|| {
                    let mut tmp = *var1.value.get()?;
                    let tmp2 = *var2.value.get()?;
                    let tmp3 = *var3.value.get()?;
                    tmp.add_assign(&tmp2);
                    tmp.add_assign(&tmp3);
                    value = Some(tmp);
                    Ok(tmp)
                })?;

                let self_term = ArithmeticTerm::from_variable(var1.variable);
                let other_term = ArithmeticTerm::from_variable(var2.variable);
                let third_term = ArithmeticTerm::from_variable(var3.variable);
                let result_term = ArithmeticTerm::from_variable(addition_result);
                let mut term = MainGateTerm::new();
                term.add_assign(self_term);
                term.add_assign(other_term);
                term.add_assign(third_term);
                term.sub_assign(result_term);

                cs.allocate_main_gate(term)?;

                Num::Variable(AllocatedNum {
                    value: value,
                    variable: addition_result
                })
            },
        };

        Ok(res)
    }

    pub fn negate<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS
    ) -> Result<Self, SynthesisError> {
        Num::Constant(E::Fr::zero()).sub(cs, self)
    }

    pub fn mul<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        other: &Self,
    ) -> Result<Self, SynthesisError> {
        match (self, other) {
            (Num::Variable(ref a), Num::Variable(ref b)) => {
                let new = a.mul(cs, b)?;

                Ok(Num::Variable(new))
            },
            (Num::Variable(ref var), Num::Constant(constant)) | 
            (Num::Constant(constant), Num::Variable(ref var)) => {
                let new = var.mul_constant(cs, *constant)?;

                Ok(Num::Variable(new))
            },
            (Num::Constant(a), Num::Constant(b)) => {
                let mut result = *a;
                result.mul_assign(&b);

                Ok(Num::Constant(result))
            }
        }
    }

    // compute coeff_ab * A * B + coeff_c * C
    pub fn fma_with_coefficients<CS: ConstraintSystem<E>>(
        cs: &mut CS, a: &Self, b: &Self, c: &Self, ab_coeff: E::Fr, c_coeff: E::Fr
    ) -> Result<Self, SynthesisError>
    {
        let result_val = {
            let a_val = a.get_value().grab()?;
            let b_val = b.get_value().grab()?;
            let c_val = c.get_value().grab()?;

            let mut tmp : E::Fr = a_val;
            tmp.mul_assign(&ab_coeff);
            tmp.mul_assign(&b_val);

            let mut tmp2 = c_val;
            tmp2.mul_assign(&c_coeff);
            
            tmp.add_assign(&tmp2);
            Ok(tmp)
        };
        
        // if all of the variables are constant:
        // return constant
        if [a, b, c].iter().all(|x| x.is_constant()) {
            return Ok(Num::Constant(result_val.unwrap()))
        }
        
        let result = AllocatedNum::alloc(cs, || result_val)?;
        let mut gate = MainGateTerm::new();
        let mut cnst = E::Fr::zero();

        // deal with main gate:
        match (a, b) {
            (Num::Constant(a_fr), Num::Constant(b_fr)) => {
                let mut tmp = a_fr.clone();
                tmp.mul_assign(&b_fr);
                tmp.mul_assign(&ab_coeff);
                cnst = tmp;
            },
            (Num::Constant(fr), Num::Variable(var)) | (Num::Variable(var), Num::Constant(fr)) => {
                let mut tmp = fr.clone();
                tmp.mul_assign(&ab_coeff);
                let term = ArithmeticTerm::from_variable_and_coeff(var.get_variable(), tmp);
                gate.add_assign(term);
            },
            (Num::Variable(a_var), Num::Variable(b_var)) => {
                let term = ArithmeticTerm::from_variable_and_coeff(
                    a_var.get_variable(), ab_coeff
                ).mul_by_variable(b_var.get_variable());
                gate.add_assign(term);
            }
        };

        match c {
            Num::Constant(fr) => cnst.add_assign(&fr),
            Num::Variable(var) => {
                let term = ArithmeticTerm::from_variable(var.get_variable());
                gate.add_assign(term);
            },
        };

        let term = ArithmeticTerm::constant(cnst);
        gate.add_assign(term);
        let term = ArithmeticTerm::from_variable(result.get_variable());
        gate.sub_assign(term);
        cs.allocate_main_gate(gate)?;
        
        Ok(Num::Variable(result))
    }

    pub fn assert_not_zero<CS>(
        &self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError>
        where CS: ConstraintSystem<E>
    {
        match self {
            Num::Constant(c) => {
                assert!(!c.is_zero());
            },
            Num::Variable(var) => {
                var.assert_not_zero(cs)?;
            }
        }

        Ok(())
    }

    pub fn assert_is_zero<CS>(
        &self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError>
        where CS: ConstraintSystem<E>
    {
        match self {
            Num::Constant(c) => {
                assert!(c.is_zero());
            },
            Num::Variable(var) => {
                var.assert_is_zero(cs)?;
            }
        }

        Ok(())
    }

    pub fn inverse<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS
    ) -> Result<Self, SynthesisError> {
        match self {
            Num::Constant(c) => {
                assert!(!c.is_zero());
                Ok(Num::Constant(c.inverse().expect("inverse must exist")))
            },
            Num::Variable(var) => {
                let result = var.inverse(cs)?;

                Ok(Num::Variable(result))
            }
        }
    }

    pub fn div<CS>(
        &self,
        cs: &mut CS,
        other: &Self
    ) -> Result<Self, SynthesisError>
        where CS: ConstraintSystem<E>
    {
        match (self, other) {
            (Num::Constant(a), Num::Constant(b)) => {
                let b_inv = b.inverse().expect("inverse must exist");

                let mut result = *a;
                result.mul_assign(&b_inv);

                Ok(Num::Constant(result))
            },
            (Num::Variable(a), Num::Variable(b)) => {
                let result =  a.div(cs, b)?;

                Ok(Num::Variable(result))
            },
            (Num::Variable(a), Num::Constant(b)) => {
                let b_inv = b.inverse().expect("inverse must exist");
                let result = Num::Variable(*a).mul(cs, &Num::Constant(b_inv))?;

                Ok(result)
            },
            (Num::Constant(a), Num::Variable(b)) => {
                let b_inv = b.inverse(cs)?;
                let result = Num::Variable(b_inv).mul(cs, &Num::Constant(*a))?;

                Ok(result)
            }
        }
    }

    // returns 0 if condition == `false` and `a` if condition == `true`
    pub fn mask<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        a: &Self,
        condition: &Boolean
    ) -> Result<Self, SynthesisError> {
        match (a, condition) {
            (Num::Constant(a), Boolean::Constant(flag)) => {
                if *flag {
                    return Ok(Num::Constant(*a));
                } else {
                    return Ok(Num::Constant(E::Fr::zero()));
                }
            },
            (Num::Variable(var), Boolean::Constant(flag)) => {
                if *flag {
                    return Ok(Num::Variable(*var));
                } else {
                    return Ok(Num::Constant(E::Fr::zero()));
                }
            },
            (Num::Variable(var), cond @ Boolean::Is(..)) => {
                return Ok(Num::Variable(AllocatedNum::mask(cs, var, cond)?))
            },
            (Num::Variable(var), cond @ Boolean::Not(..)) => {
                return Ok(Num::Variable(AllocatedNum::mask(cs, var, cond)?))
            },
            (Num::Constant(a), Boolean::Is(flag)) => {
                let a = *a;
                let c = AllocatedNum::alloc(
                    cs,
                    || {
                        if *flag.get_value().get()? {
                            Ok(a)
                        } else {
                            Ok(E::Fr::zero())
                        }
                    }
                )?;

                let mut main_term = MainGateTerm::<E>::new();
                let term = ArithmeticTerm::from_variable_and_coeff(flag.get_variable(), a);
                main_term.add_assign(term);
                main_term.sub_assign(ArithmeticTerm::from_variable(c.get_variable()));

                cs.allocate_main_gate(main_term)?;

                return Ok(Num::Variable(c));
            },
            (Num::Constant(a), Boolean::Not(flag)) => {
                let a = *a;
                let c = AllocatedNum::alloc(
                    cs,
                    || {
                        if *flag.get_value().get()? {
                            Ok(E::Fr::zero())
                        } else {
                            Ok(a)
                        }
                    }
                )?;

                // a - flag*a - c = 0

                let mut main_term = MainGateTerm::<E>::new();
                let term = ArithmeticTerm::from_variable_and_coeff(flag.get_variable(), a);
                main_term.sub_assign(term);
                main_term.sub_assign(ArithmeticTerm::from_variable(c.get_variable()));
                main_term.add_assign(ArithmeticTerm::constant(a));

                cs.allocate_main_gate(main_term)?;

                return Ok(Num::Variable(c));
            },
        }
    }

    pub fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        condition_flag: &Boolean,
        a: &Self,
        b: &Self
    ) -> Result<Self, SynthesisError> {
        match (a, b) {
            (Num::Variable(ref a), Num::Variable(ref b)) => {
                let num = AllocatedNum::conditionally_select(cs, a, b, condition_flag)?;

                Ok(Num::Variable(num))
            },
            (Num::Variable(ref var), Num::Constant(constant)) => {
                match condition_flag {
                    Boolean::Constant(flag) => {
                        if *flag { 
                            Ok(Num::Variable(var.clone()))
                        } else { 
                            Ok(Num::Constant(*constant))
                        }
                    },
                    Boolean::Is(cond) => {
                        // var * flag + constant * (1 - flag) - result = 0

                        let c = AllocatedNum::alloc(
                            cs,
                            || {
                                let a_value = *var.get_value().get()?;
                                let b_value = *constant;
                                if *cond.get_value().get()? {
                                    Ok(a_value)
                                } else {
                                    Ok(b_value)
                                }
                            }
                        )?;
                
                        let mut main_term = MainGateTerm::<E>::new();
                        let term = ArithmeticTerm::from_variable(cond.get_variable()).mul_by_variable(var.get_variable());
                        main_term.add_assign(term);
                        main_term.sub_assign(ArithmeticTerm::from_variable_and_coeff(cond.get_variable(), *constant));
                        main_term.sub_assign(ArithmeticTerm::from_variable(c.get_variable()));
                        main_term.add_assign(ArithmeticTerm::constant(*constant));

                        cs.allocate_main_gate(main_term)?;
        
                        Ok(Num::Variable(c))
                    },
        
                    Boolean::Not(cond) => {
                        // var * (1-cond) + constant * cond - result = 0

                        let c = AllocatedNum::alloc(
                            cs,
                            || {
                                let a_value = *var.get_value().get()?;
                                let b_value = *constant;
                                if *cond.get_value().get()? {
                                    Ok(b_value)
                                } else {
                                    Ok(a_value)
                                }
                            }
                        )?;
                
                        let mut main_term = MainGateTerm::<E>::new();
                        let term = ArithmeticTerm::from_variable(cond.get_variable()).mul_by_variable(var.get_variable());
                        main_term.sub_assign(term);
                        main_term.add_assign(ArithmeticTerm::from_variable_and_coeff(cond.get_variable(), *constant));
                        main_term.sub_assign(ArithmeticTerm::from_variable(c.get_variable()));
                        main_term.add_assign(ArithmeticTerm::from_variable(var.get_variable()));

                        cs.allocate_main_gate(main_term)?;
        
                        Ok(Num::Variable(c))
                    }
                }
            },

            (Num::Constant(..), Num::Variable(..)) => {
                Self::conditionally_select(cs, &condition_flag.not(), b, a)
            },
            (&Num::Constant(a), &Num::Constant(b)) => {
                if a == b {
                    return Ok(Num::Constant(a));
                }
                match condition_flag {
                    Boolean::Constant(flag) => {
                        let result_value = if *flag { 
                            a
                        } else { 
                            b
                        };

                        Ok(Num::Constant(result_value))
                    },
                    Boolean::Is(cond) => {
                        let c = AllocatedNum::alloc(
                            cs,
                            || {
                                if *cond.get_value().get()? {
                                    Ok(a)
                                } else {
                                    Ok(b)
                                }
                            }
                        )?;
        
                        // a * condition + b*(1-condition) = c ->
                        // (a - b) *condition - c + b = 0
        
                        let mut a_minus_b = a;
                        a_minus_b.sub_assign(&b);
        
                        let mut main_term = MainGateTerm::<E>::new();
                        let term = ArithmeticTerm::from_variable_and_coeff(cond.get_variable(), a_minus_b);
                        main_term.add_assign(term);
                        main_term.add_assign(ArithmeticTerm::constant(b));
                        main_term.sub_assign(ArithmeticTerm::from_variable(c.get_variable()));

                        cs.allocate_main_gate(main_term)?;
        
                        Ok(Num::Variable(c))
                    },
        
                    Boolean::Not(cond) => {
                        let c = AllocatedNum::alloc(
                            cs,
                            || {
                                if *cond.get_value().get()? {
                                    Ok(b)
                                } else {
                                    Ok(a)
                                }
                            }
                        )?;
        
                        // b * condition + a*(1-condition) = c ->
                        // (b - a) * condition - c + a = 0
        
                        let mut b_minus_a = b;
                        b_minus_a.sub_assign(&a);
        
                        let mut main_term = MainGateTerm::<E>::new();
                        let term = ArithmeticTerm::from_variable_and_coeff(cond.get_variable(), b_minus_a);
                        main_term.add_assign(term);
        
                        main_term.sub_assign(ArithmeticTerm::from_variable(c.get_variable()));
                        main_term.add_assign(ArithmeticTerm::constant(a));

                        cs.allocate_main_gate(main_term)?;
        
                        Ok(Num::Variable(c))
                    }
                }
            }
        }
    }

    pub fn alloc_multiple<CS: ConstraintSystem<E>, const N: usize>(
        cs: &mut CS,
        witness: Option<[E::Fr; N]>
    ) -> Result<[Self; N], SynthesisError> {
        let mut result = [Num::Constant(E::Fr::zero()); N];
        for (idx, r) in result.iter_mut().enumerate() {
            let witness = witness.map(|el| el[idx]);
            *r = Num::alloc(cs, witness)?;
        }
    
        Ok(result)
    }

    pub fn get_value_multiple<const N: usize>(
        els: &[Self; N]
    ) -> Option<[E::Fr; N]> {
        let mut result = [E::Fr::zero(); N];
        for (r, el) in result.iter_mut().zip(els.iter()) {
            if let Some(value) = el.get_value() {
                *r = value;
            } else {
                return None
            }
        }
    
        Some(result)
    }

    pub fn get_value_for_slice(
        els: &[Self]
    ) -> Option<Vec<E::Fr>> {
        let mut result = vec![];
        for el in els.iter() {
            if let Some(value) = el.get_value() {
                result.push(value);
            } else {
                return None;
            }
        }
    
        Some(result)
    }

    pub fn into_bits_le<CS>(
        &self,
        cs: &mut CS,
        bit_length: Option<usize>,
    ) -> Result<Vec<Boolean>, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        if let Some(bit_length) = bit_length {
            assert!(bit_length <= E::Fr::NUM_BITS as usize);
        }

        match self {
            Num::Variable(ref var) => {
                var.into_bits_le(cs, bit_length)
            },
            Num::Constant(c) => {
                use crate::plonk::circuit::utils::fe_to_lsb_first_bits;
                if let Some(bit_length) = bit_length {
                    assert!(c.into_repr().num_bits() as usize <= bit_length);
                }

                let bits = fe_to_lsb_first_bits(c);

                let mut result = vec![];
                for b in bits.into_iter() {
                    result.push(Boolean::constant(b));
                }

                if let Some(bit_length) = bit_length {
                    assert!(result.len() >= bit_length);
                    result.truncate(bit_length);
                }

                Ok(result)
            }
        }
    }

    pub fn conditionally_select_multiple<CS: ConstraintSystem<E>, const N: usize>(
        cs: &mut CS,
        flag: &Boolean,
        a: &[Self; N],
        b: &[Self; N]
    ) -> Result<[Self; N], SynthesisError> {
        let mut result = [Num::zero(); N];

        for ((a, b), r) in (a.iter().zip(b.iter())).zip(result.iter_mut()) {
            *r = Num::conditionally_select(cs, flag, a, b)?;
        }

        Ok(result)
    }
}

impl<E: Engine> From<Boolean> for Num<E>  {
    fn from(b: Boolean) -> Num<E> {
        match b {
            Boolean::Constant(cnst_flag) => {
                let value = if cnst_flag {E::Fr::one()} else {E::Fr::zero()};
                Num::Constant(value)
            },
            Boolean::Is(is) => {
                let var = AllocatedNum {
                    value : is.get_value_as_field_element::<E>(),
                    variable : is.get_variable(),
                };
                Num::Variable(var)
            },
            Boolean::Not(_) => unimplemented!("convertion from Boolean::Not into Num is not supported yet"),
        }
    }
}


#[derive(Debug)]
pub struct AllocatedNum<E: Engine> {
    pub(crate) value: Option<E::Fr>,
    pub(crate) variable: Variable
}

impl<E: Engine> Clone for AllocatedNum<E> {
    fn clone(&self) -> Self {
        AllocatedNum {
            value: self.value,
            variable: self.variable
        }
    }
}

impl<E: Engine> Copy for AllocatedNum<E> {}

impl<E: Engine> AllocatedNum<E> {
    pub fn get_variable(&self) -> Variable {
        self.variable
    }

    pub fn get_value(&self) -> Option<E::Fr> {
        self.value
    }
    
    pub fn alloc<CS, F>(
        cs: &mut CS,
        value: F,
    ) -> Result<Self, SynthesisError>
        where CS: ConstraintSystem<E>,
            F: FnOnce() -> Result<E::Fr, SynthesisError>
    {
        let mut new_value = None;
        let var = cs.alloc(
            || {
                let tmp = value()?;

                new_value = Some(tmp);

                Ok(tmp)
            }
        )?;

        Ok(AllocatedNum {
            value: new_value,
            variable: var
        })
    }

    pub fn alloc_input<CS, F>(
        cs: &mut CS,
        value: F,
    ) -> Result<Self, SynthesisError>
        where CS: ConstraintSystem<E>,
            F: FnOnce() -> Result<E::Fr, SynthesisError>
    {
        let mut new_value = None;
        let var = cs.alloc_input(
            || {
                let tmp = value()?;

                new_value = Some(tmp);

                Ok(tmp)
            }
        )?;

        Ok(AllocatedNum {
            value: new_value,
            variable: var
        })
    }

    pub fn from_boolean_is(boolean: Boolean) -> Self {
        match boolean {
            Boolean::Is(var) => {
                AllocatedNum {
                    value: var.get_value_as_field_element::<E>(),
                    variable: var.get_variable()
                }
            },
            _ => {
                panic!("Can not convert boolean constant or boolean NOT")
            }
        }
    }

    pub fn alloc_cnst<CS>(
        cs: &mut CS, fr: E::Fr,
    ) -> Result<Self, SynthesisError>
        where CS: ConstraintSystem<E>
    {
        let var = cs.alloc(|| { Ok(fr.clone()) })?;

        let self_term = ArithmeticTerm::<E>::from_variable(var);
        let other_term = ArithmeticTerm::constant(fr.clone());
        let mut term = MainGateTerm::new();
        term.add_assign(self_term);
        term.sub_assign(other_term);

        cs.allocate_main_gate(term)?;

        Ok(AllocatedNum {
            value: Some(fr),
            variable: var
        })
    }

    pub fn inputize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        let input = Self::alloc_input(
            cs,
            || {
                Ok(*self.get_value().get()?)
            }
        )?;

        self.enforce_equal(cs, &input)?;

        Ok(())
    }

    // allocate a variable with value "one"
    pub fn one<CS: ConstraintSystem<E>>(cs: &mut CS) -> Self {
        AllocatedNum {
            value: Some(E::Fr::one()),
            variable: cs.get_explicit_one().expect("must get an explicit one from CS"),
        }
    }

    // allocate a variable with value "zero"
    pub fn zero<CS: ConstraintSystem<E>>(cs: &mut CS) -> Self {
        AllocatedNum {
            value: Some(E::Fr::zero()),
            variable: cs.get_explicit_zero().expect("must get an explicit zero from CS"),
        }
    }

    #[track_caller]
    pub fn enforce_equal<CS>(
        &self,
        cs: &mut CS,
        other: &Self
    ) -> Result<(), SynthesisError>
        where CS: ConstraintSystem<E>
    {
        if self.get_variable() == other.get_variable() {
            return Ok(())
        }
        match (self.get_value(), other.get_value()) {
            (Some(a), Some(b)) => {
                assert_eq!(a, b);
            },
            _ => {}
        }
        let self_term = ArithmeticTerm::from_variable(self.variable);
        let other_term = ArithmeticTerm::from_variable(other.variable);
        let mut term = MainGateTerm::new();
        term.add_assign(self_term);
        term.sub_assign(other_term);

        cs.allocate_main_gate(term)?;

        Ok(())
    }

    pub fn inverse<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS
    ) -> Result<Self, SynthesisError> {
        let new_value = if let Some(value) = self.get_value() {
            let t = value.inverse();
            if let Some(inv) = t {
                Some(inv)
            } else {
                dbg!("Tried to inverse", value);
                return Err(SynthesisError::DivisionByZero);
            }

            // Some(t)
        } else {
            None
        };

        let new_allocated = Self::alloc(
            cs,
            || {
                Ok(*new_value.get()?)
            }
        )?;

        let self_by_inv = ArithmeticTerm::from_variable(self.variable).mul_by_variable(new_allocated.variable);
        let constant_term = ArithmeticTerm::constant(E::Fr::one());
        let mut term = MainGateTerm::new();
        term.add_assign(self_by_inv);
        term.sub_assign(constant_term);

        cs.allocate_main_gate(term)?;

        Ok(new_allocated)
    }

    pub fn assert_not_zero<CS>(
        &self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError>
        where CS: ConstraintSystem<E>
    {
        let _ = self.inverse(cs)?;

        Ok(())
    }

    pub fn assert_is_zero<CS>(
        &self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError>
        where CS: ConstraintSystem<E>
    {
        self.assert_equal_to_constant(cs, E::Fr::zero())?;

        Ok(())
    }

    #[track_caller]
    pub fn assert_equal_to_constant<CS>(
        &self,
        cs: &mut CS,
        constant: E::Fr
    ) -> Result<(), SynthesisError>
        where CS: ConstraintSystem<E>
    {
        if let Some(v) = self.get_value() {
            assert_eq!(v, constant);
        }
        let self_term = ArithmeticTerm::from_variable(self.variable);
        let other_term = ArithmeticTerm::constant(constant);
        let mut term = MainGateTerm::new();
        term.add_assign(self_term);
        term.sub_assign(other_term);

        cs.allocate_main_gate(term)?;

        Ok(())
    }

    pub fn is_zero<CS>(
        &self,
        cs: &mut CS,
    ) -> Result<Boolean, SynthesisError>
        where CS: ConstraintSystem<E> 
    {

        let flag_value = self.get_value().map(|x| x.is_zero());
        let flag = AllocatedBit::alloc(cs, flag_value)?;

        let inv_value = if let Some(value) = self.get_value() {
            let inv = value.inverse();
            
            if inv.is_some() {
                inv
            } else {
                Some(E::Fr::zero())
            }
        } else {
            None
        };

        let inv = Self::alloc(
            cs,
            || {
                Ok(*inv_value.get()?)
            }
        )?;

        //  inv * X = (1 - flag) => inv * X + flag - 1 = 0
        //  flag * X = 0

        // | a != 0 | inv = a^-1 | flag = 0 | - valid assignment, satisfiable

        // | a != 0 | inv != a^-1 | flag = 0 | - invalid assignment, but not satisfiable
        // | a != 0 | inv != a^-1 | flag = 1 | - invalid assignment, but not satisfiable

        // | a = 0 | inv = 0 | flag = 1 | - valid assignment, satisfiable

        // | a = 0 | inv != 0 | flag = 1 | - invalid assignment, but not satisfiable
        // | a = 0 | inv != 0 | flag = 0 | - invalid assignment, but not satisfiable

        
        let a_term = ArithmeticTerm::from_variable(self.variable).mul_by_variable(inv.variable);
        let b_term = ArithmeticTerm::from_variable(flag.get_variable());
        let c_term = ArithmeticTerm::constant(E::Fr::one());
        let mut term = MainGateTerm::new();
        term.add_assign(a_term);
        term.add_assign(b_term);
        term.sub_assign(c_term);
        cs.allocate_main_gate(term)?;

        let self_term = ArithmeticTerm::from_variable(self.variable).mul_by_variable(flag.get_variable());
        let res_term = ArithmeticTerm::constant(E::Fr::zero());
        let mut term = MainGateTerm::new();
        term.add_assign(self_term);
        term.sub_assign(res_term);
        cs.allocate_main_gate(term)?;

        Ok(flag.into())
    }

    /// Takes two allocated numbers (a, b) and returns
    /// (b, a) if the condition is true, and (a, b)
    /// otherwise.
    pub fn conditionally_reverse<CS>(
        cs: &mut CS,
        a: &Self,
        b: &Self,
        condition: &Boolean
    ) -> Result<(Self, Self), SynthesisError>
        where CS: ConstraintSystem<E>
    {
        if condition.is_constant() {
            let swap = condition.get_value().expect("must get a value of the constant");

            if swap {
                return Ok((b.clone(), a.clone()))
            } else {
                return Ok((a.clone(), b.clone()))
            }
        }

        if is_selector_specialized_gate::<E, CS>() {
            let c = Self::conditionally_select(cs, &b, &a, &condition)?;
            let d = Self::conditionally_select(cs, &a, &b, &condition)?;

            return Ok((c, d));
        }

        let c = Self::alloc(
            cs,
            || {
                if *condition.get_value().get()? {
                    Ok(*b.value.get()?)
                } else {
                    Ok(*a.value.get()?)
                }
            }
        )?;

        let d = Self::alloc(
            cs,
            || {
                if *condition.get_value().get()? {
                    Ok(*a.value.get()?)
                } else {
                    Ok(*b.value.get()?)
                }
            }
        )?;

        let a_minus_b = a.sub(cs, &b)?;

        // (a - b) * condition = a - c
        // (b - a) * condition = b - d 
        // if condition == 0, then a == c, b == d
        // if condition == 1, then b == c, a == d

        match condition {
            Boolean::Constant(..) => {
                unreachable!("constant is already handled")
            },
            Boolean::Is(condition_var) => {
                // no modifications
                // (a - b) * condition = a - c
                // (b - a) * condition = b - d 
                // if condition == 0, then a == c, b == d
                // if condition == 1, then b == c, a == d

                // (a-b) * condition - a + c = 0
                // -(a-b) * condition - b + d = 0

                let ab_condition_term = ArithmeticTerm::from_variable(a_minus_b.get_variable()).mul_by_variable(condition_var.get_variable());
                let a_term = ArithmeticTerm::from_variable(a.get_variable());
                let b_term = ArithmeticTerm::from_variable(b.get_variable());
                let c_term = ArithmeticTerm::from_variable(c.get_variable());
                let d_term = ArithmeticTerm::from_variable(d.get_variable());

                let mut ac_term = MainGateTerm::new();
                ac_term.add_assign(ab_condition_term.clone());
                ac_term.sub_assign(a_term);
                ac_term.add_assign(c_term);

                cs.allocate_main_gate(ac_term)?;

                let mut bd_term = MainGateTerm::new();
                bd_term.sub_assign(ab_condition_term);
                bd_term.sub_assign(b_term);
                bd_term.add_assign(d_term);

                cs.allocate_main_gate(bd_term)?;
            },

            Boolean::Not(condition_var) => {
                // modifications
                // (a - b) * (1 - condition) = a - c
                // (b - a) * (1 - condition) = b - d 

                // -(a-b) * condition - b + c = 0
                // (a-b) * condition - a + d = 0

                let ab_condition_term = ArithmeticTerm::from_variable(a_minus_b.get_variable()).mul_by_variable(condition_var.get_variable());
                let a_term = ArithmeticTerm::from_variable(a.get_variable());
                let b_term = ArithmeticTerm::from_variable(b.get_variable());
                let c_term = ArithmeticTerm::from_variable(c.get_variable());
                let d_term = ArithmeticTerm::from_variable(d.get_variable());

                let mut ac_term = MainGateTerm::new();
                ac_term.sub_assign(ab_condition_term.clone());
                ac_term.sub_assign(b_term);
                ac_term.add_assign(c_term);

                cs.allocate_main_gate(ac_term)?;

                let mut bd_term = MainGateTerm::new();
                bd_term.add_assign(ab_condition_term);
                bd_term.sub_assign(a_term);
                bd_term.add_assign(d_term);

                cs.allocate_main_gate(bd_term)?;
            }
        }
        Ok((c, d))
    }

    // returns a==b
    pub fn equals<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        a: &Self,
        b: &Self,
    ) -> Result<Boolean, SynthesisError> {
        let delta = a.sub(cs, b)?;

        delta.is_zero(cs)
    }

    pub fn add<CS>(
        &self,
        cs: &mut CS,
        other: &Self
    ) -> Result<Self, SynthesisError>
        where CS: ConstraintSystem<E>
    {
        let mut value = None;

        let addition_result = cs.alloc(|| {
            let mut tmp = *self.value.get()?;
            tmp.add_assign(other.value.get()?);

            value = Some(tmp);

            Ok(tmp)
        })?;

        let self_term = ArithmeticTerm::from_variable(self.variable);
        let other_term = ArithmeticTerm::from_variable(other.variable);
        let result_term = ArithmeticTerm::from_variable(addition_result);
        let mut term = MainGateTerm::new();
        term.add_assign(self_term);
        term.add_assign(other_term);
        term.sub_assign(result_term);

        cs.allocate_main_gate(term)?;

        Ok(AllocatedNum {
            value: value,
            variable: addition_result
        })
    }

    pub fn sub<CS>(
        &self,
        cs: &mut CS,
        other: &Self
    ) -> Result<Self, SynthesisError>
        where CS: ConstraintSystem<E>
    {
        let mut value = None;

        let subtraction_result = cs.alloc(|| {
            let mut tmp = *self.value.get()?;
            tmp.sub_assign(other.value.get()?);

            value = Some(tmp);

            Ok(tmp)
        })?;

        let self_term = ArithmeticTerm::from_variable(self.variable);
        let other_term = ArithmeticTerm::from_variable(other.variable);
        let result_term = ArithmeticTerm::from_variable(subtraction_result);
        let mut term = MainGateTerm::new();
        term.add_assign(self_term);
        term.sub_assign(other_term);
        term.sub_assign(result_term);

        cs.allocate_main_gate(term)?;

        Ok(AllocatedNum {
            value: value,
            variable: subtraction_result
        })
    }

    pub fn add_constant<CS>(
        &self,
        cs: &mut CS,
        constant: E::Fr
    ) -> Result<Self, SynthesisError>
        where CS: ConstraintSystem<E>
    {
        let mut value = None;

        let addition_result = cs.alloc(|| {
            let mut tmp = *self.value.get()?;
            tmp.add_assign(&constant);

            value = Some(tmp);

            Ok(tmp)
        })?;

        let self_term = ArithmeticTerm::from_variable(self.variable);
        let other_term = ArithmeticTerm::constant(constant);
        let result_term = ArithmeticTerm::from_variable(addition_result);
        let mut term = MainGateTerm::new();
        term.add_assign(self_term);
        term.add_assign(other_term);
        term.sub_assign(result_term);

        cs.allocate_main_gate(term)?;

        Ok(AllocatedNum {
            value: value,
            variable: addition_result
        })
    }

    pub fn sub_constant<CS>(
        &self,
        cs: &mut CS,
        constant: E::Fr
    ) -> Result<Self, SynthesisError>
        where CS: ConstraintSystem<E>
    {
        let mut c = constant;
        c.negate();

        self.add_constant(cs, c)
    }

    pub fn fma<CS: ConstraintSystem<E>>(&self, cs: &mut CS, b: Self, c: Self) -> Result<Self, SynthesisError>
    {     
        let mut value = None;

        let result = cs.alloc(|| {
            let mut tmp = *self.value.get()?;
            let tmp2 = b.value.get()?;
            let tmp3 = c.value.get()?;
            tmp.mul_assign(&tmp2);
            tmp.add_assign(&tmp3);
            value = Some(tmp);
            Ok(tmp)
        })?;

        let self_term = ArithmeticTerm::from_variable(self.get_variable()).mul_by_variable(b.get_variable());
        let other_term = ArithmeticTerm::from_variable(c.variable);
        let result_term = ArithmeticTerm::from_variable(result);
        let mut term = MainGateTerm::new();
        term.add_assign(self_term);
        term.add_assign(other_term);
        term.sub_assign(result_term);

        cs.allocate_main_gate(term)?;

        Ok(AllocatedNum {
            value: value,
            variable: result
        })
    }

    // compute coeff_ab * A * B + coeff_c * C
    pub fn fma_with_coefficients<CS: ConstraintSystem<E>>(&self, cs: &mut CS, b: (E::Fr, Self), c: (E::Fr, Self)) -> Result<Self, SynthesisError>
    {     
        let mut value = None;

        let (ab_coeff, b) = b;
        let (c_coeff, c) = c;

        let result = cs.alloc(|| {
            let mut tmp = *self.value.get()?;
            let tmp2 = b.value.get()?;
            let mut tmp3 = *c.value.get()?;
            tmp3.mul_assign(&c_coeff);
            tmp.mul_assign(&tmp2);
            tmp.mul_assign(&ab_coeff);
            tmp.add_assign(&tmp3);
            value = Some(tmp);

            Ok(tmp)
        })?;

        let self_term = ArithmeticTerm::from_variable_and_coeff(self.get_variable(), ab_coeff).mul_by_variable(b.get_variable());
        let other_term = ArithmeticTerm::from_variable_and_coeff(c.variable, c_coeff);
        let result_term = ArithmeticTerm::from_variable(result);
        let mut term = MainGateTerm::new();
        term.add_assign(self_term);
        term.add_assign(other_term);
        term.sub_assign(result_term);

        cs.allocate_main_gate(term)?;

        Ok(AllocatedNum {
            value: value,
            variable: result
        })
    }

    pub fn mask_by_boolean_into_accumulator<CS: ConstraintSystem<E>>(&self, cs: &mut CS, boolean: &Boolean, accumulator: &Self) -> Result<Self, SynthesisError>
    {   
        match boolean {
            Boolean::Constant(flag) => {
                if *flag {
                    return self.add(cs, accumulator);
                } else {
                    return Ok(accumulator.clone());
                }
            },
            Boolean::Is(bit) => {
                let mut value = None;
                let bit_value = bit.get_value();
        
                let result = cs.alloc(|| {
                    let mut tmp = *self.value.get()?;
                    let bit_value = bit_value.get()?;
                    let acc_value = accumulator.value.get()?;
                    if !bit_value {
                        tmp = E::Fr::zero();
                    }
                    tmp.add_assign(&acc_value);
                    value = Some(tmp);
        
                    Ok(tmp)
                })?;
        
                let self_term = ArithmeticTerm::from_variable(self.get_variable()).mul_by_variable(bit.get_variable());
                let other_term = ArithmeticTerm::from_variable(accumulator.variable);
                let result_term = ArithmeticTerm::from_variable(result);
                let mut term = MainGateTerm::new();
                term.add_assign(self_term);
                term.add_assign(other_term);
                term.sub_assign(result_term);
        
                cs.allocate_main_gate(term)?;
        
                Ok(AllocatedNum {
                    value: value,
                    variable: result
                })
            },
            Boolean::Not(not_bit) => {
                let mut value = None;
                let not_bit_value = not_bit.get_value();
        
                let result = cs.alloc(|| {
                    let mut tmp = *self.value.get()?;
                    let not_bit_value = not_bit_value.get()?;
                    let acc_value = accumulator.value.get()?;
                    if *not_bit_value {
                        tmp = E::Fr::zero();
                    }
                    tmp.add_assign(&acc_value);
                    value = Some(tmp);
        
                    Ok(tmp)
                })?;

                // a - a*bit + accumulator -> new

                let mut minus_one = E::Fr::one();
                minus_one.negate();
        
                let self_term = ArithmeticTerm::from_variable_and_coeff(self.get_variable(), minus_one).mul_by_variable(not_bit.get_variable());
                let a_term = ArithmeticTerm::from_variable(self.get_variable());
                let other_term = ArithmeticTerm::from_variable(accumulator.variable);
                let result_term = ArithmeticTerm::from_variable(result);
                let mut term = MainGateTerm::new();
                term.add_assign(self_term);
                term.add_assign(a_term);
                term.add_assign(other_term);
                term.sub_assign(result_term);
        
                cs.allocate_main_gate(term)?;
        
                Ok(AllocatedNum {
                    value: value,
                    variable: result
                })
            }
        }  
    }

    pub fn add_two<CS: ConstraintSystem<E>>(&self, cs: &mut CS, x: Self, y: Self) -> Result<Self, SynthesisError>
    {     
        let mut value = None;

        let addition_result = cs.alloc(|| {
            let mut tmp = *self.value.get()?;
            let tmp2 = x.value.get()?;
            let tmp3 = y.value.get()?;
            tmp.add_assign(&tmp2);
            tmp.add_assign(&tmp3);
            value = Some(tmp);
            Ok(tmp)
        })?;

        let self_term = ArithmeticTerm::from_variable(self.variable);
        let other_term = ArithmeticTerm::from_variable(x.variable);
        let third_term = ArithmeticTerm::from_variable(y.variable);
        let result_term = ArithmeticTerm::from_variable(addition_result);
        let mut term = MainGateTerm::new();
        term.add_assign(self_term);
        term.add_assign(other_term);
        term.add_assign(third_term);
        term.sub_assign(result_term);

        cs.allocate_main_gate(term)?;

        Ok(AllocatedNum {
            value: value,
            variable: addition_result
        })
    }

    pub fn mul_constant<CS>(
        &self,
        cs: &mut CS,
        constant: E::Fr
    ) -> Result<Self, SynthesisError>
        where CS: ConstraintSystem<E>
    {
        let mut value = None;

        let result = cs.alloc(|| {
            let mut tmp = *self.value.get()?;
            tmp.mul_assign(&constant);

            value = Some(tmp);

            Ok(tmp)
        })?;

        let self_term = ArithmeticTerm::from_variable_and_coeff(self.variable, constant);
        let result_term = ArithmeticTerm::from_variable(result);
        let mut term = MainGateTerm::new();
        term.add_assign(self_term);
        term.sub_assign(result_term);

        cs.allocate_main_gate(term)?;

        Ok(AllocatedNum {
            value: value,
            variable: result
        })
    }

    pub fn mul<CS>(
        &self,
        cs: &mut CS,
        other: &Self
    ) -> Result<Self, SynthesisError>
        where CS: ConstraintSystem<E>
    {
        let mut value = None;

        let product = cs.alloc(|| {
            let mut tmp = *self.value.get()?;
            tmp.mul_assign(other.value.get()?);

            value = Some(tmp);

            Ok(tmp)
        })?;

        let self_term = ArithmeticTerm::from_variable(self.variable).mul_by_variable(other.variable);
        let result_term = ArithmeticTerm::from_variable(product);
        let mut term = MainGateTerm::new();
        term.add_assign(self_term);
        term.sub_assign(result_term);

        cs.allocate_main_gate(term)?;

        Ok(AllocatedNum {
            value: value,
            variable: product
        })
    }

    pub fn square<CS>(
        &self,
        cs: &mut CS,
    ) -> Result<Self, SynthesisError>
        where CS: ConstraintSystem<E>
    {
        self.mul(cs, &self)
    }


    /// Takes two allocated numbers (a, b) and returns
    /// a if the condition is true, and b
    /// otherwise.
    /// Most often to be used with b = 0
    pub fn conditionally_select<CS>(
        cs: &mut CS,
        a: &Self,
        b: &Self,
        condition: &Boolean
    ) -> Result<Self, SynthesisError>
        where CS: ConstraintSystem<E>
    {
        // we quickly work on a special case if we actually do not select anything
        if a.get_variable() == b.get_variable() {
            return Ok(a.clone());
        }

        if is_selector_specialized_gate::<E, CS>() {
            return Self::conditionally_select_for_special_main_gate(cs, a, b, condition);
        }

        // code below is valid if a variable != b variable
        let res = match condition {
            Boolean::Constant(flag) => if *flag { a.clone() } else { b.clone() },
            
            Boolean::Is(cond) => {
                let c = Self::alloc(
                    cs,
                    || {
                        if *cond.get_value().get()? {
                            Ok(*a.value.get()?)
                        } else {
                            Ok(*b.value.get()?)
                        }
                    }
                )?;

                // a * condition + b*(1-condition) = c ->
                // (a - b) *condition - c + b = 0

                let a_minus_b = a.sub(cs, b)?;

                let mut main_term = MainGateTerm::<E>::new();
                let term = ArithmeticTerm::from_variable(a_minus_b.get_variable()).mul_by_variable(cond.get_variable());
                main_term.add_assign(term);
                main_term.sub_assign(ArithmeticTerm::from_variable(c.get_variable()));
                main_term.add_assign(ArithmeticTerm::from_variable(b.get_variable()));

                cs.allocate_main_gate(main_term)?;

                self::stats::increment_counter();

                c
            },

            Boolean::Not(cond) => {
                let c = Self::alloc(
                    cs,
                    || {
                        if *cond.get_value().get()? {
                            Ok(*b.value.get()?)
                        } else {
                            Ok(*a.value.get()?)
                        }
                    }
                )?;

                // b * condition + a*(1-condition) = c ->
                // ( b - a) * condition - c + a = 0

                let b_minus_a = b.sub(cs, a)?;

                let mut main_term = MainGateTerm::<E>::new();
                let term = ArithmeticTerm::from_variable(b_minus_a.get_variable()).mul_by_variable(cond.get_variable());
                main_term.add_assign(term);
                main_term.sub_assign(ArithmeticTerm::from_variable(c.get_variable()));
                main_term.add_assign(ArithmeticTerm::from_variable(a.get_variable()));

                cs.allocate_main_gate(main_term)?;

                self::stats::increment_counter();

                c
            }
        };
        
        Ok(res)
    }

    fn conditionally_select_for_special_main_gate<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        a: &Self,
        b: &Self,
        condition: &Boolean
    ) -> Result<Self, SynthesisError> {
        use bellman::plonk::better_better_cs::cs::GateInternal;
        use bellman::plonk::better_better_cs::gates::selector_optimized_with_d_next::SelectorOptimizedWidth4MainGateWithDNext;

        assert!(is_selector_specialized_gate::<E, CS>());

        let mg = CS::MainGate::default();

        // we can have a relationship as a + b + c + d + ab + ac + const + d_next = 0

        // code below is valid if a variable != b variable
        let res = match condition {
            Boolean::Constant(flag) => if *flag { a.clone() } else { b.clone() },
            
            Boolean::Is(cond) => {

                let c = Self::alloc(
                    cs,
                    || {
                        if *cond.get_value().get()? {
                            Ok(*a.value.get()?)
                        } else {
                            Ok(*b.value.get()?)
                        }
                    }
                )?;

                // a * condition + b*(1-condition) = c ->
                // (a - b) *condition - c + b = 0

                // that has to be formatted as 
                // A (var) = condition
                // B = a
                // C = b
                // D = c

                // coefficients
                // [0, 0, 1, -1, 1, -1, 0, 0]

                // so AB - AC => condition * a - condition * b
                // then we make +b and -c

                let dummy = CS::get_dummy_variable();

                let mut vars = CS::MainGate::dummy_vars_to_inscribe(dummy);
                let mut coeffs = CS::MainGate::empty_coefficients();

                let mut minus_one = E::Fr::one();
                minus_one.negate();

                coeffs[2] = E::Fr::one();
                coeffs[3] = minus_one;
                coeffs[SelectorOptimizedWidth4MainGateWithDNext::AB_MULTIPLICATION_TERM_COEFF_INDEX] = E::Fr::one();
                coeffs[SelectorOptimizedWidth4MainGateWithDNext::AC_MULTIPLICATION_TERM_COEFF_INDEX] = minus_one;

                vars[0] = cond.get_variable();
                vars[1] = a.get_variable();
                vars[2] = b.get_variable();
                vars[3] = c.get_variable();

                cs.new_single_gate_for_trace_step(
                    &mg, 
                    &coeffs, 
                    &vars,
                    &[]
                )?;

                c
            },

            Boolean::Not(cond) => {
                let c = Self::alloc(
                    cs,
                    || {
                        if *cond.get_value().get()? {
                            Ok(*b.value.get()?)
                        } else {
                            Ok(*a.value.get()?)
                        }
                    }
                )?;

                // b * condition + a*(1-condition) = c ->
                // (b - a) * condition - c + a = 0

                // that has to be formatted as 
                // A (var) = condition
                // B = a
                // C = b
                // D = c

                // coefficients
                // [0, 1, 0, -1, -1, 1, 0, 0]

                let dummy = CS::get_dummy_variable();

                let mut vars = CS::MainGate::dummy_vars_to_inscribe(dummy);
                let mut coeffs = CS::MainGate::empty_coefficients();

                let mut minus_one = E::Fr::one();
                minus_one.negate();

                coeffs[1] = E::Fr::one();
                coeffs[3] = minus_one;
                coeffs[SelectorOptimizedWidth4MainGateWithDNext::AB_MULTIPLICATION_TERM_COEFF_INDEX] = minus_one;
                coeffs[SelectorOptimizedWidth4MainGateWithDNext::AC_MULTIPLICATION_TERM_COEFF_INDEX] = E::Fr::one();

                vars[0] = cond.get_variable();
                vars[1] = a.get_variable();
                vars[2] = b.get_variable();
                vars[3] = c.get_variable();

                cs.new_single_gate_for_trace_step(
                    &mg, 
                    &coeffs, 
                    &vars,
                    &[]
                )?;

                c
            }
        };
        
        Ok(res)
    }

    /// Masks a value with a Boolean
    pub fn mask<CS>(
        cs: &mut CS,
        a: &Self,
        condition: &Boolean
    ) -> Result<Self, SynthesisError>
        where CS: ConstraintSystem<E>
    {
        // code below is valid if a variable != b variable
        let res = match condition {
            Boolean::Constant(flag) => if *flag { a.clone() } else { AllocatedNum::zero(cs) },
            
            Boolean::Is(cond) => {
                let c = Self::alloc(
                    cs,
                    || {
                        if *cond.get_value().get()? {
                            Ok(*a.value.get()?)
                        } else {
                            Ok(E::Fr::zero())
                        }
                    }
                )?;

                // c = a * condition
                // a * condition - c = 0

                let mut main_term = MainGateTerm::<E>::new();
                let term = ArithmeticTerm::from_variable(a.get_variable()).mul_by_variable(cond.get_variable());
                main_term.add_assign(term);
                main_term.sub_assign(ArithmeticTerm::from_variable(c.get_variable()));

                cs.allocate_main_gate(main_term)?;

                c
            },

            Boolean::Not(cond) => {
                let c = Self::alloc(
                    cs,
                    || {
                        if *cond.get_value().get()? {
                            Ok(E::Fr::zero())
                        } else {
                            Ok(*a.value.get()?)
                        }
                    }
                )?;

                // a * (1 - condition) = c
                // a * (1-condition) - c = 0
                // -a * condition + a - c = 0

                let mut main_term = MainGateTerm::<E>::new();
                let term = ArithmeticTerm::from_variable(a.get_variable()).mul_by_variable(cond.get_variable());
                main_term.sub_assign(term);

                main_term.sub_assign(ArithmeticTerm::from_variable(c.get_variable()));
                main_term.add_assign(ArithmeticTerm::from_variable(a.get_variable()));

                cs.allocate_main_gate(main_term)?;

                c
            }
        };
        
        Ok(res)
    }

    pub fn div<CS>(
        &self,
        cs: &mut CS,
        other: &Self
    ) -> Result<Self, SynthesisError>
        where CS: ConstraintSystem<E>
    {
        let mut value = None;

        let quotient= cs.alloc(|| {
            let mut tmp = *other.value.get()?;
            tmp = *tmp.inverse().get()?;
        
            tmp.mul_assign(self.value.get()?);

            value = Some(tmp);

            Ok(tmp)
        })?;

        let self_term = ArithmeticTerm::from_variable(quotient).mul_by_variable(other.variable);
        let result_term = ArithmeticTerm::from_variable(self.variable);
        let mut term = MainGateTerm::new();
        term.add_assign(self_term);
        term.sub_assign(result_term);

        cs.allocate_main_gate(term)?;

        Ok(AllocatedNum {
            value: value,
            variable: quotient
        })
    }

    // Montgomery double and add algorithm
    pub fn pow<CS, F>(cs: &mut CS, base: &Self, d: F) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>, F: AsRef<[Boolean]>
    {
        let mut r0 = Self::one(cs);
        let mut r1 = base.clone();

        for b in d.as_ref().iter() {
            // RO = RO * R1 if b == 1 else R0^2
            // R1 = R1^2 if b == 1 else R0 * R1
            let r0_squared = r0.square(cs)?;
            let r1_squared = r1.square(cs)?;
            let r0_times_r1 = r0.mul(cs, &r1)?;
            
            r0 = AllocatedNum::conditionally_select(
                cs,
                &r0_times_r1,
                &r0_squared,
                b,
            )?;

            r1 = AllocatedNum::conditionally_select(
                cs,
                &r1_squared,
                &r0_times_r1,
                b,
            )?;
        }

        Ok(r0)
    }

    /// Return (fixed) amount of bits of the allocated number.
    /// Can be used when there is a priori knowledge of bit length of the number
    pub fn into_bits_le<CS>(
        &self,
        cs: &mut CS,
        bit_length: Option<usize>,
    ) -> Result<Vec<Boolean>, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        if let Some(bit_length) = bit_length {
            assert!(bit_length <= E::Fr::NUM_BITS as usize);
        }
        
        let bits = boolean::field_into_allocated_bits_le_fixed(cs, self.value, bit_length)?;

        let mut minus_one = E::Fr::one();
        minus_one.negate();

        let mut packed_lc = LinearCombination::zero();
        packed_lc.add_assign_variable_with_coeff(self, minus_one);

        let mut coeff = E::Fr::one();

        for bit in bits.iter() {
            packed_lc.add_assign_bit_with_coeff(bit, coeff);

            coeff.double();
        }

        packed_lc.enforce_zero(cs)?;

        Ok(bits.into_iter().map(|b| Boolean::from(b)).collect())
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

    #[test]
    fn test_multiplication() {
        let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        let in_0: Fr = rng.gen();
        let in_1: Fr = rng.gen();

        let mut out = in_0;
        out.mul_assign(&in_1);

        {
            let mut cs = TrivialAssembly::<Bn256, 
            PlonkCsWidth4WithNextStepParams,
                Width4MainGateWithDNext
            >::new();

            let this = AllocatedNum::alloc(&mut cs, 
                || Ok(in_0)
            ).unwrap();

            let other = AllocatedNum::alloc(&mut cs, 
                || Ok(in_1)
            ).unwrap();

            let result = this.mul(&mut cs, &other).unwrap();

            assert_eq!(result.get_value().unwrap(), out);

            assert!(cs.is_satisfied());
        }
    }

    #[test]
    fn check_explicits() {
        use crate::bellman::pairing::bn256::{Bn256, Fr};
        use crate::bellman::plonk::better_better_cs::cs::*;

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
                let z = AllocatedNum::zero(cs);
                dbg!(cs.get_value(z.get_variable())?);
                let o = AllocatedNum::one(cs);
                dbg!(cs.get_value(o.get_variable())?);

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

        let _proof = assembly.create_proof::<_, RollingKeccakTranscript<Fr>>(
            &worker, 
            &setup, 
            &crs_mons,
            None
        ).unwrap();
    }
}