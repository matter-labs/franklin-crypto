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

use super::boolean::{self, AllocatedBit, Boolean};
use super::linear_combination::*;

use crate::circuit::{
    Assignment
};

pub const STATE_WIDTH : usize = 4;


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

        // match condition {
        //     Boolean::Constant(..) => {
        //         unreachable!("constant is already handles")
        //     },
        //     Boolean::Is(condition_var) => {
        //         // no modifications
        //         // (a - b) * condition = a - c
        //         // (b - a) * condition = b - d 
        //         // if condition == 0, then a == c, b == d
        //         // if condition == 1, then b == c, a == d

        //         // (a-b) * condition - a + c = 0
        //         // -(a-b) * condition - b + d = 0

        //         let ab_condition_term = ArithmeticTerm::from_variable(a_minus_b.get_variable()).mul_by_variable(condition_var.get_variable());
        //         let a_term = ArithmeticTerm::from_variable(a.get_variable());
        //         let b_term = ArithmeticTerm::from_variable(b.get_variable());
        //         let c_term = ArithmeticTerm::from_variable(c.get_variable());
        //         let d_term = ArithmeticTerm::from_variable(d.get_variable());

        //         let mut ac_term = MainGateTerm::new();
        //         ac_term.add_assign(ab_condition_term.clone());
        //         ac_term.sub_assign(a_term);
        //         ac_term.add_assign(c_term);

        //         cs.allocate_main_gate(ac_term)?;

        //         let mut bd_term = MainGateTerm::new();
        //         bd_term.sub_assign(ab_condition_term);
        //         bd_term.sub_assign(b_term);
        //         bd_term.add_assign(d_term);

        //         cs.allocate_main_gate(bd_term)?;
        //     },

        //     Boolean::Not(condition_var) => {
        //         // modifications
        //         // (a - b) * (1 - condition) = a - c
        //         // (b - a) * (1 - condition) = b - d 

        //         // -(a-b) * condition - b + c = 0
        //         // (a-b) * condition - a + d = 0

        //         let ab_condition_term = ArithmeticTerm::from_variable(a_minus_b.get_variable()).mul_by_variable(condition_var.get_variable());
        //         let a_term = ArithmeticTerm::from_variable(a.get_variable());
        //         let b_term = ArithmeticTerm::from_variable(b.get_variable());
        //         let c_term = ArithmeticTerm::from_variable(c.get_variable());
        //         let d_term = ArithmeticTerm::from_variable(d.get_variable());

        //         let mut ac_term = MainGateTerm::new();
        //         ac_term.sub_assign(ab_condition_term.clone());
        //         ac_term.sub_assign(b_term);
        //         ac_term.add_assign(c_term);

        //         cs.allocate_main_gate(ac_term)?;

        //         let mut bd_term = MainGateTerm::new();
        //         bd_term.add_assign(ab_condition_term);
        //         bd_term.sub_assign(a_term);
        //         bd_term.add_assign(d_term);

        //         cs.allocate_main_gate(bd_term)?;
        //     }
        // }

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


    // compute coeff_ab * A * B + coeff_c * C
    pub fn mask_by_boolean_into_accumulator<CS: ConstraintSystem<E>>(&self, cs: &mut CS, boolean: &Boolean, accumulator: &Self) -> Result<Self, SynthesisError>
    {   
        match (self, accumulator) {
            (Num::Variable(self_var), Num::Variable(accumulator_var)) => {
                let accumulated = self_var.mask_by_boolean_into_accumulator(cs, boolean, accumulator_var)?;

                Ok(Num::Variable(accumulated))
            },
            (Num::Constant(self_value), Num::Constant(accumulator_value)) => {
                let mut lc = LinearCombination::zero();
                lc.add_assign_constant(*accumulator_value);
                lc.add_assign_boolean_with_coeff(boolean, *self_value);

                lc.into_num(cs)
            },
            (Num::Constant(self_value), accumulator @ Num::Variable(..)) => {
                let mut lc = LinearCombination::zero();
                lc.add_assign_number_with_coeff(accumulator, E::Fr::one());
                lc.add_assign_boolean_with_coeff(boolean, *self_value);

                lc.into_num(cs)
            },
            _ => {
                unimplemented!()
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
                        main_term.sub_assign(ArithmeticTerm::from_variable_and_coeff(cond.get_variable(), *constant));
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

    pub fn lc<CS: ConstraintSystem<E>>(cs: &mut CS, input_coeffs: &[E::Fr], inputs: &[Num<E>]) -> Result<Self, SynthesisError>
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
            let tmp = AllocatedNum::quartic_lc_with_cnst(cs, &coeffs[..], &vars[..], &constant_term)?;

            constant_term = E::Fr::zero();
            vars = vec![tmp];
            coeffs = vec![E::Fr::one()];
        }

        // pad with dummy variables
        for _i in vars.len()..(STATE_WIDTH-1) {
            vars.push(AllocatedNum::zero(cs));
            coeffs.push(E::Fr::zero());
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

        vars.push(res_var.clone());
        coeffs.push(minus_one);
        coeffs.reverse();
        vars.reverse();
        
        AllocatedNum::general_lc_gate(cs, &coeffs[..], &vars[..], &constant_term, &E::Fr::zero(), &dummy)?;
        Ok(Num::Variable(res_var))
    }

    // same as lc but with all the coefficients set to be 1
    pub fn sum<CS: ConstraintSystem<E>>(cs: &mut CS, nums: &[Num<E>]) -> Result<Self, SynthesisError>
    {
        let coeffs = vec![E::Fr::one(); nums.len()];
        Self::lc(cs, &coeffs[..], &nums[..])
    }

    // for given array of slices : [x0, x1, x2, ..., xn] of arbitrary length, base n and total accumulated x
    // validates that x = x0 + x1 * base + x2 * base^2 + ... + xn * base^n
    pub fn long_weighted_sum<CS>(cs: &mut CS, vars: &[Self], base: &E::Fr) -> Result<Self, SynthesisError>
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

    pub fn alloc_from_lc<CS: ConstraintSystem<E>>(
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

        let r = self.mul(cs, &new_allocated)?;

        r.assert_equal_to_constant(cs, E::Fr::one())?;

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
                unreachable!("constant is already handles")
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

    // compute coeff_ab * A * B + coeff_c * C
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

    // given vector of coefs: [c0, c1, c2, c3],
    // vector of vars: [var0, var1, var2, var3],
    // next row var and coef: c4 and var4
    // and additional constant: cnst
    // constrcut the gate asserting that: 
    // c0 * var0 + c1 * var1 + c2 * var3 + c4 * var4 + cnst = 0
    // here the state is [var0, var1, var2, var3]
    // and var4 should be placed on the next row with the help of d_next
    pub fn general_lc_gate<CS: ConstraintSystem<E>>(
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
    pub fn quartic_lc_with_cnst<CS: ConstraintSystem<E>>(
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

    pub fn quartic_lc<CS: ConstraintSystem<E>>(
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

    pub fn quartic_lc_eq<CS: ConstraintSystem<E>>(
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

    pub fn ternary_lc_eq<CS: ConstraintSystem<E>>(
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

    pub fn ternary_lc_with_cnst<CS: ConstraintSystem<E>>(
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

    // for given array of slices : [x0, x1, x2, ..., xn] of arbitrary length, base n and total accumulated x
    // validates that x = x0 + x1 * base + x2 * base^2 + ... + xn * base^n
    // use_d_next flag allows to place total on the next row, without expicitely constraiting it and leaving
    // is as a job for the next gate allocation.
    pub fn long_weighted_sum_eq<CS: ConstraintSystem<E>>(
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

        let proof = assembly.create_proof::<_, RollingKeccakTranscript<Fr>>(
            &worker, 
            &setup, 
            &crs_mons,
            None
        ).unwrap();
    }
}