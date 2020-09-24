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

use super::boolean::{self, AllocatedBit, Boolean};
use super::linear_combination::*;

use crate::circuit::{
    Assignment
};

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
                let allocated = AllocatedNum::alloc(cs, 
                || {
                    Ok(*constant)
                })?;

                allocated.assert_equal_to_constant(cs, *constant)?;
                let num = AllocatedNum::conditionally_select(cs, var, &allocated, condition_flag)?;

                Ok(Num::Variable(num))
            },

            (Num::Constant(constant), Num::Variable(ref var)) => {
                let allocated = AllocatedNum::alloc(cs, 
                || {
                    Ok(*constant)
                })?;

                allocated.assert_equal_to_constant(cs, *constant)?;
                let num = AllocatedNum::conditionally_select(cs, &allocated, var, condition_flag)?;

                Ok(Num::Variable(num))
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
        
                        Ok(Num::Variable(c))
                    }
                }
            }
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

    pub fn enforce_equal<CS>(
        &self,
        cs: &mut CS,
        other: &Self
    ) -> Result<(), SynthesisError>
        where CS: ConstraintSystem<E>
    {
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

    pub fn assert_equal_to_constant<CS>(
        &self,
        cs: &mut CS,
        constant: E::Fr
    ) -> Result<(), SynthesisError>
        where CS: ConstraintSystem<E>
    {
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
        // let flag = AllocatedBit::alloc_unchecked(cs, flag_value)?;
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

        let proof = assembly.create_proof::<_, RollingKeccakTranscript<Fr>>(
            &worker, 
            &setup, 
            &crs_mons,
            None
        ).unwrap();
    }
}