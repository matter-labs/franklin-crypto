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
    Index, 
    ConstraintSystem,
    ArithmeticTerm,
    MainGateTerm
};

use crate::circuit::{
    Assignment
};

use super::boolean::*;
use std::sync::Once;

#[derive(Clone, Debug)]
pub enum Num<E: Engine> {
    Variable(AllocatedNum<E>),
    Constant(E::Fr)
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

    pub fn is_constant(&self) -> bool {
        match self {
            Num::Variable(..) => false,
            Num::Constant(..) => true
        }
    }

    pub fn is_zero<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Boolean, SynthesisError> {
        let flag = match self {
            Num::Constant(c) => Ok(Boolean::constant(c.is_zero())),
            Num::Variable(var) => var.is_zero(cs),
        };

        flag
    }

    pub(crate) fn get_constant_value(&self) -> E::Fr {
        match self {
            Num::Variable(..) => panic!("is variable"),
            Num::Constant(c) => *c
        }
    }

    pub(crate) fn get_variable(&self) -> AllocatedNum<E> {
        match self {
            Num::Constant(..) => {
                panic!("constant")
            },
            Num::Variable(v) => {
                v.clone()
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

    // allocate public variable with value "one"
    pub fn one<CS: ConstraintSystem<E>>(cs: &mut CS) -> Self {
    
        static INIT: Once = Once::new();
        static mut VAR: Option<Variable> = None;

        unsafe {
            INIT.call_once(|| {
                let temp = Self::alloc_input(cs, || Ok(E::Fr::one())).expect("should alloc");
                VAR = Some(temp.get_variable());
            });
        }

        let var = unsafe {
            VAR.unwrap()
        };
     
        AllocatedNum {
            value: Some(E::Fr::one()),
            variable: var,
        }
    }

    // allocate public variable with value "one"
    pub fn zero<CS: ConstraintSystem<E>>(cs: &mut CS) -> Self {
    
        static INIT: Once = Once::new();
        static mut VAR: Option<Variable> = None;

        unsafe {
            INIT.call_once(|| {
                let temp = Self::alloc_input(cs, || Ok(E::Fr::zero())).expect("should alloc");
                VAR = Some(temp.get_variable());
            });
        }

        let var = unsafe {
            VAR.unwrap()
        };
     
        AllocatedNum {
            value: Some(E::Fr::zero()),
            variable: var,
        }
    }

    // used as placeholder in some circumstances
    pub fn dumb() -> Self 
    { 
        AllocatedNum {
            value: None,
            variable: Variable::new_unchecked(Index::Aux(0)),
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
            let t = value.inverse().unwrap();

            Some(t)
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
        let flag = AllocatedBit::alloc_unchecked(cs, flag_value)?;


        let inv_value = if let Some(value) = self.get_value() {
            //value.inverse()
            Some(E::Fr::zero())
        } else {
            Some(E::Fr::zero())
        };

        let inv = Self::alloc(
            cs,
            || {
                Ok(*inv_value.get()?)
            }
        )?;

    

        //  inv * X = (1 - flag) => inv * X + flag - 1 = 0
        //  flag * X = 0
        
        let a_term = ArithmeticTerm::from_variable(self.variable).mul_by_variable(inv.variable);
        let b_term = ArithmeticTerm::from_variable(flag.get_variable());
        let c_term = ArithmeticTerm::constant(E::Fr::one());
        let mut term = MainGateTerm::new();
        term.add_assign(a_term);
        term.add_assign(b_term);
        term.sub_assign(c_term);
        cs.allocate_main_gate(term)?;

        let self_term = ArithmeticTerm::from_variable(self.variable).mul_by_variable(flag.get_variable());
        let res_term = ArithmeticTerm::constant(E::Fr::one());
        let mut term = MainGateTerm::new();
        term.add_assign(self_term);
        term.sub_assign(res_term);
        cs.allocate_main_gate(term)?;

        Ok(flag.into())
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

        let substraction_result = cs.alloc(|| {
            let mut tmp = *self.value.get()?;
            tmp.sub_assign(other.value.get()?);

            value = Some(tmp);

            Ok(tmp)
        })?;

        let self_term = ArithmeticTerm::from_variable(self.variable);
        let other_term = ArithmeticTerm::from_variable(other.variable);
        let result_term = ArithmeticTerm::from_variable(substraction_result);
        let mut term = MainGateTerm::new();
        term.add_assign(self_term);
        term.sub_assign(other_term);
        term.sub_assign(result_term);

        cs.allocate_main_gate(term)?;

        Ok(AllocatedNum {
            value: value,
            variable: substraction_result
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
        let mut value = None;

        let substraction_result = cs.alloc(|| {
            let mut tmp = *self.value.get()?;
            tmp.sub_assign(&constant);

            value = Some(tmp);

            Ok(tmp)
        })?;

        let self_term = ArithmeticTerm::from_variable(self.variable);
        let mut constant = constant.clone();
        constant.negate();
        let other_term = ArithmeticTerm::constant(constant);
        let result_term = ArithmeticTerm::from_variable(substraction_result);
        let mut term = MainGateTerm::new();
        term.add_assign(self_term);
        term.add_assign(other_term);
        term.sub_assign(result_term);

        cs.allocate_main_gate(term)?;

        Ok(AllocatedNum {
            value: value,
            variable: substraction_result
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

    // returns c * x * y, where c = const
    pub fn mul_scaled<CS>(
        cs: &mut CS,
        x: &Self, 
        y: &Self,
        c: &E::Fr,
    ) -> Result<Self, SynthesisError>
        where CS: ConstraintSystem<E>
    {
        let mut out_value = None;
        let out = cs.alloc(|| {
            let mut x_val = *x.value.get()?;
            let mut y_val = *y.value.get()?;

            let mut tmp = x_val;
            tmp.mul_assign(&y_val);
            tmp.mul_assign(c);

            out_value = Some(tmp);
            Ok(tmp)
        })?;

        let mut mul_term = ArithmeticTerm::from_variable(x.variable).mul_by_variable(y.variable);
        mul_term.scale(c);
        let out_term = ArithmeticTerm::from_variable(out);
        
        let mut term = MainGateTerm::new();
        term.add_assign(mul_term);
        term.sub_assign(out_term);
        cs.allocate_main_gate(term)?;

        Ok(AllocatedNum {
            value: out_value,
            variable: out,
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
                let mut term = ArithmeticTerm::from_variable(a_minus_b.get_variable()).mul_by_variable(cond.get_variable());
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
                let mut term = ArithmeticTerm::from_variable(b_minus_a.get_variable()).mul_by_variable(cond.get_variable());
                main_term.add_assign(term);

                main_term.sub_assign(ArithmeticTerm::from_variable(c.get_variable()));
                main_term.add_assign(ArithmeticTerm::from_variable(a.get_variable()));

                c
            }
        };
        
        Ok(res)

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

    // out = q_m * a * b + q_a * a + q_b *b + q_c * c
    pub fn general_equation<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        a: &Self,
        b: &Self,
        c: &Self,
        q_m : &E::Fr,
        q_a: &E::Fr,
        q_b: &E::Fr,
        q_c: &E::Fr,
        q_const: &E::Fr,
    ) -> Result<Self, SynthesisError> {

        let mut out_value = None;

        let out = cs.alloc(|| {
            let mut a_val = *a.value.get()?;
            let mut b_val = *b.value.get()?;
            let mut c_val = *c.value.get()?;
            let mut total = E::Fr::zero();

            let mut tmp = a_val.clone();
            tmp.mul_assign(&b_val);
            tmp.mul_assign(q_m);
            total.add_assign(&tmp);

            tmp = a_val.clone();
            tmp.mul_assign(q_a);
            total.add_assign(&tmp);

            tmp = b_val.clone();
            tmp.mul_assign(q_b);
            total.add_assign(&tmp);

            tmp = c_val.clone();
            tmp.mul_assign(q_c);
            tmp.add_assign(q_const);
            total.add_assign(&tmp);

            out_value = Some(total);
            Ok(total)
        })?;

        let mut main_term = MainGateTerm::new();

        let mut term = ArithmeticTerm::from_variable(a.variable).mul_by_variable(b.variable);
        term.scale(q_m);
        main_term.add_assign(term);

        let mut term = ArithmeticTerm::from_variable(a.variable);
        term.scale(q_a);
        main_term.add_assign(term);

        let mut term = ArithmeticTerm::from_variable(b.variable);
        term.scale(q_b);
        main_term.add_assign(term);

        let mut term = ArithmeticTerm::from_variable(c.variable);
        term.scale(q_c);
        main_term.add_assign(term);

        let term = ArithmeticTerm::constant(*q_const);
        main_term.add_assign(term);

        let term = ArithmeticTerm::from_variable(out);
        main_term.sub_assign(term);

        cs.allocate_main_gate(main_term)?;

        Ok(AllocatedNum {
            value: out_value,
            variable: out,
        })
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
}