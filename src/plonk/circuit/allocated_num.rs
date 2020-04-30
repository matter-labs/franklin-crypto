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
        Width4MainGateWithDNextEquation
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
                Width4MainGateWithDNextEquation
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