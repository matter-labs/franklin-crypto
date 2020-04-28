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

use super::allocated_num::*;
use super::linear_combination::*;

// a*X + b that is more lightweight than linear
// combination but allows to better work with constants and scaling
#[derive(Clone, Debug)]
pub struct Term<E: Engine> {
    num: Num<E>,
    coeff: E::Fr,
    constant_term: E::Fr,
}

impl<E: Engine> Term<E> {
    pub fn is_constant(&self) -> bool {
        match self.num {
            Num::Constant(..) => true,
            _ => false
        }
    }

    fn from_constant(val: E::Fr) -> Self {
        Self {
            num: Num::Constant(val),
            coeff: E::Fr::one(),
            constant_term: E::Fr::zero()
        }
    }

    fn from_allocated_num(n: AllocatedNum<E>) -> Self {
        Self {
            num: Num::Variable(n),
            coeff: E::Fr::one(),
            constant_term: E::Fr::zero()
        }
    }

    fn from_num(n: Num<E>) -> Self {
        Self {
            num: n,
            coeff: E::Fr::one(),
            constant_term: E::Fr::zero()
        }
    }

    fn get_constant_value(&self) -> E::Fr {
        match self.num {
            Num::Constant(c) => {
                let mut tmp = self.coeff;
                tmp.mul_assign(&c);
                tmp.add_assign(&self.constant_term);

                tmp
            },
            _ => {panic!("variable")}
        }
    }

    fn get_variable(&self) -> AllocatedNum<E> {
        match self.num {
            Num::Constant(..) => {
                panic!("constant")
            },
            Num::Variable(v) => {
                v.clone()
            }
        }
    }

    fn get_value(&self) -> Option<E::Fr> {
        match self.num {
            Num::Constant(..) => {
                Some(self.get_constant_value())
            },
            Num::Variable(v) => {
                if let Some(v) = v.get_value() {
                    let mut tmp = self.coeff;
                    tmp.mul_assign(&v);
                    tmp.add_assign(&self.constant_term);

                    Some(tmp)
                } else {
                    None
                }
            }
        }
    }

    pub fn collapse_into_num<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS
    ) -> Result<Num<E>, SynthesisError> {
        if self.is_constant() {
            return Ok(Num::Constant(self.get_constant_value()));
        }

        if self.coeff == E::Fr::one() && self.constant_term == E::Fr::zero() {
            return Ok(self.num.clone());
        }

        let mut value = None;

        let coeff = self.coeff;
        let constant_term = self.constant_term;

        let result = cs.alloc(|| {
            let mut tmp = *self.get_value().get()?;

            value = Some(tmp);

            Ok(tmp)
        })?;

        let self_term = ArithmeticTerm::from_variable_and_coeff(self.get_variable().get_variable(), coeff);
        let constant_term = ArithmeticTerm::constant(constant_term);
        let result_term = ArithmeticTerm::from_variable(result);
        let mut term = MainGateTerm::new();
        term.add_assign(self_term);
        term.add_assign(constant_term);
        term.sub_assign(result_term);

        cs.allocate_main_gate(term)?;

        let allocated = AllocatedNum::<E> {
            variable: result,
            value: value
        };

        Ok(Num::Variable(allocated))
    }

    pub fn add<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        other: &Self
    ) -> Result<Self, SynthesisError> {
        let this_is_constant = self.is_constant();
        let other_is_constant = other.is_constant();

        match (this_is_constant, other_is_constant) {
            (true, true) => {
                let mut v = self.get_constant_value();
                v.add_assign(&other.get_constant_value());

                return Ok(Self::from_constant(v))
            },
            (true, false) | (false, true) => {
                let c = if this_is_constant {
                    self.get_constant_value()
                } else {
                    other.get_constant_value()
                };

                let mut non_constant = if this_is_constant {
                    other.clone()
                } else {
                    self.clone()
                };

                non_constant.constant_term.add_assign(&c);

                let num = non_constant.collapse_into_num(cs)?;

                return Ok(Self::from_num(num));
            },
            (false, false) => {
                let mut lc = LinearCombination::<E>::zero();
                lc.add_assign_number_with_coeff(&self.num, self.coeff);
                lc.add_assign_number_with_coeff(&other.num, other.coeff);
                lc.add_assign_constant(self.constant_term);
                lc.add_assign_constant(other.constant_term);

                let num = lc.into_num(cs)?;

                return Ok(Self::from_num(num));
            }
        }
    }

    pub fn add_multiple<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        other: &[Self]
    ) -> Result<Self, SynthesisError> {
        let mut lc = LinearCombination::<E>::zero();
        for o in other.iter() {
            if o.is_constant() {
                lc.add_assign_constant(o.get_constant_value());
            } else {
                lc.add_assign_number_with_coeff(&o.num, o.coeff);
                lc.add_assign_constant(o.constant_term);
            }
        }

        let num = lc.into_num(cs)?;

        return Ok(Self::from_num(num));
    }
}