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

use crate::plonk::circuit::Assignment;

use super::allocated_num::*;
use super::linear_combination::*;
use super::boolean::Boolean;

// a*X + b that is more lightweight than linear
// combination but allows to better work with constants and scaling
#[derive(Clone, Debug)]
pub struct Term<E: Engine> {
    pub(crate) num: Num<E>,
    pub(crate) coeff: E::Fr,
    pub(crate) constant_term: E::Fr,
}


impl<E: Engine> std::fmt::Display for Term<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Term {{ ")?;
        write!(f, "Num = {}, ", self.num)?;
        write!(f, "Coeff = {}, ", self.coeff)?;
        write!(f, "Constant = {}, ", self.constant_term)?;
        writeln!(f, "}}")
    }
}

impl<E: Engine> Term<E> {
    pub fn is_constant(&self) -> bool {
        match self.num {
            Num::Constant(..) => true,
            _ => false
        }
    }

    pub fn from_constant(val: E::Fr) -> Self {
        Self {
            num: Num::Constant(val),
            coeff: E::Fr::one(),
            constant_term: E::Fr::zero()
        }
    }

    pub fn from_allocated_num(n: AllocatedNum<E>) -> Self {
        Self {
            num: Num::Variable(n),
            coeff: E::Fr::one(),
            constant_term: E::Fr::zero()
        }
    }

    pub fn from_num(n: Num<E>) -> Self {
        Self {
            num: n,
            coeff: E::Fr::one(),
            constant_term: E::Fr::zero()
        }
    }

    pub fn allocate<CS: ConstraintSystem<E>>(cs: &mut CS, witness: Option<E::Fr>) -> Result<Self, SynthesisError> {
        let num = Num::alloc(cs, witness)?;

        Ok(Self::from_num(num))
    }

    pub fn zero() -> Self {
        Self::from_num(Num::<E>::Constant(E::Fr::zero()))
    }

    pub fn from_boolean(b: &Boolean) -> Self {
        match b {
            Boolean::Constant(c) => {
                if *c {
                    Self::from_constant(E::Fr::one())
                } else {
                    Self::from_constant(E::Fr::zero())
                }
            },
            Boolean::Is(bit) => {
                let var = bit.get_variable();
                let val = bit.get_value_as_field_element::<E>();

                let allocated = AllocatedNum::<E> {
                    variable: var,
                    value: val
                };

                Self::from_allocated_num(allocated)
            },
            Boolean::Not(bit) => {
                let var = bit.get_variable();
                let val = bit.get_value_as_field_element::<E>();

                let allocated = AllocatedNum::<E> {
                    variable: var,
                    value: val
                };

                let mut tmp = Self::from_allocated_num(allocated);
                tmp.negate();
                tmp.add_constant(&E::Fr::one());

                tmp
            },

        }
    }

    pub(crate) fn get_constant_value(&self) -> E::Fr {
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

    pub fn into_constant_value(&self) -> E::Fr {
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

    #[track_caller]
    pub fn into_num(&self) -> Num<E> {
        let one = E::Fr::one();
        assert!(self.coeff == one, "term must not containt coefficient to cast into Num");
        assert!(self.constant_term.is_zero(), "term must not containt additive constant to cast into Num");

        self.num.clone()
    }

    #[track_caller]
    pub(crate) fn get_variable(&self) -> AllocatedNum<E> {
        match &self.num {
            Num::Constant(..) => {
                panic!("this term is constant")
            },
            Num::Variable(v) => {
                v.clone()
            }
        }
    }

    #[track_caller]
    pub fn into_variable(&self) -> AllocatedNum<E> {
        match &self.num {
            Num::Constant(..) => {
                panic!("this term is constant")
            },
            Num::Variable(v) => {
                assert_eq!(E::Fr::one(), self.coeff);
                assert!(self.constant_term.is_zero());
                v.clone()
            }
        }
    }

    pub fn scale(&mut self, by: &E::Fr) {
        self.coeff.mul_assign(&by);
        self.constant_term.mul_assign(&by);
    }

    pub fn add_constant(&mut self, c: &E::Fr) {
        self.constant_term.add_assign(&c);
    }

    pub fn negate(&mut self) {
        self.coeff.negate();
        self.constant_term.negate();
    }

    pub fn get_value(&self) -> Option<E::Fr> {
        match &self.num {
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

        let mut new_value = None;

        let result_var = cs.alloc(|| {
            let tmp = *self.get_value().get()?;

            new_value = Some(tmp);

            Ok(tmp)
        })?;

        let self_term = ArithmeticTerm::from_variable_and_coeff(self.get_variable().get_variable(), self.coeff);
        let constant_term = ArithmeticTerm::constant(self.constant_term);
        let result_term = ArithmeticTerm::from_variable(result_var);
        let mut term = MainGateTerm::new();
        term.add_assign(self_term);
        term.add_assign(constant_term);
        term.sub_assign(result_term);

        cs.allocate_main_gate(term)?;

        let allocated = AllocatedNum::<E> {
            variable: result_var,
            value: new_value
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

                non_constant.add_constant(&c);

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

    pub fn sub<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        other: &Self
    ) -> Result<Self, SynthesisError> {
        let mut other = other.clone();
        other.negate();

        self.add(cs, &other)
    }

    pub fn add_multiple<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        other: &[Self]
    ) -> Result<Self, SynthesisError> {
        if other.len() == 0 {
            return Ok(self.clone());
        }
        let mut lc = LinearCombination::<E>::zero();
        lc.add_assign_number_with_coeff(&self.num, self.coeff);
        lc.add_assign_constant(self.constant_term);
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

    pub fn mul<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        other: &Self
    ) -> Result<Self, SynthesisError> {
        Self::fma(cs, self, other, &Self::zero())
    }

    pub fn fma<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        mul_x: &Self,
        mul_y: &Self,
        add_z: &Self
    ) -> Result<Self, SynthesisError> {
        let x_is_constant = mul_x.is_constant();
        let y_is_constant = mul_y.is_constant();
        let z_is_constant = add_z.is_constant();

        match (x_is_constant, y_is_constant, z_is_constant) {
            (true, true, true) => {
                let mut result = mul_x.get_constant_value();
                result.mul_assign(&mul_y.get_constant_value());
                result.add_assign(&add_z.get_constant_value());

                let n = Self::from_constant(result);

                return Ok(n);
            },
            (true, true, false) => {
                let mut value = mul_x.get_constant_value();
                value.mul_assign(&mul_y.get_constant_value());

                let mut result = add_z.clone();
                result.add_constant(&value);

                return Ok(result);
            },
            (true, false, true) | (false, true, true)=> {
                let additive_constant = add_z.get_constant_value();
                let multiplicative_constant = if x_is_constant {
                    mul_x.get_constant_value()
                } else {
                    mul_y.get_constant_value()
                };

                let mut result = if x_is_constant {
                    mul_y.clone()
                } else {
                    mul_x.clone()
                };

                result.scale(&multiplicative_constant);
                result.add_constant(&additive_constant);

                return Ok(result);
            },
            (true, false, false) | (false, true, false) => {
                let multiplicative_constant = if x_is_constant {
                    mul_x.get_constant_value()
                } else {
                    mul_y.get_constant_value()
                };

                let mut tmp = if x_is_constant {
                    mul_y.clone()
                } else {
                    mul_x.clone()
                };

                tmp.scale(&multiplicative_constant);

                let tmp = tmp.add(cs, &add_z)?;

                return Ok(tmp);
            },
            (false, false, true) => {
                let mut mul_coeff = mul_x.coeff;
                mul_coeff.mul_assign(&mul_y.coeff);

                let mut x_coeff = mul_x.coeff;
                x_coeff.mul_assign(&mul_y.constant_term);

                let mut y_coeff = mul_y.coeff;
                y_coeff.mul_assign(&mul_x.constant_term);

                let mut constant_coeff = mul_x.constant_term;
                constant_coeff.mul_assign(&mul_y.constant_term);
                constant_coeff.add_assign(&add_z.get_constant_value());

                let x_var = mul_x.get_variable().get_variable();
                let y_var = mul_y.get_variable().get_variable();

                let new_value = match (mul_x.get_value(), mul_y.get_value(), add_z.get_value()) {
                    (Some(x), Some(y), Some(z)) => {
                        let mut new_value = x;
                        new_value.mul_assign(&y);
                        new_value.add_assign(&z);

                        Some(new_value)
                    },
                    _ => {None}
                };

                let allocated_num = AllocatedNum::alloc(
                    cs, 
                    || {
                        Ok(*new_value.get()?)
                    }
                )?;

                let mut term = MainGateTerm::<E>::new();
                let mul_term = ArithmeticTerm::<E>::from_variable_and_coeff(x_var, mul_coeff).mul_by_variable(y_var);
                let x_term = ArithmeticTerm::<E>::from_variable_and_coeff(x_var, x_coeff);
                let y_term = ArithmeticTerm::<E>::from_variable_and_coeff(y_var, y_coeff);
                let n_term = ArithmeticTerm::<E>::from_variable(allocated_num.get_variable());
                let const_term = ArithmeticTerm::constant(constant_coeff);

                term.add_assign(mul_term);
                term.add_assign(x_term);
                term.add_assign(y_term);
                term.add_assign(const_term);
                term.sub_assign(n_term);

                cs.allocate_main_gate(term)?;

                let new = Self::from_allocated_num(allocated_num);

                return Ok(new);
            },
            (false, false, false) => {
                // each term is something like a*X + b
                // in this case we have do manually unroll it

                // (a_0 * X + b_0) * (a_1 * Y + b_1) + (a_2 * Z + b_2) = 

                // a_0 * X * a_1 * Y + (a_0 * X * b_1 + a_1 * Y * b_0 + a_2 * Z) + (b_0 * b_1 + b_2)

                let mut mul_coeff = mul_x.coeff;
                mul_coeff.mul_assign(&mul_y.coeff);

                let mut x_coeff = mul_x.coeff;
                x_coeff.mul_assign(&mul_y.constant_term);

                let mut y_coeff = mul_y.coeff;
                y_coeff.mul_assign(&mul_x.constant_term);

                let mut constant_coeff = mul_x.constant_term;
                constant_coeff.mul_assign(&mul_y.constant_term);
                constant_coeff.add_assign(&add_z.constant_term);

                let x_var = mul_x.get_variable().get_variable();
                let y_var = mul_y.get_variable().get_variable();
                let z_var = add_z.get_variable().get_variable();

                let new_value = match (mul_x.get_value(), mul_y.get_value(), add_z.get_value()) {
                    (Some(x), Some(y), Some(z)) => {
                        let mut new_value = x;
                        new_value.mul_assign(&y);
                        new_value.add_assign(&z);

                        Some(new_value)
                    },
                    _ => {None}
                };

                let allocated_num = AllocatedNum::alloc(
                    cs, 
                    || {
                        Ok(*new_value.get()?)
                    }
                )?;

                let mut term = MainGateTerm::<E>::new();
                let mul_term = ArithmeticTerm::<E>::from_variable_and_coeff(x_var, mul_coeff).mul_by_variable(y_var);
                let x_term = ArithmeticTerm::<E>::from_variable_and_coeff(x_var, x_coeff);
                let y_term = ArithmeticTerm::<E>::from_variable_and_coeff(y_var, y_coeff);
                let z_term = ArithmeticTerm::<E>::from_variable_and_coeff(z_var, add_z.coeff);
                let n_term = ArithmeticTerm::<E>::from_variable(allocated_num.get_variable());
                let const_term = ArithmeticTerm::constant(constant_coeff);

                term.add_assign(mul_term);
                term.add_assign(x_term);
                term.add_assign(y_term);
                term.add_assign(z_term);
                term.add_assign(const_term);
                term.sub_assign(n_term);

                cs.allocate_main_gate(term)?;

                let new = Self::from_allocated_num(allocated_num);

                return Ok(new);
            }
        }
    }

    pub(crate) fn square_with_factor_and_add<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        x: &Self,
        z: &Self,
        factor: &E::Fr
    ) -> Result<Self, SynthesisError> {
        let x_is_constant = x.is_constant();
        let z_is_constant = z.is_constant();

        match (x_is_constant, z_is_constant) {
            (true, true) => {
                let mut result = x.get_constant_value();
                result.square();
                result.mul_assign(&factor);
                result.add_assign(&z.get_constant_value());

                let n = Self::from_constant(result);

                return Ok(n);
            },
            (true, false) => {
                let mut value = x.get_constant_value();
                value.square();
                value.mul_assign(&factor);

                let mut result = z.clone();
                result.add_constant(&value);

                return Ok(result);
            },
            (false, true) => {
                let mut mul_coeff = x.coeff;
                mul_coeff.square();
                mul_coeff.mul_assign(&factor);

                let mut x_coeff = x.coeff;
                x_coeff.mul_assign(&x.constant_term);
                x_coeff.double();
                x_coeff.mul_assign(&factor);

                let mut constant_coeff = x.constant_term;
                constant_coeff.square();
                constant_coeff.mul_assign(&factor);
                constant_coeff.add_assign(&z.get_constant_value());

                let x_var = x.get_variable().get_variable();

                let new_value = match (x.get_value(), z.get_value()) {
                    (Some(x), Some(z)) => {
                        let mut new_value = x;
                        new_value.square();
                        new_value.mul_assign(&factor);
                        new_value.add_assign(&z);

                        Some(new_value)
                    },
                    _ => {None}
                };

                let allocated_num = AllocatedNum::alloc(
                    cs, 
                    || {
                        Ok(*new_value.get()?)
                    }
                )?;

                let mut term = MainGateTerm::<E>::new();
                let mul_term = ArithmeticTerm::<E>::from_variable_and_coeff(x_var, mul_coeff).mul_by_variable(x_var);
                let x_term = ArithmeticTerm::<E>::from_variable_and_coeff(x_var, x_coeff);
                let n_term = ArithmeticTerm::<E>::from_variable(allocated_num.get_variable());
                let const_term = ArithmeticTerm::constant(constant_coeff);

                term.add_assign(mul_term);
                term.add_assign(x_term);
                term.add_assign(const_term);
                term.sub_assign(n_term);

                cs.allocate_main_gate(term)?;

                let new = Self::from_allocated_num(allocated_num);

                return Ok(new);
            },
            (false, false) => {
                let mut mul_coeff = x.coeff;
                mul_coeff.square();
                mul_coeff.mul_assign(&factor);

                let mut x_coeff = x.coeff;
                x_coeff.mul_assign(&x.constant_term);
                x_coeff.double();
                x_coeff.mul_assign(&factor);

                let mut constant_coeff = x.constant_term;
                constant_coeff.square();
                constant_coeff.mul_assign(&factor);
                constant_coeff.add_assign(&z.constant_term);

                let x_var = x.get_variable().get_variable();
                let z_var = z.get_variable().get_variable();

                let new_value = match (x.get_value(), z.get_value()) {
                    (Some(x), Some(z)) => {
                        let mut new_value = x;
                        new_value.square();
                        new_value.mul_assign(&factor);
                        new_value.add_assign(&z);

                        Some(new_value)
                    },
                    _ => {None}
                };

                let allocated_num = AllocatedNum::alloc(
                    cs, 
                    || {
                        Ok(*new_value.get()?)
                    }
                )?;

                let mut term = MainGateTerm::<E>::new();
                let mul_term = ArithmeticTerm::<E>::from_variable_and_coeff(x_var, mul_coeff).mul_by_variable(x_var);
                let x_term = ArithmeticTerm::<E>::from_variable_and_coeff(x_var, x_coeff);
                let z_term = ArithmeticTerm::<E>::from_variable_and_coeff(z_var, z.coeff);
                let n_term = ArithmeticTerm::<E>::from_variable(allocated_num.get_variable());
                let const_term = ArithmeticTerm::constant(constant_coeff);

                term.add_assign(mul_term);
                term.add_assign(x_term);
                term.add_assign(z_term);
                term.add_assign(const_term);
                term.sub_assign(n_term);

                cs.allocate_main_gate(term)?;

                let new = Self::from_allocated_num(allocated_num);

                return Ok(new);
            },
        }
    }

    // returns first if true and second if false
    pub fn select<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        flag: &Boolean,
        first: &Self,
        second: &Self
    ) -> Result<Self, SynthesisError> {
        match flag {
            Boolean::Constant(c) => {
                if *c {
                    return Ok(first.clone());
                } else {
                    return Ok(second.clone());
                }
            },
            _ => {}
        }

        let flag_as_term = Term::<E>::from_boolean(flag);

        // flag * a + (1-flag)*b = flag * (a-b) + b

        let mut minus_b = second.clone();
        minus_b.negate();
        let a_minus_b = first.add(cs, &minus_b)?;

        let new = Term::<E>::fma(cs, &flag_as_term, &a_minus_b, &second)?;

        Ok(new)
    }

    pub fn inverse<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<Self, SynthesisError> {
        if self.is_constant() {
            let new_value = self.into_constant_value().inverse().expect("inverse must exist");
            
            let new = Self::from_constant(new_value);

            return Ok(new)
        }

        let new_value = self.get_value().map(|el| el.inverse().expect("inverse must exist"));
        let new = Self::allocate(cs, new_value)?;

        // (a*X + b) * Y - 1 = 0
        // a * X * Y + b * Y - 1 = 0
        let mut term = MainGateTerm::<E>::new();
        let mul_term = ArithmeticTerm::<E>::from_variable_and_coeff(self.num.get_variable().get_variable(), self.coeff).mul_by_variable(new.num.get_variable().get_variable());
        let y_term = ArithmeticTerm::<E>::from_variable_and_coeff(new.num.get_variable().get_variable(), self.constant_term);
        let const_term = ArithmeticTerm::constant(E::Fr::one());

        term.add_assign(mul_term);
        term.add_assign(y_term);
        term.sub_assign(const_term);

        cs.allocate_main_gate(term)?;
        
        Ok(new)
    }

    pub fn div<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        other: &Self
    ) -> Result<Self, SynthesisError> {
        match (self.is_constant(), other.is_constant()) {
            (true, true) => {
                let mut new_value = other.into_constant_value().inverse().expect("inverse must exist");
                new_value.mul_assign(&self.into_constant_value());
                let new = Self::from_constant(new_value);
    
                return Ok(new)
            },
            (false, false) => {
                let new_value = match (self.get_value(), other.get_value()) {
                    (Some(this), Some(other)) => {
                        let mut new_value = other.inverse().expect("inverse must exist");
                        new_value.mul_assign(&this);

                        Some(new_value)
                    }
                    _ => None
                };

                // (a * X + b) / (c * Y + d) = Z
                // a * X + b - c * Y * Z - d * Z = 0
                let z = Self::allocate(cs, new_value)?;

                let mut term = MainGateTerm::<E>::new();
                let x_term = ArithmeticTerm::<E>::from_variable_and_coeff(self.num.get_variable().get_variable(), self.coeff);
                let yz_term = ArithmeticTerm::<E>::from_variable_and_coeff(other.num.get_variable().get_variable(), other.coeff).mul_by_variable(z.num.get_variable().get_variable());
                let z_term = ArithmeticTerm::<E>::from_variable_and_coeff(z.num.get_variable().get_variable(), other.constant_term);
                let b_term = ArithmeticTerm::constant(self.constant_term);
        
                term.add_assign(x_term);
                term.add_assign(b_term);
                term.sub_assign(yz_term);
                term.sub_assign(z_term);
        
                cs.allocate_main_gate(term)?;

                return Ok(z)
            },
            _ => {
                unimplemented!()
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::bellman::plonk::better_better_cs::cs::{
        Variable, 
        ConstraintSystem,
        ArithmeticTerm,
        MainGateTerm,
        Width4MainGateWithDNext,
        MainGate,
        GateInternal,
        Gate,
        LinearCombinationOfTerms,
        PolynomialMultiplicativeTerm,
        PolynomialInConstraint,
        TimeDilation,
        Coefficient,
        PlonkConstraintSystemParams,
        TrivialAssembly, 
        PlonkCsWidth4WithNextStepParams,
    };

    use crate::bellman::pairing::bn256::{Fq, Bn256, Fr};

    #[test]
    fn test_add_on_random_witness(){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for _ in 0..100 {
            let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

            let v0 = rng.gen();
            let v1 = rng.gen();

            let a0 = rng.gen();
            let a1 = rng.gen();

            let c0 = rng.gen();
            let c1 = rng.gen();

            let a = AllocatedNum::alloc(
                &mut cs,
                || {
                    Ok(a0)
                }
            ).unwrap();

            let b = AllocatedNum::alloc(
                &mut cs,
                || {
                    Ok(a1)
                }
            ).unwrap();

            let mut a_term = Term::<Bn256>::from_allocated_num(a);
            a_term.scale(&v0);
            a_term.add_constant(&c0);

            let mut b_term = Term::<Bn256>::from_allocated_num(b);
            b_term.scale(&v1);
            b_term.add_constant(&c1);

            let a_b_term = a_term.add(&mut cs, &b_term).unwrap();

            let mut val0 = a0;
            val0.mul_assign(&v0);
            val0.add_assign(&c0);

            let mut val1 = a1;
            val1.mul_assign(&v1);
            val1.add_assign(&c1);

            let mut res = val0;
            res.add_assign(&val1);

            assert!(cs.is_satisfied());
            assert!(a_b_term.get_value().unwrap() == res);
        }

    }

    #[test]
    fn test_square_on_random_witness(){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for _ in 0..100 {
            let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

            let v0 = rng.gen();
            let v1 = rng.gen();

            let a0 = rng.gen();
            let a1 = rng.gen();

            let c0 = rng.gen();
            let c1 = rng.gen();

            let a = AllocatedNum::alloc(
                &mut cs,
                || {
                    Ok(a0)
                }
            ).unwrap();

            let b = AllocatedNum::alloc(
                &mut cs,
                || {
                    Ok(a1)
                }
            ).unwrap();

            let mut a_term = Term::<Bn256>::from_allocated_num(a);
            a_term.scale(&v0);
            a_term.add_constant(&c0);

            let mut b_term = Term::<Bn256>::from_allocated_num(b);
            b_term.scale(&v1);
            b_term.add_constant(&c1);

            let factor: Fr = rng.gen();

            let a_b_term = Term::<Bn256>::square_with_factor_and_add(&mut cs, &a_term, &b_term, &factor).unwrap();

            let mut val0 = a0;
            val0.mul_assign(&v0);
            val0.add_assign(&c0);

            let mut val1 = a1;
            val1.mul_assign(&v1);
            val1.add_assign(&c1);

            let mut res = val0;
            res.square();
            res.mul_assign(&factor);
            res.add_assign(&val1);

            assert!(cs.is_satisfied());
            assert!(a_b_term.get_value().unwrap() == res);
        }

    }


    #[test]
    fn test_fma_on_random_witness(){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for _ in 0..100 {
            let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

            let v0 = rng.gen();
            let v1 = rng.gen();
            let v2 = rng.gen();

            let a0 = rng.gen();
            let a1 = rng.gen();
            let a2 = rng.gen();

            let c0 = rng.gen();
            let c1 = rng.gen();
            let c2 = rng.gen();

            let a = AllocatedNum::alloc(
                &mut cs,
                || {
                    Ok(a0)
                }
            ).unwrap();

            let b = AllocatedNum::alloc(
                &mut cs,
                || {
                    Ok(a1)
                }
            ).unwrap();

            let c = AllocatedNum::alloc(
                &mut cs,
                || {
                    Ok(a2)
                }
            ).unwrap();

            let mut a_term = Term::<Bn256>::from_allocated_num(a);
            a_term.scale(&v0);
            a_term.add_constant(&c0);

            let mut b_term = Term::<Bn256>::from_allocated_num(b);
            b_term.scale(&v1);
            b_term.add_constant(&c1);

            let mut c_term = Term::<Bn256>::from_allocated_num(c);
            c_term.scale(&v2);
            c_term.add_constant(&c2);

            let a_b_term = Term::<Bn256>::fma(&mut cs, &a_term, &b_term, &c_term).unwrap();

            let mut val0 = a0;
            val0.mul_assign(&v0);
            val0.add_assign(&c0);

            let mut val1 = a1;
            val1.mul_assign(&v1);
            val1.add_assign(&c1);

            let mut val2 = a2;
            val2.mul_assign(&v2);
            val2.add_assign(&c2);

            let mut res = val0;
            res.mul_assign(&val1);
            res.add_assign(&val2);

            assert!(cs.is_satisfied());
            assert!(a_b_term.get_value().unwrap() == res);
        }

    }
}