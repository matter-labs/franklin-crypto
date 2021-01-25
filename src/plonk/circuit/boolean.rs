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
    Width4MainGateWithDNext,
    MainGate,
    GateInternal,
    Gate,
    LinearCombinationOfTerms,
    PolynomialMultiplicativeTerm,
    PolynomialInConstraint,
    TimeDilation,
    Coefficient,
};


use crate::circuit::{
    Assignment
};

use super::allocated_num::{
    AllocatedNum
};

use super::linear_combination::{
    LinearCombination
};

pub fn field_into_allocated_bits_le_fixed<E: Engine, CS: ConstraintSystem<E>, F: PrimeField>(
    cs: &mut CS,
    value: Option<F>,
    bit_length: Option<usize>,
) -> Result<Vec<AllocatedBit>, SynthesisError> {
    let limit = if let Some(bit_length) = bit_length {
        assert!(bit_length <= F::NUM_BITS as usize);

        bit_length
    } else {
        F::NUM_BITS as usize
    };
    
    // Deconstruct in big-endian bit order
    let values = match value {
        Some(ref value) => {
            let mut field_char = BitIterator::new(F::char());

            let mut tmp = Vec::with_capacity(F::NUM_BITS as usize);

            let mut found_one = false;
            for b in BitIterator::new(value.into_repr()) {
                // Skip leading bits
                found_one |= field_char.next().unwrap();
                if !found_one {
                    continue;
                }

                tmp.push(Some(b));
            }

            assert_eq!(tmp.len(), F::NUM_BITS as usize);

            tmp
        }
        None => vec![None; F::NUM_BITS as usize],
    };

    // Allocate in little-endian order
    let bits = values
        .into_iter()
        .rev()
        .take(limit)
        .map(|b| AllocatedBit::alloc(cs, b))
        .collect::<Result<Vec<_>, SynthesisError>>()?;

    Ok(bits)
}

pub fn field_into_allocated_booleans_le_fixed<E: Engine, CS: ConstraintSystem<E>, F: PrimeField>(
    cs: &mut CS,
    value: Option<F>,
    bit_length: Option<usize>,
) -> Result<Vec<Boolean>, SynthesisError> {
    let bits = field_into_allocated_bits_le_fixed(cs, value, bit_length)?;
    let bools: Vec<_> = bits.into_iter().map(|el| Boolean::from(el)).collect();

    Ok(bools)
}

/// Represents a variable in the constraint system which is guaranteed
/// to be either zero or one.
#[derive(Clone, Debug)]
pub struct AllocatedBit {
    variable: Variable,
    value: Option<bool>
}

impl Copy for AllocatedBit {}

impl AllocatedBit {
    pub fn get_value(&self) -> Option<bool> {
        self.value
    }

    pub fn get_value_as_field_element<E:Engine>(&self) -> Option<E::Fr> {
       let value = self.get_value();
       match value{
           None => None,
           Some(value) =>{
               if value{
                   Some(E::Fr::one())
               }else{
                    Some(E::Fr::zero()) 
               }
           }
       }
    }
    
    pub fn get_variable(&self) -> Variable {
        self.variable
    }

    /// Allocate a variable in the constraint system which can only be a
    /// boolean value. Further, constrain that the boolean is false
    /// unless the condition is false.
    pub fn alloc_conditionally<E, CS>(
        cs: &mut CS,
        value: Option<bool>,
        must_be_false: &AllocatedBit
    ) -> Result<Self, SynthesisError>
        where E: Engine,
              CS: ConstraintSystem<E>
    {
        // In gated form it would be two separate logical gates
        // - a is boolean
        // - b = a AND (NOT must_be_false)
        // return b

        let a = Self::alloc(cs, value)?;

        // b = a * (1 - must_be_false)
        // a*must_be_false - a + b = 0

        let b = cs.alloc(|| {
            match (a.get_value().get(), must_be_false.get_value().get()) {
                (Ok(a_value), Ok(must_be_false_value)) => {
                    let value = *a_value & (! *must_be_false_value);

                    if value {
                        Ok(E::Fr::one())
                    } else {
                        Ok(E::Fr::zero())
                    }
                },
                _ => return Err(SynthesisError::AssignmentMissing)
            }
        })?;

        let mut gate_term = MainGateTerm::new();

        let mut multiplicative_term = ArithmeticTerm::from_variable(a.get_variable());
        multiplicative_term = multiplicative_term.mul_by_variable(must_be_false.get_variable());
        gate_term.add_assign(multiplicative_term);
        gate_term.sub_assign(ArithmeticTerm::from_variable(a.get_variable()));
        gate_term.add_assign(ArithmeticTerm::from_variable(b));

        cs.allocate_main_gate(gate_term)?;

        Ok(AllocatedBit {
            variable: b,
            value: value
        })
    }

    /// Allocate a variable in the constraint system which can only be a
    /// boolean value.
    pub fn alloc<E, CS>(
        cs: &mut CS,
        value: Option<bool>,
    ) -> Result<Self, SynthesisError>
        where E: Engine,
              CS: ConstraintSystem<E>
    {
        let var = cs.alloc(|| {
            if *value.get()? {
                Ok(E::Fr::one())
            } else {
                Ok(E::Fr::zero())
            }
        })?;

        // Constrain: (1 - a) * a = 0
        // This constrains a to be either 0 or 1.

        let mut gate_term = MainGateTerm::new();

        let mut multiplicative_term = ArithmeticTerm::from_variable(var);
        multiplicative_term = multiplicative_term.mul_by_variable(var);
        gate_term.add_assign(multiplicative_term);
        gate_term.sub_assign(ArithmeticTerm::from_variable(var));

        cs.allocate_main_gate(gate_term)?;
        
        Ok(AllocatedBit {
            variable: var,
            value: value
        })
    }

    /// Performs an XOR operation over the two operands, returning
    /// an `AllocatedBit`.
    pub fn xor<E, CS>(
        cs: &mut CS,
        a: &Self,
        b: &Self
    ) -> Result<Self, SynthesisError>
        where E: Engine,
              CS: ConstraintSystem<E>
    {
        let mut result_value = None;

        let result_var = cs.alloc(|| {
            if *a.value.get()? ^ *b.value.get()? {
                result_value = Some(true);

                Ok(E::Fr::one())
            } else {
                result_value = Some(false);

                Ok(E::Fr::zero())
            }
        })?;

        // Constrain (a + a) * (b) = (a + b - c)
        // Given that a and b are boolean constrained, if they
        // are equal, the only solution for c is 0, and if they
        // are different, the only solution for c is 1.
        //
        // ¬(a ∧ b) ∧ ¬(¬a ∧ ¬b) = c
        // (1 - (a * b)) * (1 - ((1 - a) * (1 - b))) = c
        // (1 - ab) * (1 - (1 - a - b + ab)) = c
        // (1 - ab) * (a + b - ab) = c
        // a + b - ab - (a^2)b - (b^2)a + (a^2)(b^2) = c
        // a + b - ab - ab - ab + ab = c
        // a + b - 2ab = c
        // -2a * b = c - a - b
        // 2a * b = a + b - c
        // (a + a) * b = a + b - c

        // 2a*b - a - b + c = 0

        let mut gate_term = MainGateTerm::new();

        let mut two = E::Fr::one();
        two.double();

        let mut multiplicative_term = ArithmeticTerm::from_variable(a.get_variable());
        multiplicative_term = multiplicative_term.mul_by_variable(b.get_variable());
        multiplicative_term.scale(&two);
        gate_term.add_assign(multiplicative_term);
        gate_term.sub_assign(ArithmeticTerm::from_variable(a.get_variable()));
        gate_term.sub_assign(ArithmeticTerm::from_variable(b.get_variable()));
        gate_term.add_assign(ArithmeticTerm::from_variable(result_var));

        cs.allocate_main_gate(gate_term)?;

        Ok(AllocatedBit {
            variable: result_var,
            value: result_value
        })
    }

    /// Performs an AND operation over the two operands, returning
    /// an `AllocatedBit`.
    pub fn and<E, CS>(
        cs: &mut CS,
        a: &Self,
        b: &Self
    ) -> Result<Self, SynthesisError>
        where E: Engine,
              CS: ConstraintSystem<E>
    {
        let mut result_value = None;

        let result_var = cs.alloc(|| {
            if *a.value.get()? & *b.value.get()? {
                result_value = Some(true);

                Ok(E::Fr::one())
            } else {
                result_value = Some(false);

                Ok(E::Fr::zero())
            }
        })?;

        // Constrain (a) * (b) = (c), ensuring c is 1 iff
        // a AND b are both 1.

        // a*b - c = 0

        let mut gate_term = MainGateTerm::new();

        let mut multiplicative_term = ArithmeticTerm::from_variable(a.get_variable());
        multiplicative_term = multiplicative_term.mul_by_variable(b.get_variable());
        gate_term.add_assign(multiplicative_term);
        gate_term.sub_assign(ArithmeticTerm::from_variable(result_var));

        cs.allocate_main_gate(gate_term)?;

        Ok(AllocatedBit {
            variable: result_var,
            value: result_value
        })
    }

    /// Performs an OR operation over the two operands, returning
    /// an `AllocatedBit`.
    pub fn or<E, CS>(
        cs: &mut CS,
        a: &Self,
        b: &Self
    ) -> Result<Self, SynthesisError>
        where E: Engine,
              CS: ConstraintSystem<E>
    {
        let mut result_value = None;

        let result_var = cs.alloc(|| {
            if *a.value.get()? || *b.value.get()? {
                result_value = Some(true);

                Ok(E::Fr::one())
            } else {
                result_value = Some(false);

                Ok(E::Fr::zero())
            }
        })?;

        // Constrain (1-a) * (1-b) = (1-c), ensuring c is 1 iff
        // any of a, b are both 1.

        // (1-a)(1-b) = (1-c) => ab-a-b+1 = 1-c
        // ab-a-b+c=0 

        let mut gate_term = MainGateTerm::new();

        let mut multiplicative_term = ArithmeticTerm::from_variable(a.get_variable());
        multiplicative_term = multiplicative_term.mul_by_variable(b.get_variable());
        gate_term.add_assign(multiplicative_term);
        gate_term.sub_assign(ArithmeticTerm::from_variable(a.get_variable()));
        gate_term.sub_assign(ArithmeticTerm::from_variable(b.get_variable()));
        gate_term.add_assign(ArithmeticTerm::from_variable(result_var));

        cs.allocate_main_gate(gate_term)?;

        Ok(AllocatedBit {
            variable: result_var,
            value: result_value
        })
    }

    /// Calculates `a AND (NOT b)`.
    pub fn and_not<E, CS>(
        cs: &mut CS,
        a: &Self,
        b: &Self
    ) -> Result<Self, SynthesisError>
        where E: Engine,
              CS: ConstraintSystem<E>
    {
        let mut result_value = None;

        let result_var = cs.alloc(|| {
            if *a.value.get()? & !*b.value.get()? {
                result_value = Some(true);

                Ok(E::Fr::one())
            } else {
                result_value = Some(false);

                Ok(E::Fr::zero())
            }
        })?;

        // Constrain (a) * (1 - b) = (c), ensuring c is 1 iff
        // a is true and b is false, and otherwise c is 0.

        // a*b - a + c = 0


        let mut gate_term = MainGateTerm::new();

        let mut multiplicative_term = ArithmeticTerm::from_variable(a.get_variable());
        multiplicative_term = multiplicative_term.mul_by_variable(b.get_variable());
        gate_term.add_assign(multiplicative_term);
        gate_term.sub_assign(ArithmeticTerm::from_variable(a.get_variable()));
        gate_term.add_assign(ArithmeticTerm::from_variable(result_var));

        cs.allocate_main_gate(gate_term)?;

        Ok(AllocatedBit {
            variable: result_var,
            value: result_value
        })
    }

    /// Calculates `(NOT a) AND (NOT b)`.
    pub fn nor<E, CS>(
        cs: &mut CS,
        a: &Self,
        b: &Self
    ) -> Result<Self, SynthesisError>
        where E: Engine,
              CS: ConstraintSystem<E>
    {
        let mut result_value = None;

        let result_var = cs.alloc(|| {
            if !*a.value.get()? & !*b.value.get()? {
                result_value = Some(true);

                Ok(E::Fr::one())
            } else {
                result_value = Some(false);

                Ok(E::Fr::zero())
            }
        })?;

        // Constrain (1 - a) * (1 - b) = (c), ensuring c is 1 iff
        // a and b are both false, and otherwise c is 0.

        // a*b - a - b - c + 1 = 0

        let mut gate_term = MainGateTerm::new();

        let mut multiplicative_term = ArithmeticTerm::from_variable(a.get_variable());
        multiplicative_term = multiplicative_term.mul_by_variable(b.get_variable());
        gate_term.add_assign(multiplicative_term);
        gate_term.sub_assign(ArithmeticTerm::from_variable(a.get_variable()));
        gate_term.sub_assign(ArithmeticTerm::from_variable(b.get_variable()));
        gate_term.sub_assign(ArithmeticTerm::from_variable(result_var));
        gate_term.add_assign(ArithmeticTerm::constant(E::Fr::one()));

        cs.allocate_main_gate(gate_term)?;

        Ok(AllocatedBit {
            variable: result_var,
            value: result_value
        })
    }
}

pub fn u64_into_boolean_vec_le<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    value: Option<u64>
) -> Result<Vec<Boolean>, SynthesisError>
{
    let values = match value {
        Some(ref value) => {
            let mut tmp = Vec::with_capacity(64);

            for i in 0..64 {
                tmp.push(Some(*value >> i & 1 == 1));
            }

            tmp
        },
        None => {
            vec![None; 64]
        }
    };

    let bits = values.into_iter().enumerate().map(|(_i, b)| {
        Ok(Boolean::from(AllocatedBit::alloc(
            cs,
            b
        )?))
    }).collect::<Result<Vec<_>, SynthesisError>>()?;

    Ok(bits)
}

// changes an order of the bits to transform bits in LSB first order into
// LE bytes. Takes 8 bit chunks and reverses them
pub fn le_bits_into_le_bytes(bits: Vec<Boolean>) -> Vec<Boolean> {
    assert_eq!(bits.len() % 8, 0);

    let mut result = vec![];
    for chunk in bits.chunks(8) {
        for b in chunk.iter().rev() {
            result.push(b.clone());
        }
    }

    result
}

pub fn field_into_boolean_vec_le<E: Engine, CS: ConstraintSystem<E>, F: PrimeField>(
    cs: &mut CS,
    value: Option<F>
) -> Result<Vec<Boolean>, SynthesisError>
{
    let v = field_into_allocated_bits_le::<E, CS, F>(cs, value)?;

    Ok(v.into_iter().map(|e| Boolean::from(e)).collect())
}

pub fn field_into_allocated_bits_le<E: Engine, CS: ConstraintSystem<E>, F: PrimeField>(
    cs: &mut CS,
    value: Option<F>
) -> Result<Vec<AllocatedBit>, SynthesisError>
{
    field_into_allocated_bits_le_fixed(cs, value, None)
}

/// This is a boolean value which may be either a constant or
/// an interpretation of an `AllocatedBit`.
#[derive(Clone, Copy, Debug)]
pub enum Boolean {
    /// Existential view of the boolean variable
    Is(AllocatedBit),
    /// Negated view of the boolean variable
    Not(AllocatedBit),
    /// Constant (not an allocated variable)
    Constant(bool)
}

impl Boolean {
    pub fn is_constant(&self) -> bool {
        match *self {
            Boolean::Constant(_) => true,
            _ => false
        }
    }

    pub fn get_variable(&self) -> Option<&AllocatedBit> {
        match *self {
            Boolean::Is(ref v) => Some(v),
            Boolean::Not(ref v) => Some(v),
            Boolean::Constant(_) => None
        }
    }

    #[track_caller]
    pub fn enforce_equal<E, CS>(
        cs: &mut CS,
        a: &Self,
        b: &Self
    ) -> Result<(), SynthesisError>
        where E: Engine,
              CS: ConstraintSystem<E>
    {
        match (a.get_value(), b.get_value()) {
            (Some(a), Some(b)) => {
                assert_eq!(a, b, "unequal: a = {}, b = {}", a, b);
            },
            _ => {}
        };
        match (a, b) {
            (&Boolean::Constant(a), &Boolean::Constant(b)) => {
                if a == b {
                    Ok(())
                } else {
                    Err(SynthesisError::Unsatisfiable)
                }
            },
            (&Boolean::Constant(true), a) | (a, &Boolean::Constant(true)) => {
                let mut lc = a.lc(E::Fr::one());
                let mut minus_one = E::Fr::one();
                minus_one.negate();
                lc.add_assign_constant(minus_one);

                lc.enforce_zero(cs)
            },
            (&Boolean::Constant(false), a) | (a, &Boolean::Constant(false)) => {
                let lc = a.lc(E::Fr::one());

                lc.enforce_zero(cs)
            },
            (a, b) => {
                let mut lc = a.lc(E::Fr::one());
                let mut minus_one = E::Fr::one();
                minus_one.negate();
                lc.add_assign(&b.lc(minus_one));

                lc.enforce_zero(cs)
            }
        }
    }

    pub fn get_value(&self) -> Option<bool> {
        match self {
            &Boolean::Constant(c) => Some(c),
            &Boolean::Is(ref v) => v.get_value(),
            &Boolean::Not(ref v) => v.get_value().map(|b| !b)
        }
    }

    pub fn get_value_in_field<E: Engine>(&self) -> Option<E::Fr> {
       let value = self.get_value();
       match value{
           None => None,
           Some(value) =>{
               if value{
                   Some(E::Fr::one())
               }else{
                    Some(E::Fr::zero()) 
               }
           }
       }
    }

    pub fn lc<E: Engine>(
        &self,
        coeff: E::Fr
    ) -> LinearCombination<E>
    {
        match self {
            &Boolean::Constant(c) => {
                if c {
                    let mut lc = LinearCombination::<E>::zero();
                    lc.add_assign_constant(coeff);

                    lc
                } else {
                    LinearCombination::<E>::zero()
                }
            },
            &Boolean::Is(ref v) => {
                let mut lc = LinearCombination::<E>::zero();
                lc.add_assign_bit_with_coeff(v, coeff);

                lc
            },
            &Boolean::Not(ref v) => {
                let mut lc = LinearCombination::<E>::zero();
                let mut coeff_negated = coeff;
                coeff_negated.negate();
                lc.add_assign_constant(coeff);
                lc.add_assign_bit_with_coeff(v, coeff_negated);

                lc
            }
        }
    }

    /// Construct a boolean from a known constant
    pub fn constant(b: bool) -> Self {
        Boolean::Constant(b)
    }

    /// Return a negated interpretation of this boolean.
    pub fn not(&self) -> Self {
        match self {
            &Boolean::Constant(c) => Boolean::Constant(!c),
            &Boolean::Is(ref v) => Boolean::Not(v.clone()),
            &Boolean::Not(ref v) => Boolean::Is(v.clone())
        }
    }

    /// Perform XOR over two boolean operands
    pub fn xor<'a, E, CS>(
        cs: &mut CS,
        a: &'a Self,
        b: &'a Self
    ) -> Result<Self, SynthesisError>
        where E: Engine,
              CS: ConstraintSystem<E>
    {
        match (a, b) {
            (&Boolean::Constant(false), x) | (x, &Boolean::Constant(false)) => Ok(x.clone()),
            (&Boolean::Constant(true), x) | (x, &Boolean::Constant(true)) => Ok(x.not()),
            // a XOR (NOT b) = NOT(a XOR b)
            (is @ &Boolean::Is(_), not @ &Boolean::Not(_)) | (not @ &Boolean::Not(_), is @ &Boolean::Is(_)) => {
                Ok(Boolean::xor(
                    cs,
                    is,
                    &not.not()
                )?.not())
            },
            // a XOR b = (NOT a) XOR (NOT b)
            (&Boolean::Is(ref a), &Boolean::Is(ref b)) | (&Boolean::Not(ref a), &Boolean::Not(ref b)) => {
                // no matter what is in the variables, we just collapse it to constant `false`
                if a.get_variable() == b.get_variable() {
                    return Ok(Boolean::constant(false));
                }
                Ok(Boolean::Is(AllocatedBit::xor(cs, a, b)?))
            }
        }
    }

    /// Perform AND over two boolean operands
    pub fn and<'a, E, CS>(
        cs: &mut CS,
        a: &'a Self,
        b: &'a Self
    ) -> Result<Self, SynthesisError>
        where E: Engine,
              CS: ConstraintSystem<E>
    {
        match (a, b) {
            // false AND x is always false
            (&Boolean::Constant(false), _) | (_, &Boolean::Constant(false)) => Ok(Boolean::Constant(false)),
            // true AND x is always x
            (&Boolean::Constant(true), x) | (x, &Boolean::Constant(true)) => Ok(x.clone()),
            // a AND (NOT b)
            (&Boolean::Is(ref is), &Boolean::Not(ref not)) | (&Boolean::Not(ref not), &Boolean::Is(ref is)) => {
                Ok(Boolean::Is(AllocatedBit::and_not(cs, is, not)?))
            },
            // (NOT a) AND (NOT b) = a NOR b
            (&Boolean::Not(ref a), &Boolean::Not(ref b)) => {
                Ok(Boolean::Is(AllocatedBit::nor(cs, a, b)?))
            },
            // a AND b
            (&Boolean::Is(ref a), &Boolean::Is(ref b)) => {
                Ok(Boolean::Is(AllocatedBit::and(cs, a, b)?))
            }
        }
    }

    /// Perform OR over two boolean operands
    pub fn or<'a, E, CS>(
        cs: &mut CS,
        a: &'a Self,
        b: &'a Self
    ) -> Result<Self, SynthesisError>
        where E: Engine,
              CS: ConstraintSystem<E>
    {
        match (a, b) {
            // true OR  x is always true
            (&Boolean::Constant(true), _) | (_, &Boolean::Constant(true)) => Ok(Boolean::Constant(true)),
            // false OR x is always x
            (&Boolean::Constant(false), x) | (x, &Boolean::Constant(false)) => Ok(x.clone()),
            // a OR (NOT b)
            (&Boolean::Is(ref is), &Boolean::Not(ref not)) | (&Boolean::Not(ref not), &Boolean::Is(ref is)) => {
                Ok(Boolean::Not(AllocatedBit::and_not(cs, not, is)?))
            },
            // (NOT a) OR (NOT b) = a NOR b
            (&Boolean::Not(ref a), &Boolean::Not(ref b)) => {
                Ok(Boolean::Not(AllocatedBit::and(cs, a, b)?))
            },
            // a OR b
            (&Boolean::Is(ref a), &Boolean::Is(ref b)) => {
                Ok(Boolean::Is(AllocatedBit::or(cs, a, b)?))
            }
        }
    }

    pub fn conditionally_select<E: Engine, CS: ConstraintSystem<E>>(
        cs: &mut CS,
        flag: &Self,
        a: &Self,
        b: &Self
    ) -> Result<Self, SynthesisError> {
        Self::sha256_ch(cs, &flag, a, b)
    }

    /// Computes (a and b) xor ((not a) and c)
    pub fn sha256_ch<'a, E, CS>(
        cs: &mut CS,
        a: &'a Self,
        b: &'a Self,
        c: &'a Self
    ) -> Result<Self, SynthesisError>
        where E: Engine,
              CS: ConstraintSystem<E>
    {
        let ch_value = match (a.get_value(), b.get_value(), c.get_value()) {
            (Some(a), Some(b), Some(c)) => {
                // (a and b) xor ((not a) and c)
                Some((a & b) ^ ((!a) & c))
            },
            _ => None
        };

        match (a, b, c) {
            (&Boolean::Constant(_),
            &Boolean::Constant(_),
            &Boolean::Constant(_)) => {
                // They're all constants, so we can just compute the value.

                return Ok(Boolean::Constant(ch_value.expect("they're all constants")));
            },
            (&Boolean::Constant(false), _, c) => {
                // If a is false
                // (a and b) xor ((not a) and c)
                // equals
                // (false) xor (c)
                // equals
                // c
                return Ok(c.clone());
            },
            (a, &Boolean::Constant(false), c) => {
                // If b is false
                // (a and b) xor ((not a) and c)
                // equals
                // ((not a) and c)
                return Boolean::and(
                    cs,
                    &a.not(),
                    &c
                );
            },
            (a, b, &Boolean::Constant(false)) => {
                // If c is false
                // (a and b) xor ((not a) and c)
                // equals
                // (a and b)
                return Boolean::and(
                    cs,
                    &a,
                    &b
                );
            },
            (a, b, &Boolean::Constant(true)) => {
                // If c is true
                // (a and b) xor ((not a) and c)
                // equals
                // (a and b) xor (not a)
                // equals
                // not (a and (not b))
                return Ok(Boolean::and(
                    cs,
                    &a,
                    &b.not()
                )?.not());
            },
            (a, &Boolean::Constant(true), c) => {
                // If b is true
                // (a and b) xor ((not a) and c)
                // equals
                // a xor ((not a) and c)
                // equals
                // not ((not a) and (not c))
                return Ok(Boolean::and(
                    cs,
                    &a.not(),
                    &c.not()
                )?.not());
            },
            (&Boolean::Constant(true), _, _) => {
                // If a is true
                // (a and b) xor ((not a) and c)
                // equals
                // b xor ((not a) and c)
                // So we just continue!
            },
            (&Boolean::Is(_), &Boolean::Is(_), &Boolean::Is(_)) |
            (&Boolean::Is(_), &Boolean::Is(_), &Boolean::Not(_)) |
            (&Boolean::Is(_), &Boolean::Not(_), &Boolean::Is(_)) |
            (&Boolean::Is(_), &Boolean::Not(_), &Boolean::Not(_)) |
            (&Boolean::Not(_), &Boolean::Is(_), &Boolean::Is(_)) |
            (&Boolean::Not(_), &Boolean::Is(_), &Boolean::Not(_)) |
            (&Boolean::Not(_), &Boolean::Not(_), &Boolean::Is(_)) |
            (&Boolean::Not(_), &Boolean::Not(_), &Boolean::Not(_))
            => {}
        }

        let ch = cs.alloc(|| {
            ch_value.get().map(|v| {
                if *v {
                    E::Fr::one()
                } else {
                    E::Fr::zero()
                }
            })
        })?;

        // a(b - c) = ch - c

        // tmp = b - c
        // a * tmp - ch + c = 0

        let one = E::Fr::one();
        let mut minus_one = one;
        minus_one.negate();
        let mut tmp_lc = LinearCombination::zero();
        tmp_lc.add_assign_boolean_with_coeff(&b, E::Fr::one());
        tmp_lc.add_assign_boolean_with_coeff(&c, minus_one);
        let tmp = tmp_lc.into_allocated_num(cs)?;

        // here we have to branch over `a` due wrapping
        match (a, c) {
            (Boolean::Is(ref a), Boolean::Is(ref c)) => {
                // a = a
                // c = c
                // a * tmp - ch + c = 0
                let mut gate_term = MainGateTerm::new();

                let mut multiplicative_term = ArithmeticTerm::from_variable(a.get_variable());
                multiplicative_term = multiplicative_term.mul_by_variable(tmp.get_variable());
                gate_term.add_assign(multiplicative_term);
                gate_term.sub_assign(ArithmeticTerm::from_variable(ch));
                gate_term.add_assign(ArithmeticTerm::from_variable(c.get_variable()));

                cs.allocate_main_gate(gate_term)?;
            },
            (Boolean::Is(ref a), Boolean::Not(ref c)) => {
                // a = a
                // c = 1 - c
                // a * tmp - ch + c = 0 -> 
                // a * tmp - ch - c + 1 = 0
                let mut gate_term = MainGateTerm::new();

                let mut multiplicative_term = ArithmeticTerm::from_variable(a.get_variable());
                multiplicative_term = multiplicative_term.mul_by_variable(tmp.get_variable());
                gate_term.add_assign(multiplicative_term);
                gate_term.sub_assign(ArithmeticTerm::from_variable(ch));
                gate_term.sub_assign(ArithmeticTerm::from_variable(c.get_variable()));
                gate_term.add_assign(ArithmeticTerm::constant(E::Fr::one()));

                cs.allocate_main_gate(gate_term)?;
            },
            (Boolean::Not(ref a), Boolean::Is(ref c)) => {
                // a = 1 - a
                // c = c
                // a * tmp - ch + c = 0 -> 
                // - a * tmp  + tmp - ch + c = 0
                let mut gate_term = MainGateTerm::new();

                let mut multiplicative_term = ArithmeticTerm::from_variable(a.get_variable());
                multiplicative_term = multiplicative_term.mul_by_variable(tmp.get_variable());
                gate_term.sub_assign(multiplicative_term);
                gate_term.add_assign(ArithmeticTerm::from_variable(tmp.get_variable()));
                gate_term.sub_assign(ArithmeticTerm::from_variable(ch));
                gate_term.add_assign(ArithmeticTerm::from_variable(c.get_variable()));

                cs.allocate_main_gate(gate_term)?;
            },
            (Boolean::Not(ref a), Boolean::Not(ref c)) => {
                // a = 1 - a
                // c = 1 - c
                // a * tmp - ch + c = 0 -> 
                // - a * tmp + tmp - ch - c + 1 = 0
                let mut gate_term = MainGateTerm::new();

                let mut multiplicative_term = ArithmeticTerm::from_variable(a.get_variable());
                multiplicative_term = multiplicative_term.mul_by_variable(tmp.get_variable());
                gate_term.sub_assign(multiplicative_term);
                gate_term.add_assign(ArithmeticTerm::from_variable(tmp.get_variable()));
                gate_term.sub_assign(ArithmeticTerm::from_variable(ch));
                gate_term.sub_assign(ArithmeticTerm::from_variable(c.get_variable()));
                gate_term.add_assign(ArithmeticTerm::constant(E::Fr::one()));

                cs.allocate_main_gate(gate_term)?;
            },
            (Boolean::Constant(true), Boolean::Is(ref c)) => {
                // a = 1
                // c = c
                // a * tmp - ch + c = 0 -> 
                // tmp - ch + c = 0
                let mut gate_term = MainGateTerm::new();

                gate_term.add_assign(ArithmeticTerm::from_variable(tmp.get_variable()));
                gate_term.sub_assign(ArithmeticTerm::from_variable(ch));
                gate_term.add_assign(ArithmeticTerm::from_variable(c.get_variable()));

                cs.allocate_main_gate(gate_term)?;
            },
            (Boolean::Constant(true), Boolean::Not(ref c)) => {
                // a = 1
                // c = 1 - c
                // a * tmp - ch + c = 0 -> 
                // tmp - ch - c + 1 = 0
                let mut gate_term = MainGateTerm::new();

                gate_term.add_assign(ArithmeticTerm::from_variable(tmp.get_variable()));
                gate_term.sub_assign(ArithmeticTerm::from_variable(ch));
                gate_term.sub_assign(ArithmeticTerm::from_variable(c.get_variable()));
                gate_term.add_assign(ArithmeticTerm::constant(E::Fr::one()));

                cs.allocate_main_gate(gate_term)?;
            },
            (Boolean::Constant(false), Boolean::Is(ref c)) => {
                // a = 0
                // c = c
                // a * tmp - ch + c = 0 -> 
                // - ch + c = 0
                let mut gate_term = MainGateTerm::new();

                gate_term.sub_assign(ArithmeticTerm::from_variable(ch));
                gate_term.add_assign(ArithmeticTerm::from_variable(c.get_variable()));

                cs.allocate_main_gate(gate_term)?;
            },
            (Boolean::Constant(false), Boolean::Not(ref c)) => {
                // a = 0
                // c = 1 - c
                // a * tmp - ch + c = 0 -> 
                // - ch - c + 1 = 0
                let mut gate_term = MainGateTerm::new();

                gate_term.sub_assign(ArithmeticTerm::from_variable(ch));
                gate_term.sub_assign(ArithmeticTerm::from_variable(c.get_variable()));
                gate_term.add_assign(ArithmeticTerm::constant(E::Fr::one()));

                cs.allocate_main_gate(gate_term)?;
            },
            _ => {
                unreachable!("Boolean `c` is not a constant here");
            }
        }

        Ok(AllocatedBit {
            value: ch_value,
            variable: ch
        }.into())
    }

    /// Computes (a and b) xor (a and c) xor (b and c)
    pub fn sha256_maj<'a, E, CS>(
        cs: &mut CS,
        a: &'a Self,
        b: &'a Self,
        c: &'a Self,
    ) -> Result<Self, SynthesisError>
        where E: Engine,
              CS: ConstraintSystem<E>
    {
        let maj_value = match (a.get_value(), b.get_value(), c.get_value()) {
            (Some(a), Some(b), Some(c)) => {
                // (a and b) xor (a and c) xor (b and c)
                Some((a & b) ^ (a & c) ^ (b & c))
            },
            _ => None
        };

        match (a, b, c) {
            (&Boolean::Constant(_),
            &Boolean::Constant(_),
            &Boolean::Constant(_)) => {
                // They're all constants, so we can just compute the value.

                return Ok(Boolean::Constant(maj_value.expect("they're all constants")));
            },
            (&Boolean::Constant(false), b, c) => {
                // If a is false,
                // (a and b) xor (a and c) xor (b and c)
                // equals
                // (b and c)
                return Boolean::and(
                    cs,
                    b,
                    c
                );
            },
            (a, &Boolean::Constant(false), c) => {
                // If b is false,
                // (a and b) xor (a and c) xor (b and c)
                // equals
                // (a and c)
                return Boolean::and(
                    cs,
                    a,
                    c
                );
            },
            (a, b, &Boolean::Constant(false)) => {
                // If c is false,
                // (a and b) xor (a and c) xor (b and c)
                // equals
                // (a and b)
                return Boolean::and(
                    cs,
                    a,
                    b
                );
            },
            (a, b, &Boolean::Constant(true)) => {
                // If c is true,
                // (a and b) xor (a and c) xor (b and c)
                // equals
                // (a and b) xor (a) xor (b)
                // equals
                // not ((not a) and (not b))
                return Ok(Boolean::and(
                    cs,
                    &a.not(),
                    &b.not()
                )?.not());
            },
            (a, &Boolean::Constant(true), c) => {
                // If b is true,
                // (a and b) xor (a and c) xor (b and c)
                // equals
                // (a) xor (a and c) xor (c)
                return Ok(Boolean::and(
                    cs,
                    &a.not(),
                    &c.not()
                )?.not());
            },
            (&Boolean::Constant(true), b, c) => {
                // If a is true,
                // (a and b) xor (a and c) xor (b and c)
                // equals
                // (b) xor (c) xor (b and c)
                return Ok(Boolean::and(
                    cs,
                    &b.not(),
                    &c.not()
                )?.not());
            },
            (&Boolean::Is(_), &Boolean::Is(_), &Boolean::Is(_)) |
            (&Boolean::Is(_), &Boolean::Is(_), &Boolean::Not(_)) |
            (&Boolean::Is(_), &Boolean::Not(_), &Boolean::Is(_)) |
            (&Boolean::Is(_), &Boolean::Not(_), &Boolean::Not(_)) |
            (&Boolean::Not(_), &Boolean::Is(_), &Boolean::Is(_)) |
            (&Boolean::Not(_), &Boolean::Is(_), &Boolean::Not(_)) |
            (&Boolean::Not(_), &Boolean::Not(_), &Boolean::Is(_)) |
            (&Boolean::Not(_), &Boolean::Not(_), &Boolean::Not(_))
            => {}
        }

        let maj = cs.alloc(|| {
            maj_value.get().map(|v| {
                if *v {
                    E::Fr::one()
                } else {
                    E::Fr::zero()
                }
            })
        })?;

        // ¬(¬a ∧ ¬b) ∧ ¬(¬a ∧ ¬c) ∧ ¬(¬b ∧ ¬c)
        // (1 - ((1 - a) * (1 - b))) * (1 - ((1 - a) * (1 - c))) * (1 - ((1 - b) * (1 - c)))
        // (a + b - ab) * (a + c - ac) * (b + c - bc)
        // -2abc + ab + ac + bc
        // a (-2bc + b + c) + bc
        //
        // (b) * (c) = (bc)
        // (2bc - b - c) * (a) = bc - maj

        let bc = Self::and(
            cs,
            b,
            c
        )?;

        let mut two = E::Fr::one();
        two.double();

        let mut minus_one = E::Fr::one();
        minus_one.negate();

        let mut lc = bc.lc(two);
        lc.add_assign(&b.lc(minus_one));
        lc.add_assign(&c.lc(minus_one));

        let tmp = lc.into_allocated_num(cs)?;

        // tmp * a - bc + maj = 0

        match (a, bc) {
            (Boolean::Is(ref a), Boolean::Is(ref bc)) => {
                // a = a
                // bc = bc
                // tmp * a - bc + maj = 0
                let mut gate_term = MainGateTerm::new();

                let mut multiplicative_term = ArithmeticTerm::from_variable(a.get_variable());
                multiplicative_term = multiplicative_term.mul_by_variable(tmp.get_variable());
                gate_term.add_assign(multiplicative_term);
                gate_term.sub_assign(ArithmeticTerm::from_variable(bc.get_variable()));
                gate_term.add_assign(ArithmeticTerm::from_variable(maj));

                cs.allocate_main_gate(gate_term)?;
            },
            (Boolean::Not(ref a), Boolean::Is(ref bc)) => {
                // a = 1 - a
                // bc = bc
                // - tmp * a + tmp - bc + maj = 0
                let mut gate_term = MainGateTerm::new();

                let mut multiplicative_term = ArithmeticTerm::from_variable(a.get_variable());
                multiplicative_term = multiplicative_term.mul_by_variable(tmp.get_variable());
                gate_term.sub_assign(multiplicative_term);
                gate_term.add_assign(ArithmeticTerm::from_variable(tmp.get_variable()));
                gate_term.sub_assign(ArithmeticTerm::from_variable(bc.get_variable()));
                gate_term.add_assign(ArithmeticTerm::from_variable(maj));

                cs.allocate_main_gate(gate_term)?;
            },
            _ => {
                unreachable!("`a` and `bc` are not constant here, and `bc` can not be Not");
            }
        }

        Ok(AllocatedBit {
            value: maj_value,
            variable: maj
        }.into())
    }
}

impl From<AllocatedBit> for Boolean {
    fn from(b: AllocatedBit) -> Boolean {
        Boolean::Is(b)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use bellman::pairing::bn256::{Bn256, Fr};
    use bellman::pairing::ff::{Field, PrimeField};
    use ::circuit::test::*;

    use crate::bellman::plonk::better_better_cs::cs::*;

    #[test]
    fn test_xor() {
        for a_val in [false, true].iter() {
            for b_val in [false, true].iter() {
                let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();
                let a = AllocatedBit::alloc(&mut cs, Some(*a_val)).unwrap();
                let b = AllocatedBit::alloc(&mut cs, Some(*b_val)).unwrap();
                let c = AllocatedBit::xor(&mut cs, &a, &b).unwrap();
                assert_eq!(c.value.unwrap(), *a_val ^ *b_val);

                assert!(cs.is_satisfied(), "unsatisfied for a = {}, b = {}", a_val, b_val);
            }
        }
    }

    #[test]
    fn test_and() {
        for a_val in [false, true].iter() {
            for b_val in [false, true].iter() {
                let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();
                let a = AllocatedBit::alloc(&mut cs, Some(*a_val)).unwrap();
                let b = AllocatedBit::alloc(&mut cs, Some(*b_val)).unwrap();
                let c = AllocatedBit::and(&mut cs, &a, &b).unwrap();
                assert_eq!(c.value.unwrap(), *a_val & *b_val);

                assert!(cs.is_satisfied());
            }
        }
    }

    #[test]
    fn test_and_not() {
        for a_val in [false, true].iter() {
            for b_val in [false, true].iter() {
                let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();
                let a = AllocatedBit::alloc(&mut cs, Some(*a_val)).unwrap();
                let b = AllocatedBit::alloc(&mut cs, Some(*b_val)).unwrap();
                let c = AllocatedBit::and_not(&mut cs, &a, &b).unwrap();
                assert_eq!(c.value.unwrap(), *a_val & !*b_val);

                assert!(cs.is_satisfied());
            }
        }
    }

    #[test]
    fn test_nor() {
        for a_val in [false, true].iter() {
            for b_val in [false, true].iter() {
                let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();
                let a = AllocatedBit::alloc(&mut cs, Some(*a_val)).unwrap();
                let b = AllocatedBit::alloc(&mut cs, Some(*b_val)).unwrap();
                let c = AllocatedBit::nor(&mut cs, &a, &b).unwrap();
                assert_eq!(c.value.unwrap(), !*a_val & !*b_val);

                assert!(cs.is_satisfied());
            }
        }
    }

    #[test]
    fn test_enforce_equal() {
        for a_bool in [false, true].iter().cloned() {
            for b_bool in [false, true].iter().cloned() {
                for a_neg in [false, true].iter().cloned() {
                    for b_neg in [false, true].iter().cloned() {
                        {
                            let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

                            let mut a = Boolean::from(AllocatedBit::alloc(&mut cs, Some(a_bool)).unwrap());
                            let mut b = Boolean::from(AllocatedBit::alloc(&mut cs, Some(b_bool)).unwrap());

                            if a_neg {
                                a = a.not();
                            }
                            if b_neg {
                                b = b.not();
                            }

                            Boolean::enforce_equal(&mut cs, &a, &b).unwrap();

                            assert_eq!(
                                cs.is_satisfied(),
                                (a_bool ^ a_neg) == (b_bool ^ b_neg)
                            );
                        }
                        {
                            let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

                            let mut a = Boolean::Constant(a_bool);
                            let mut b = Boolean::from(AllocatedBit::alloc(&mut cs, Some(b_bool)).unwrap());

                            if a_neg {
                                a = a.not();
                            }
                            if b_neg {
                                b = b.not();
                            }

                            Boolean::enforce_equal(&mut cs, &a, &b).unwrap();

                            assert_eq!(
                                cs.is_satisfied(),
                                (a_bool ^ a_neg) == (b_bool ^ b_neg)
                            );
                        }
                        {
                            let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

                            let mut a = Boolean::from(AllocatedBit::alloc(&mut cs, Some(a_bool)).unwrap());
                            let mut b = Boolean::Constant(b_bool);

                            if a_neg {
                                a = a.not();
                            }
                            if b_neg {
                                b = b.not();
                            }

                            Boolean::enforce_equal(&mut cs, &a, &b).unwrap();

                            assert_eq!(
                                cs.is_satisfied(),
                                (a_bool ^ a_neg) == (b_bool ^ b_neg)
                            );
                        }
                        {
                            let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

                            let mut a = Boolean::Constant(a_bool);
                            let mut b = Boolean::Constant(b_bool);

                            if a_neg {
                                a = a.not();
                            }
                            if b_neg {
                                b = b.not();
                            }

                            let result = Boolean::enforce_equal(&mut cs, &a, &b);

                            if (a_bool ^ a_neg) == (b_bool ^ b_neg) {
                                assert!(result.is_ok());
                                assert!(cs.is_satisfied());
                            } else {
                                assert!(result.is_err());
                            }
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn test_boolean_negation() {
        let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

        let mut b = Boolean::from(AllocatedBit::alloc(&mut cs, Some(true)).unwrap());

        match b {
            Boolean::Is(_) => {},
            _ => panic!("unexpected value")
        }

        b = b.not();

        match b {
            Boolean::Not(_) => {},
            _ => panic!("unexpected value")
        }

        b = b.not();

        match b {
            Boolean::Is(_) => {},
            _ => panic!("unexpected value")
        }

        b = Boolean::constant(true);

        match b {
            Boolean::Constant(true) => {},
            _ => panic!("unexpected value")
        }

        b = b.not();

        match b {
            Boolean::Constant(false) => {},
            _ => panic!("unexpected value")
        }

        b = b.not();

        match b {
            Boolean::Constant(true) => {},
            _ => panic!("unexpected value")
        }
    }

    #[derive(Copy, Clone, Debug)]
    enum OperandType {
        True,
        False,
        AllocatedTrue,
        AllocatedFalse,
        NegatedAllocatedTrue,
        NegatedAllocatedFalse
    }

    impl OperandType {
        fn is_constant(&self) -> bool {
            match *self {
                OperandType::True => true,
                OperandType::False => true,
                OperandType::AllocatedTrue => false,
                OperandType::AllocatedFalse => false,
                OperandType::NegatedAllocatedTrue => false,
                OperandType::NegatedAllocatedFalse => false
            }
        }

        fn val(&self) -> bool {
            match *self {
                OperandType::True => true,
                OperandType::False => false,
                OperandType::AllocatedTrue => true,
                OperandType::AllocatedFalse => false,
                OperandType::NegatedAllocatedTrue => false,
                OperandType::NegatedAllocatedFalse => true
            }
        }
    }


    #[test]
    fn test_boolean_xor() {
        let variants = [
            OperandType::True,
            OperandType::False,
            OperandType::AllocatedTrue,
            OperandType::AllocatedFalse,
            OperandType::NegatedAllocatedTrue,
            OperandType::NegatedAllocatedFalse
        ];

        for first_operand in variants.iter().cloned() {
            for second_operand in variants.iter().cloned() {
                let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

                let a;
                let b;

                {
                    let mut dyn_construct = |operand, name| {
                        match operand {
                            OperandType::True => Boolean::constant(true),
                            OperandType::False => Boolean::constant(false),
                            OperandType::AllocatedTrue => Boolean::from(AllocatedBit::alloc(&mut cs, Some(true)).unwrap()),
                            OperandType::AllocatedFalse => Boolean::from(AllocatedBit::alloc(&mut cs, Some(false)).unwrap()),
                            OperandType::NegatedAllocatedTrue => Boolean::from(AllocatedBit::alloc(&mut cs, Some(true)).unwrap()).not(),
                            OperandType::NegatedAllocatedFalse => Boolean::from(AllocatedBit::alloc(&mut cs, Some(false)).unwrap()).not(),
                        }
                    };

                    a = dyn_construct(first_operand, "a");
                    b = dyn_construct(second_operand, "b");
                }

                let c = Boolean::xor(&mut cs, &a, &b).unwrap();

                assert!(cs.is_satisfied());

                match (first_operand, second_operand, c) {
                    (OperandType::True, OperandType::True, Boolean::Constant(false)) => {},
                    (OperandType::True, OperandType::False, Boolean::Constant(true)) => {},
                    (OperandType::True, OperandType::AllocatedTrue, Boolean::Not(_)) => {},
                    (OperandType::True, OperandType::AllocatedFalse, Boolean::Not(_)) => {},
                    (OperandType::True, OperandType::NegatedAllocatedTrue, Boolean::Is(_)) => {},
                    (OperandType::True, OperandType::NegatedAllocatedFalse, Boolean::Is(_)) => {},

                    (OperandType::False, OperandType::True, Boolean::Constant(true)) => {},
                    (OperandType::False, OperandType::False, Boolean::Constant(false)) => {},
                    (OperandType::False, OperandType::AllocatedTrue, Boolean::Is(_)) => {},
                    (OperandType::False, OperandType::AllocatedFalse, Boolean::Is(_)) => {},
                    (OperandType::False, OperandType::NegatedAllocatedTrue, Boolean::Not(_)) => {},
                    (OperandType::False, OperandType::NegatedAllocatedFalse, Boolean::Not(_)) => {},

                    (OperandType::AllocatedTrue, OperandType::True, Boolean::Not(_)) => {},
                    (OperandType::AllocatedTrue, OperandType::False, Boolean::Is(_)) => {},
                    (OperandType::AllocatedTrue, OperandType::AllocatedTrue, Boolean::Is(ref v)) => {
                        assert_eq!(v.value, Some(false));
                    },
                    (OperandType::AllocatedTrue, OperandType::AllocatedFalse, Boolean::Is(ref v)) => {
                        assert_eq!(v.value, Some(true));
                    },
                    (OperandType::AllocatedTrue, OperandType::NegatedAllocatedTrue, Boolean::Not(ref v)) => {
                        assert_eq!(v.value, Some(false));
                    },
                    (OperandType::AllocatedTrue, OperandType::NegatedAllocatedFalse, Boolean::Not(ref v)) => {
                        assert_eq!(v.value, Some(true));
                    },

                    (OperandType::AllocatedFalse, OperandType::True, Boolean::Not(_)) => {},
                    (OperandType::AllocatedFalse, OperandType::False, Boolean::Is(_)) => {},
                    (OperandType::AllocatedFalse, OperandType::AllocatedTrue, Boolean::Is(ref v)) => {
                        assert_eq!(v.value, Some(true));
                    },
                    (OperandType::AllocatedFalse, OperandType::AllocatedFalse, Boolean::Is(ref v)) => {
                        assert_eq!(v.value, Some(false));
                    },
                    (OperandType::AllocatedFalse, OperandType::NegatedAllocatedTrue, Boolean::Not(ref v)) => {
                        assert_eq!(v.value, Some(true));
                    },
                    (OperandType::AllocatedFalse, OperandType::NegatedAllocatedFalse, Boolean::Not(ref v)) => {
                        assert_eq!(v.value, Some(false));
                    },

                    (OperandType::NegatedAllocatedTrue, OperandType::True, Boolean::Is(_)) => {},
                    (OperandType::NegatedAllocatedTrue, OperandType::False, Boolean::Not(_)) => {},
                    (OperandType::NegatedAllocatedTrue, OperandType::AllocatedTrue, Boolean::Not(ref v)) => {
                        assert_eq!(v.value, Some(false));
                    },
                    (OperandType::NegatedAllocatedTrue, OperandType::AllocatedFalse, Boolean::Not(ref v)) => {
                        assert_eq!(v.value, Some(true));
                    },
                    (OperandType::NegatedAllocatedTrue, OperandType::NegatedAllocatedTrue, Boolean::Is(ref v)) => {
                        assert_eq!(v.value, Some(false));
                    },
                    (OperandType::NegatedAllocatedTrue, OperandType::NegatedAllocatedFalse, Boolean::Is(ref v)) => {
                        assert_eq!(v.value, Some(true));
                    },

                    (OperandType::NegatedAllocatedFalse, OperandType::True, Boolean::Is(_)) => {},
                    (OperandType::NegatedAllocatedFalse, OperandType::False, Boolean::Not(_)) => {},
                    (OperandType::NegatedAllocatedFalse, OperandType::AllocatedTrue, Boolean::Not(ref v)) => {
                        assert_eq!(v.value, Some(true));
                    },
                    (OperandType::NegatedAllocatedFalse, OperandType::AllocatedFalse, Boolean::Not(ref v)) => {
                        assert_eq!(v.value, Some(false));
                    },
                    (OperandType::NegatedAllocatedFalse, OperandType::NegatedAllocatedTrue, Boolean::Is(ref v)) => {
                        assert_eq!(v.value, Some(true));
                    },
                    (OperandType::NegatedAllocatedFalse, OperandType::NegatedAllocatedFalse, Boolean::Is(ref v)) => {
                        assert_eq!(v.value, Some(false));
                    },

                    _ => panic!("this should never be encountered")
                }
            }
        }
    }

    #[test]
    fn test_boolean_and() {
        let variants = [
            OperandType::True,
            OperandType::False,
            OperandType::AllocatedTrue,
            OperandType::AllocatedFalse,
            OperandType::NegatedAllocatedTrue,
            OperandType::NegatedAllocatedFalse
        ];

        for first_operand in variants.iter().cloned() {
            for second_operand in variants.iter().cloned() {
                let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

                let a;
                let b;

                {
                    let mut dyn_construct = |operand, name| {

                        match operand {
                            OperandType::True => Boolean::constant(true),
                            OperandType::False => Boolean::constant(false),
                            OperandType::AllocatedTrue => Boolean::from(AllocatedBit::alloc(&mut cs, Some(true)).unwrap()),
                            OperandType::AllocatedFalse => Boolean::from(AllocatedBit::alloc(&mut cs, Some(false)).unwrap()),
                            OperandType::NegatedAllocatedTrue => Boolean::from(AllocatedBit::alloc(&mut cs, Some(true)).unwrap()).not(),
                            OperandType::NegatedAllocatedFalse => Boolean::from(AllocatedBit::alloc(&mut cs, Some(false)).unwrap()).not(),
                        }
                    };

                    a = dyn_construct(first_operand, "a");
                    b = dyn_construct(second_operand, "b");
                }

                let c = Boolean::and(&mut cs, &a, &b).unwrap();

                assert!(cs.is_satisfied());

                match (first_operand, second_operand, c) {
                    (OperandType::True, OperandType::True, Boolean::Constant(true)) => {},
                    (OperandType::True, OperandType::False, Boolean::Constant(false)) => {},
                    (OperandType::True, OperandType::AllocatedTrue, Boolean::Is(_)) => {},
                    (OperandType::True, OperandType::AllocatedFalse, Boolean::Is(_)) => {},
                    (OperandType::True, OperandType::NegatedAllocatedTrue, Boolean::Not(_)) => {},
                    (OperandType::True, OperandType::NegatedAllocatedFalse, Boolean::Not(_)) => {},

                    (OperandType::False, OperandType::True, Boolean::Constant(false)) => {},
                    (OperandType::False, OperandType::False, Boolean::Constant(false)) => {},
                    (OperandType::False, OperandType::AllocatedTrue, Boolean::Constant(false)) => {},
                    (OperandType::False, OperandType::AllocatedFalse, Boolean::Constant(false)) => {},
                    (OperandType::False, OperandType::NegatedAllocatedTrue, Boolean::Constant(false)) => {},
                    (OperandType::False, OperandType::NegatedAllocatedFalse, Boolean::Constant(false)) => {},

                    (OperandType::AllocatedTrue, OperandType::True, Boolean::Is(_)) => {},
                    (OperandType::AllocatedTrue, OperandType::False, Boolean::Constant(false)) => {},
                    (OperandType::AllocatedTrue, OperandType::AllocatedTrue, Boolean::Is(ref v)) => {
                        assert_eq!(v.value, Some(true));
                    },
                    (OperandType::AllocatedTrue, OperandType::AllocatedFalse, Boolean::Is(ref v)) => {
                        assert_eq!(v.value, Some(false));
                    },
                    (OperandType::AllocatedTrue, OperandType::NegatedAllocatedTrue, Boolean::Is(ref v)) => {
                        assert_eq!(v.value, Some(false));
                    },
                    (OperandType::AllocatedTrue, OperandType::NegatedAllocatedFalse, Boolean::Is(ref v)) => {
                        assert_eq!(v.value, Some(true));
                    },

                    (OperandType::AllocatedFalse, OperandType::True, Boolean::Is(_)) => {},
                    (OperandType::AllocatedFalse, OperandType::False, Boolean::Constant(false)) => {},
                    (OperandType::AllocatedFalse, OperandType::AllocatedTrue, Boolean::Is(ref v)) => {
                        assert_eq!(v.value, Some(false));
                    },
                    (OperandType::AllocatedFalse, OperandType::AllocatedFalse, Boolean::Is(ref v)) => {
                        assert_eq!(v.value, Some(false));
                    },
                    (OperandType::AllocatedFalse, OperandType::NegatedAllocatedTrue, Boolean::Is(ref v)) => {
                        assert_eq!(v.value, Some(false));
                    },
                    (OperandType::AllocatedFalse, OperandType::NegatedAllocatedFalse, Boolean::Is(ref v)) => {
                        assert_eq!(v.value, Some(false));
                    },

                    (OperandType::NegatedAllocatedTrue, OperandType::True, Boolean::Not(_)) => {},
                    (OperandType::NegatedAllocatedTrue, OperandType::False, Boolean::Constant(false)) => {},
                    (OperandType::NegatedAllocatedTrue, OperandType::AllocatedTrue, Boolean::Is(ref v)) => {
                        assert_eq!(v.value, Some(false));
                    },
                    (OperandType::NegatedAllocatedTrue, OperandType::AllocatedFalse, Boolean::Is(ref v)) => {
                        assert_eq!(v.value, Some(false));
                    },
                    (OperandType::NegatedAllocatedTrue, OperandType::NegatedAllocatedTrue, Boolean::Is(ref v)) => {
                        assert_eq!(v.value, Some(false));
                    },
                    (OperandType::NegatedAllocatedTrue, OperandType::NegatedAllocatedFalse, Boolean::Is(ref v)) => {
                        assert_eq!(v.value, Some(false));
                    },

                    (OperandType::NegatedAllocatedFalse, OperandType::True, Boolean::Not(_)) => {},
                    (OperandType::NegatedAllocatedFalse, OperandType::False, Boolean::Constant(false)) => {},
                    (OperandType::NegatedAllocatedFalse, OperandType::AllocatedTrue, Boolean::Is(ref v)) => {
                        assert_eq!(v.value, Some(true));
                    },
                    (OperandType::NegatedAllocatedFalse, OperandType::AllocatedFalse, Boolean::Is(ref v)) => {
                        assert_eq!(v.value, Some(false));
                    },
                    (OperandType::NegatedAllocatedFalse, OperandType::NegatedAllocatedTrue, Boolean::Is(ref v)) => {
                        assert_eq!(v.value, Some(false));
                    },
                    (OperandType::NegatedAllocatedFalse, OperandType::NegatedAllocatedFalse, Boolean::Is(ref v)) => {
                        assert_eq!(v.value, Some(true));
                    },

                    _ => {
                        panic!("unexpected behavior at {:?} AND {:?}", first_operand, second_operand);
                    }
                }
            }
        }
    }

    #[test]
    fn test_u64_into_boolean_vec_le() {
        let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

        let bits = u64_into_boolean_vec_le(&mut cs, Some(17234652694787248421)).unwrap();

        assert!(cs.is_satisfied());

        assert_eq!(bits.len(), 64);

        assert_eq!(bits[63 - 0].get_value().unwrap(), true);
        assert_eq!(bits[63 - 1].get_value().unwrap(), true);
        assert_eq!(bits[63 - 2].get_value().unwrap(), true);
        assert_eq!(bits[63 - 3].get_value().unwrap(), false);
        assert_eq!(bits[63 - 4].get_value().unwrap(), true);
        assert_eq!(bits[63 - 5].get_value().unwrap(), true);
        assert_eq!(bits[63 - 20].get_value().unwrap(), true);
        assert_eq!(bits[63 - 21].get_value().unwrap(), false);
        assert_eq!(bits[63 - 22].get_value().unwrap(), false);
    }

    #[test]
    fn test_field_into_allocated_bits_le() {
        use crate::bellman::pairing::bls12_381;
        let mut cs = TrivialAssembly::<bls12_381::Bls12, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

        let r = bls12_381::Fr::from_str("9147677615426976802526883532204139322118074541891858454835346926874644257775").unwrap();

        let bits = field_into_allocated_bits_le(&mut cs, Some(r)).unwrap();

        let char_bits: Vec<_> = BitIterator::new(bls12_381::Fr::char()).collect();
        assert!(char_bits[0] == false);
        assert!(char_bits[1] == true);

        assert!(cs.is_satisfied());

        assert_eq!(bits.len(), 255);

        assert_eq!(bits[254 - 0].value.unwrap(), false);
        assert_eq!(bits[254 - 1].value.unwrap(), false);
        assert_eq!(bits[254 - 2].value.unwrap(), true);
        assert_eq!(bits[254 - 3].value.unwrap(), false);
        assert_eq!(bits[254 - 4].value.unwrap(), true);
        assert_eq!(bits[254 - 5].value.unwrap(), false);
        assert_eq!(bits[254 - 20].value.unwrap(), true);
        assert_eq!(bits[254 - 23].value.unwrap(), true);
    }

    #[test]
    fn test_boolean_sha256_ch() {
        let variants = [
            OperandType::True,
            OperandType::False,
            OperandType::AllocatedTrue,
            OperandType::AllocatedFalse,
            OperandType::NegatedAllocatedTrue,
            OperandType::NegatedAllocatedFalse
        ];

        for first_operand in variants.iter().cloned() {
            for second_operand in variants.iter().cloned() {
                for third_operand in variants.iter().cloned() {
                    let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

                    let a;
                    let b;
                    let c;

                    // ch = (a and b) xor ((not a) and c)
                    let expected = (first_operand.val() & second_operand.val()) ^
                                   ((!first_operand.val()) & third_operand.val());

                    {
                        let mut dyn_construct = |operand, name| {

                            match operand {
                                OperandType::True => Boolean::constant(true),
                                OperandType::False => Boolean::constant(false),
                                OperandType::AllocatedTrue => Boolean::from(AllocatedBit::alloc(&mut cs, Some(true)).unwrap()),
                                OperandType::AllocatedFalse => Boolean::from(AllocatedBit::alloc(&mut cs, Some(false)).unwrap()),
                                OperandType::NegatedAllocatedTrue => Boolean::from(AllocatedBit::alloc(&mut cs, Some(true)).unwrap()).not(),
                                OperandType::NegatedAllocatedFalse => Boolean::from(AllocatedBit::alloc(&mut cs, Some(false)).unwrap()).not(),
                            }
                        };

                        a = dyn_construct(first_operand, "a");
                        b = dyn_construct(second_operand, "b");
                        c = dyn_construct(third_operand, "c");
                    }

                    let ch = Boolean::sha256_ch(&mut cs, &a, &b, &c).unwrap();

                    assert!(cs.is_satisfied());

                    assert_eq!(ch.get_value().unwrap(), expected);

                    if first_operand.is_constant() ||
                       second_operand.is_constant() ||
                       third_operand.is_constant()
                    {
                        if first_operand.is_constant() &&
                           second_operand.is_constant() &&
                           third_operand.is_constant()
                        {
                            assert_eq!(cs.n(), 0);
                        }
                    }
                    else
                    {
                        assert_eq!(ch.get_value().unwrap(), expected);
                    }
                }
            }
        }
    }

    #[test]
    fn test_boolean_sha256_maj() {
        let variants = [
            OperandType::True,
            OperandType::False,
            OperandType::AllocatedTrue,
            OperandType::AllocatedFalse,
            OperandType::NegatedAllocatedTrue,
            OperandType::NegatedAllocatedFalse
        ];

        for first_operand in variants.iter().cloned() {
            for second_operand in variants.iter().cloned() {
                for third_operand in variants.iter().cloned() {
                    let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

                    let a;
                    let b;
                    let c;

                    // maj = (a and b) xor (a and c) xor (b and c)
                    let expected = (first_operand.val() & second_operand.val()) ^
                                   (first_operand.val() & third_operand.val()) ^
                                   (second_operand.val() & third_operand.val());

                    {
                        let mut dyn_construct = |operand, name| {

                            match operand {
                                OperandType::True => Boolean::constant(true),
                                OperandType::False => Boolean::constant(false),
                                OperandType::AllocatedTrue => Boolean::from(AllocatedBit::alloc(&mut cs, Some(true)).unwrap()),
                                OperandType::AllocatedFalse => Boolean::from(AllocatedBit::alloc(&mut cs, Some(false)).unwrap()),
                                OperandType::NegatedAllocatedTrue => Boolean::from(AllocatedBit::alloc(&mut cs, Some(true)).unwrap()).not(),
                                OperandType::NegatedAllocatedFalse => Boolean::from(AllocatedBit::alloc(&mut cs, Some(false)).unwrap()).not(),
                            }
                        };

                        a = dyn_construct(first_operand, "a");
                        b = dyn_construct(second_operand, "b");
                        c = dyn_construct(third_operand, "c");
                    }

                    let maj = Boolean::sha256_maj(&mut cs, &a, &b, &c).unwrap();

                    assert!(cs.is_satisfied());

                    assert_eq!(maj.get_value().unwrap(), expected);

                    if first_operand.is_constant() ||
                       second_operand.is_constant() ||
                       third_operand.is_constant()
                    {
                        if first_operand.is_constant() &&
                           second_operand.is_constant() &&
                           third_operand.is_constant()
                        {
                            assert_eq!(cs.n(), 0);
                        }
                    }
                    else
                    {
                        assert_eq!(maj.get_value().unwrap(), expected);
                    }
                }
            }
        }
    }
}
