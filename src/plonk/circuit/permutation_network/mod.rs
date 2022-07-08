use crate::bellman::pairing::Engine;

use crate::bellman::pairing::ff::{BitIterator, Field, PrimeField, PrimeFieldRepr};

use crate::bellman::SynthesisError;

use crate::bellman::plonk::better_better_cs::cs::{
    ArithmeticTerm, ConstraintSystem, MainGateTerm, Variable,
};

use crate::plonk::circuit::Assignment;

use super::allocated_num::{AllocatedNum, Num};

use super::boolean::{AllocatedBit, Boolean};

mod circuit;
mod witness;

pub use self::circuit::*;
pub use self::witness::*;
