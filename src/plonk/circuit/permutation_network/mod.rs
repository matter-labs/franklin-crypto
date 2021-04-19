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

use super::allocated_num::{
    AllocatedNum,
    Num
};

use super::boolean::{
    AllocatedBit,
    Boolean
};

mod witness;
mod circuit;

pub use self::witness::*;
pub use self::circuit::*;