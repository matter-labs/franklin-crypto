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
    PlonkConstraintSystemParams,
    PlonkCsWidth4WithNextStepParams,
    TrivialAssembly
};

use crate::bellman::plonk::better_better_cs::data_structures::PolyIdentifier;
use crate::bellman::plonk::better_better_cs::lookup_tables::*;

use crate::plonk::circuit::Assignment;
use super::*;
use super::bigint::*;

use crate::plonk::circuit::allocated_num::{AllocatedNum, Num};
use crate::plonk::circuit::simple_term::{Term};
use crate::plonk::circuit::linear_combination::LinearCombination;

const DEFAULT_RANGE_TABLE_NAME_PREFIX: &'static str = "Range check table over 3 columns for";

pub fn inscribe_default_range_table_for_bit_width_over_first_three_columns<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    width: usize
) -> Result<(), SynthesisError> {
    let over = vec![PolyIdentifier::VariablesPolynomial(0), PolyIdentifier::VariablesPolynomial(1), PolyIdentifier::VariablesPolynomial(2)];
    let table = LookupTableApplication::new_range_table_of_width_3(width, over)?;
    cs.add_table(table)?;

    Ok(())
}

pub fn inscribe_range_table_for_bit_width_over_first_three_columns<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    width: usize
) -> Result<String, SynthesisError> {
    assert!(width > 0);
    let generator = move || {
        format!("{} {} bits over A/B/C", DEFAULT_RANGE_TABLE_NAME_PREFIX, width)
    };
    let name = (&generator)();
    if let Ok(..) = cs.get_table(&name) {
        return Ok(name);
    }

    let table_internal = RangeCheckTableOverOneColumnOfWidth3::new(width);
    let over = vec![PolyIdentifier::VariablesPolynomial(0), PolyIdentifier::VariablesPolynomial(1), PolyIdentifier::VariablesPolynomial(2)];
    let name_generator = Box::new(generator) as Box<dyn Fn() -> String + Send + Sync>;

    let application = LookupTableApplication::new(
        "Range check table",
        table_internal,
        over,
        Some(name_generator),
        true
    );

    cs.add_table(application)?;

    Ok(name)
}

pub fn get_name_for_range_table_for_bit_width_over_first_three_columns(
    width: usize
) -> String {
    assert!(width > 0);
    format!("{} {} bits over A/B/C", DEFAULT_RANGE_TABLE_NAME_PREFIX, width)
}

