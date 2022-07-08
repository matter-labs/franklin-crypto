use super::*;
use crate::bellman::pairing::ff::{BitIterator, Field, PrimeField, PrimeFieldRepr};
use crate::bellman::pairing::Engine;
use crate::bellman::plonk::better_better_cs::cs::*;
use crate::bellman::SynthesisError;
use crate::plonk::circuit::boolean::Boolean;
use crate::plonk::circuit::linear_combination::LinearCombination;

pub fn smart_or<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    bools: &[Boolean],
) -> Result<Boolean, SynthesisError> {
    const LIMIT: usize = 6;
    if bools.len() == 0 {
        return Ok(Boolean::constant(false));
    }

    if bools.len() == 1 {
        return Ok(bools[0]);
    }

    if bools.len() == 2 {
        // 1 gate
        let result = Boolean::or(cs, &bools[0], &bools[1])?;
        return Ok(result);
    }

    // 1 gate for 2,
    // 2 gates for 3, etc
    if bools.len() < LIMIT {
        // 1 gate
        let mut result = Boolean::or(cs, &bools[0], &bools[1])?;
        // len - 2 gates
        for b in bools[2..].iter() {
            result = Boolean::or(cs, &result, &b)?;
        }
        return Ok(result);
    }

    // 1 gate for 3
    // 2 gates for 6
    // 3 gates for 9, etc
    let mut lc = LinearCombination::zero();
    for b in bools.iter() {
        lc.add_assign_boolean_with_coeff(b, E::Fr::one());
    }
    let as_num = lc.into_num(cs)?;

    // 3 gates here
    let all_false = as_num.is_zero(cs)?;

    // so 4 gates for 3
    // 5 gates for 5
    // 6 gates for 9
    // so we win at 6+

    Ok(all_false.not())
}

pub fn smart_and<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    bools: &[Boolean],
) -> Result<Boolean, SynthesisError> {
    const LIMIT: usize = 6;
    assert!(bools.len() > 0);
    if bools.len() == 1 {
        return Ok(bools[0]);
    }

    if bools.len() == 2 {
        // 1 gate
        let result = Boolean::and(cs, &bools[0], &bools[1])?;
        return Ok(result);
    }

    // 1 gate for 2,
    // 2 gates for 3, etc
    if bools.len() < LIMIT {
        // 1 gate
        let mut result = Boolean::and(cs, &bools[0], &bools[1])?;
        // len - 2 gates
        for b in bools[2..].iter() {
            result = Boolean::and(cs, &result, &b)?;
        }
        return Ok(result);
    }

    // 1 gate for 3
    // 2 gates for 6
    // 3 gates for 9, etc
    let mut lc = LinearCombination::zero();
    let num_elements_as_fr = E::Fr::from_str(&bools.len().to_string()).unwrap();
    lc.sub_assign_constant(num_elements_as_fr);
    for b in bools.iter() {
        lc.add_assign_boolean_with_coeff(b, E::Fr::one());
    }
    let as_num = lc.into_num(cs)?;

    // 3 gates here
    let all_true = as_num.is_zero(cs)?;

    // so 4 gates for 3
    // 5 gates for 5
    // 6 gates for 9
    // so we win at 6+

    Ok(all_true)
}
