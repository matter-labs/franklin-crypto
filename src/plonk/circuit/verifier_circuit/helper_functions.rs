use crate::plonk::circuit::curve::sw_affine::AffinePoint;
use crate::plonk::circuit::bigint::field::*;
use crate::plonk::circuit::allocated_num::*;
use crate::plonk::circuit::linear_combination::*;

use crate::bellman::pairing::{
    Engine,
    CurveAffine,
};

use crate::bellman::pairing::ff::{
    Field,
    PrimeField,
};

use crate::bellman::{
    SynthesisError,
};

use crate::bellman::plonk::better_better_cs::cs::{
    Variable, 
    ConstraintSystem,
};


pub fn evaluate_inverse_vanishing_poly<E, CS>(
    cs: &mut CS, 
    vahisning_size: usize,
    omega_inv : &E::Fr, 
    point: AllocatedNum<E>,
    point_in_pow_n : AllocatedNum<E>,
) -> Result<AllocatedNum<E>, SynthesisError> 
where E: Engine, CS: ConstraintSystem<E>
{
    assert!(vahisning_size.is_power_of_two());

    // update from the paper - it should not hold for the last generator, omega^(n) in original notations

    // Z(X) = (X^n - 1) / (X - omega^(n-1)) => Z^{-1}(X) = (X - omega^(n-1)) / (X^(n) - 1)
    // note that omega^(n-1) = omega^(-1)

    let mut numerator = point.sub_constant(cs, *omega_inv)?;
    let mut denominator = point_in_pow_n.sub_constant(cs, E::Fr::one())?;

    numerator.div(cs, &denominator)
}


pub fn evaluate_lagrange_poly<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    vahisning_size: usize, 
    poly_number: usize,
    omega_inv : &E::Fr,
    point: AllocatedNum<E>,
    // point raise to n-th power (n = vanishing size)
    point_in_pow_n : AllocatedNum<E>,
) -> Result<AllocatedNum<E>, SynthesisError> 
{
    assert!(vahisning_size.is_power_of_two());

    // L_0(X) = (Z_H(X) / (X - 1)) * (1/n) and L_0(1) = 1
    // L_k(omega) = 1 = L_0(omega * omega^-k)
    // L_k(z) = L_0(z * omega^-k) = (1/n-1) * (z^n - 1)/(z * omega^{-k} - 1)

    // TODO: I think the code above has a bug - the scale coefficient should be 1/(n-1) instead of n

    let mut numerator  = point_in_pow_n.sub_constant(cs, E::Fr::one())?;
    let omega_inv_pow = omega_inv.pow([poly_number as u64]);

    let mut denominator_lc : LinearCombination<E> = point.into();
    denominator_lc.scale(&omega_inv_pow);
    denominator_lc.sub_assign_constant(E::Fr::one());

    let mut repr = E::Fr::zero().into_repr();
    repr.as_mut()[0] = vahisning_size as u64;
    let size_fe = E::Fr::from_repr(repr).expect("is a valid representation");
    denominator_lc.scale(&size_fe);
    let denominator = denominator_lc.into_allocated_num(cs)?;

    numerator.div(cs, &denominator);
}

// check point is on curve
// subgroup check (using substraction - addition chains)

// checked addition