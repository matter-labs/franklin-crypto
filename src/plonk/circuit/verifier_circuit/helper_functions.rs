use crate::plonk::circuit::curve::sw_affine::AffinePoint;
use crate::plonk::circuit::bigint::field::*;
use crate::plonk::circuit::allocated_num::*;
use crate::plonk::circuit::boolean::*;
use crate::plonk::circuit::linear_combination::*;
use crate::plonk::circuit::simple_term::*;

use crate::bellman::pairing::{
    Engine,
    GenericCurveAffine,
};

use crate::bellman::pairing::ff::{
    Field,
    PrimeField,
    BitIterator,
};

use crate::bellman::{
    SynthesisError,
};

use crate::bellman::plonk::better_better_cs::cs::{
    Variable, 
    ConstraintSystem,
};

pub fn evaluate_vanishing_poly<E, CS>(
    cs: &mut CS, 
    point_in_pow_n : AllocatedNum<E>,
) -> Result<AllocatedNum<E>, SynthesisError> 
where E: Engine, CS: ConstraintSystem<E>
{
    point_in_pow_n.sub_constant(cs, E::Fr::one())
}

pub fn evaluate_vanishing_poly_without_last_point<E, CS>(
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

    // Z(X) = (X^n - 1) / (X - omega^(n-1)) 
    // note that omega^(n-1) = omega^(-1)

    let numerator = point_in_pow_n.sub_constant(cs, E::Fr::one())?;
    let denominator = point.sub_constant(cs, *omega_inv)?;
     
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

    let numerator  = point_in_pow_n.sub_constant(cs, E::Fr::one())?;
    let omega_inv_pow = omega_inv.pow([poly_number as u64]);

    let mut denominator_lc : LinearCombination<E> = point.into();
    denominator_lc.scale(&omega_inv_pow);
    denominator_lc.sub_assign_constant(E::Fr::one());

    let mut repr = E::Fr::zero().into_repr();
    repr.as_mut()[0] = vahisning_size as u64;
    let size_fe = E::Fr::from_repr(repr).expect("is a valid representation");
    denominator_lc.scale(&size_fe);
    let denominator = denominator_lc.into_allocated_num(cs)?;

    numerator.div(cs, &denominator)
}


pub fn evaluate_lagrange_poly_for_variable_domain_size<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    poly_number: usize,
    domain_size: AllocatedNum<E>,
    omega_inv : &AllocatedNum<E>,
    point: AllocatedNum<E>,
    // point raise to n-th power (n = vanishing size)
    point_in_pow_n : AllocatedNum<E>,
) -> Result<AllocatedNum<E>, SynthesisError> 
{
    // L_0(X) = (Z_H(X) / (X - 1)) * (1/n) and L_0(1) = 1
    // L_k(omega) = 1 = L_0(omega * omega^-k)
    // L_k(z) = L_0(z * omega^-k) = (1/n-1) * (z^n - 1)/(z * omega^{-k} - 1)

    let numerator  = point_in_pow_n.sub_constant(cs, E::Fr::one())?;
    let omega_inv_pow = if poly_number == 0 {
        AllocatedNum::<E>::one(cs)
    } else {
        let poly_num_decomposed = decompose_const_to_bits::<E, _>(&[poly_number as u64]);
        AllocatedNum::pow(cs, omega_inv, &poly_num_decomposed)?
    };

    let point_as_term = Term::<E>::from_num(Num::Variable(point));
    let omega_inv_power_as_term =  Term::<E>::from_num(Num::Variable(omega_inv_pow));

    let mut minus_one = E::Fr::one();
    minus_one.negate();

    let mut den = point_as_term.mul(cs, &omega_inv_power_as_term)?;
    den.add_constant(&minus_one);

    let domain_size_as_term = Term::<E>::from_num(Num::Variable(domain_size));

    let den = den.mul(cs, &domain_size_as_term)?;

    let den = den.collapse_into_num(cs)?.get_variable();

    numerator.div(cs, &den)
}

pub fn decompose_const_to_bits<E: Engine, F: AsRef<[u64]>>(
    n: F,
) -> Vec<Boolean>
{
    let mut res = Vec::with_capacity(<E::Fr as PrimeField>::NUM_BITS as usize);
    let mut found_one = false;

    for i in BitIterator::new(n) {
        if !found_one {
            found_one = i;
        }
        if found_one {
            res.push(Boolean::constant(i))
        }
    }

    res
}