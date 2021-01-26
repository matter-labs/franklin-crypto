use crate::bellman::pairing::{
    Engine,
    CurveAffine,
    CurveProjective,
};

use crate::bellman::pairing::ff::{
    Field,
    PrimeField,
    PrimeFieldRepr,
    BitIterator,
    ScalarEngine
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
    TrivialAssembly,
    PlonkCsWidth4WithNextStepParams,
};

use crate::circuit::Assignment;

use super::super::allocated_num::{AllocatedNum, Num};
use super::super::linear_combination::LinearCombination;
use super::super::simple_term::Term;
use super::super::boolean::{Boolean, AllocatedBit};

use num_bigint::BigUint;
use num_integer::Integer;

use super::super::bigint::field::*;
use super::super::bigint::bigint::*;

use super::sw_affine;
use super::sw_affine::AffinePoint;

//pub struct Signature<'a, E: Engine, G: CurveAffine> where <G as CurveAffine>::Base: PrimeField {
//    pub s: FieldElement<'a, E, G::Base>,
//    pub r: FieldElement<'a, E, G::Base>,
//}
pub struct Signature<F: PrimeField> {
    pub s: F,
    pub r: F,
}

// pub trait ECDSA<E: Engine>: std::clone::Clone {
pub trait ECDSA<E: Engine, G: CurveAffine, F: PrimeField> {

    fn sign<CS: ConstraintSystem<E>>(
        privkey: FieldElement<E, G>,
        cs: &mut CS,
        message: FieldElement<E, F>,
    ) -> Result<Signature<F>, SynthesisError>;

    fn verify<CS: ConstraintSystem<E>>(
        signature: Signature<F>,
        pubkey: AffinePoint<E, G>,
        cs: &mut CS,
        message: FieldElement<E, F>,
    ) -> Result<(Boolean), SynthesisError>;
}

impl<'a, E: Engine, F: PrimeField, G: CurveAffine> ECDSA<E, G, F> {

    pub fn verify<CS: ConstraintSystem<E>>(
        signature: Signature<F>,
        pubkey: AffinePoint<E, G>,
        cs: &mut CS,
        message: FieldElement<E, F>,
    ) -> Result<(Boolean), SynthesisError> {

        // make a function input?
        let params: RnsParameters<E, F>;

        let sig_s = signature.s;
        // let sig_s= signature.s.clone(); ??
        let sig_r = signature.r;

        // we allocate the signature into circuit elements (variables)
        let s = FieldElement::new_allocated(
            &mut cs,
            Some(sig_s),
            &params
        ).unwrap();
        let r = FieldElement::new_allocated(
            &mut cs,
            Some(sig_r),
            &params
        ).unwrap();

        let pk = pubkey;
        let m = message;

        // we need to do arithmetic mod Fr here
        let (u1, (m, s)) = m.div(&mut cs, s).unwrap();
        let (u2, (r, s)) = r.div(&mut cs, s).unwrap();


        // should make sure that the curve generator is used to set public keys!
        // should use CurveAffine instead of G1Affine ??
        //let gen = CurveAffine::one();
        let gen = E::G1Affine::one();
        let g = AffinePoint::constant(
            gen,
            &params
        );

        // need to convert u1 as field element into num - the following doesn't work
        let u1 = Num::Variable(u1);
        let u2 = Num::Variable(u2);
        let (p1, g) = g.mul(&mut cs, &u1, None).unwrap();
        let (p2, pk) = pk.mul(&mut cs, &u2, None).unwrap();
        let (result, (p1, p2)) = p1.add_unequal(&mut cs, p2).unwrap();

        // we need to check x-coordinate of p1 + p2 equals r
        let (check, _) = FieldElement::equals(cs, result.get_x(), r)?;
        //let (check, _) = FieldElement::equals(cs, result.get_x().clone(), r.clone())?;

        Ok(check)

    }

}
