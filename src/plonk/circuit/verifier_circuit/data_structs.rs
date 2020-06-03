use crate::plonk::circuit::curve::sw_affine::AffinePoint;
use crate::plonk::circuit::bigint::field::*;
use crate::plonk::circuit::allocated_num::*;
use crate::plonk::circuit::boolean::*;

use crate::bellman::pairing::{
    Engine,
    CurveAffine,
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

use crate::bellman::plonk::better_cs::cs::PlonkConstraintSystemParams;
use crate::bellman::plonk::better_cs::keys::{Proof, VerificationKey};


pub trait AuxData<E: Engine>
{
    fn get_b(&self) -> <E::G1Affine as CurveAffine>::Base;
    fn get_group_order(&self) -> &[u64];
}

// x_{m+n} = Q_{m+n}[x] = -4b z_m * z_n * (x_m*z_n + x_n*z_m) + (x_m * x_n)^2
// z_{m+n} = Q_{m+n}[z] = x * (x_m * z_n - x_n * z_m)^2

fn add<'b, E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS, 
    x_m: &mut FieldElement<'b, E, <E::G1Affine as CurveAffine>::Base>, 
    z_m: &mut FieldElement<'b, E, <E::G1Affine as CurveAffine>::Base>, 
    x_n: &mut FieldElement<'b, E, <E::G1Affine as CurveAffine>::Base>,
    z_n: &mut FieldElement<'b, E, <E::G1Affine as CurveAffine>::Base>,
    x: &FieldElement<'b, E, <E::G1Affine as CurveAffine>::Base>,

    params: &'b RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
    b: &<E::G1Affine as CurveAffine>::Base, 
) -> Result<(FieldElement<'b, E, <E::G1Affine as CurveAffine>::Base>, 
            FieldElement<'b, E, <E::G1Affine as CurveAffine>::Base>), SynthesisError> 
{ 
    let (x_m_z_n, (red_x_m, red_z_n)) = x_m.mul(cs, *z_n)?;
    *x_m = red_x_m;
    *z_n = red_z_n;

    let (x_n_z_m, (red_x_n, red_z_m)) = x_n.mul(cs, *z_m)?;
    *x_n = red_x_n;
    *z_m = red_z_m;

    let x_m_x_n = x_m.mul(cs, *x_n)?.0;
    let z_m_z_n = z_m.mul(cs, *z_n)?.0;

    let mut cnst = <<E::G1Affine as CurveAffine>::Base>::one();
    cnst.double();
    cnst.double();
    cnst.negate();
    cnst.mul_assign(b);

    let mut temp1 = FieldElement::new_constant(cnst, params);
    temp1 = temp1.mul(cs, z_m_z_n)?.0;

    let mut temp2 = x_m_z_n.add(cs, x_n_z_m)?.0;
    temp1 = temp1.mul(cs, temp2)?.0;

    temp2 = x_m_x_n.square(cs)?.0;
    let res_x = temp1.add(cs, temp2)?.0;

    temp1 = x_m_z_n.sub(cs, x_n_z_m)?.0;
    temp1 = temp1.square(cs)?.0;
    let res_z = temp1.mul(cs, *x)?.0;

    Ok((res_x, res_z))
}

// x_{2n} = x_n * [(x^n)^3 - 8 * b * (z_n)^3]
// z_{2n} = 4*z_n*[(x_n)^3 + b * (z_n)^3]

fn double<'b, E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS, 
    x_n: &mut FieldElement<'b, E, <E::G1Affine as CurveAffine>::Base>, 
    z_n: &mut FieldElement<'b, E, <E::G1Affine as CurveAffine>::Base>, 

    params: &'b RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
    b: &<E::G1Affine as CurveAffine>::Base, 
) -> Result<(FieldElement<'b, E, <E::G1Affine as CurveAffine>::Base>, 
            FieldElement<'b, E, <E::G1Affine as CurveAffine>::Base>), SynthesisError> 
{ 
    let (x_n_2, x_n_red) = x_n.square(cs)?;
    let (z_n_2, z_n_red) = z_n.square(cs)?;
    *x_n = x_n_red.clone();
    *z_n = z_n_red.clone();

    let x_n_3 = x_n_2.mul(cs, *x_n)?.0;
    let z_n_3 = z_n_2.mul(cs, *z_n)?.0;

    let mut cnst = <<E::G1Affine as CurveAffine>::Base>::one();
    cnst.double();
    cnst.double();
    let cnst_4 = FieldElement::new_constant(cnst, params);
    cnst.double();
    cnst.mul_assign(b);
    let cnst_8_b = FieldElement::new_constant(cnst, params);
    let cnst_b = FieldElement::new_constant(*b, params);

    let mut temp1 = z_n_3.mul(cs, cnst_8_b)?.0;
    temp1 = x_n_3.sub(cs, temp1)?.0;
    let res_x = x_n.mul(cs, temp1)?.0;

    temp1 = z_n_3.mul(cs, cnst_b)?.0;
    temp1 = x_n_3.add(cs, temp1)?.0;
    let temp2 = z_n.mul(cs, cnst_4)?.0;
    let res_z = temp1.mul(cs, temp2)?.0;
    
    Ok((res_x, res_z))
}


#[derive(Clone, Debug)]
pub struct WrappedAffinePoint<'a, E: Engine> {
    pub is_zero: Boolean,
    pub point: AffinePoint<'a, E, E::G1Affine>,
}

impl<'a, E: Engine> WrappedAffinePoint<'a, E> {

    pub fn alloc<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        value: Option<E::G1Affine>,
        params: &'a RnsParameters<E, <E::G1Affine as CurveAffine>::Base>
    ) -> Result<Self, SynthesisError> 
    {
        let point = AffinePoint::alloc(cs, value, params)?;
        let is_zero = Boolean::and(cs, &point.x.is_zero(cs)?, &point.y.is_zero(cs)?)?;

        Ok( WrappedAffinePoint {
            is_zero,
            point,
        }) 
    }

    pub fn zero(
        params: &'a RnsParameters<E, <E::G1Affine as CurveAffine>::Base>
    ) -> Self
    {
        let is_zero = Boolean::constant(true);
        let point = AffinePoint::constant(E::G1Affine::zero(), params);
        
        WrappedAffinePoint {
            is_zero,
            point,
        }
    }

    pub fn add<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        other: &mut Self,
        params: &'a RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
    ) -> Result<Self, SynthesisError> {
        
        // assume we have points A with coordinates (x_1, y_1) and point B with cooridnates (x_2, y_2)
        // B == 0 --- (true) ----- res = A
        //        |
        //     (false)
        //        |
        //      A == 0 ---(true)----- res = B
        //        |
        //     (false)
        //        |
        //    x_1 == x_2 ----(true)--- y1 == y2 ---(true)--- res = double(A)
        //        |                        |
        //     (false)                  (false)
        //        |                        |
        //    res = add(A, B)            res = O
        //
        // we are going to construct this selection tree from backwards

        // also our group is odd, so doubling on nonzero point is never zero
        // res.is_zero = (A.is_zero && B.iz_zero) || (x_1 == x_2 & y_1 != y_2)

        let x_equality_flag = self.point.x.equals(cs, &other.point.x)?;      
        let y_equality_flag = self.point.y.equals(cs, &other.point.y)?;    
        
        let double_A_point = self.point.double(cs)?;
        self.point = double_A_point.1;
        let zero = AffinePoint::zero(params);
        let mut temp = AffinePoint::select(cs, &y_equality_flag, double_A_point.0, zero)?;

        let add_A_B_point = self.point.add_unequal(cs, other.point)?;
        self.point = (add_A_B_point.1).0;
        other.point = (add_A_B_point.1).1;
        temp = AffinePoint::select(cs, &x_equality_flag, temp, add_A_B_point.0)?;

        temp = AffinePoint::select(cs, &self.is_zero, other.point, temp)?;
        temp = AffinePoint::select(cs, &other.is_zero, self.point, temp)?;
                             
        let flag_cond1 = Boolean::and(cs, &self.is_zero, &other.is_zero)?;
        let flag_cond2 = Boolean::and(cs, &x_equality_flag, &y_equality_flag.not())?;
        let zero_flag = Boolean::or(cs, &flag_cond1, &flag_cond2)?;

        Ok(WrappedAffinePoint {
            is_zero: zero_flag,
            point: temp,
        })
    }

    // pub fn sub<CS: ConstraintSystem<E>>(
    //     &mut self,
    //     cs: &mut CS,
    //     other: &mut Self,
    //     params: &'a RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
    // ) -> Result<Self, SynthesisError> {

    //     // assume we have points A with coordinates (x_1, y_1) and point B with cooridnates (x_2, y_2)
    //     // B == 0 --- (true) ----- res = A
    //     //        |
    //     //     (false)
    //     //        |
    //     //      A == 0 ---(true)----- res = -B
    //     //        |
    //     //     (false)
    //     //        |
    //     //    x_1 == x_2 ----(true)--- y1 == y2 ---(true)--- res = O
    //     //        |                        |
    //     //     (false)                  (false)
    //     //        |                        |
    //     //    res = sub(A, B)            res = double(A)
    //     //
    //     // we are going to construct this selection tree from backwards

    //     // also our group is odd, so doubling on nonzero point is never zero
    //     // res.is_zero = (A.is_zero && B.iz_zero) || (x_1 == x_2 & y_1 == y_2)

    //     let x_equality_flag = self.point.x.equals(cs, &other.point.x)?;      
    //     let y_equality_flag = self.point.y.equals(cs, &other.point.y)?;    
        
    //     let double_A_point = self.point.double(cs)?;
    //     self.point = double_A_point.1;
    //     let zero = AffinePoint::zero(params);
    //     let mut temp = AffinePoint::select(cs, &y_equality_flag, zero, double_A_point.0)?;

    //     let sub_A_B_point = self.point.sub_unequal(cs, other.point)?;
    //     self.point = (sub_A_B_point.1).0;
    //     other.point = (sub_A_B_point.1).1;
    //     temp = AffinePoint::select(cs, &x_equality_flag, temp, sub_A_B_point.0)?;

    //     temp = AffinePoint::select(cs, &self.is_zero, other.point.negate(cs)?, temp)?;
    //     temp = AffinePoint::select(cs, &other.is_zero, self.point, temp)?;
                             
    //     let flag_cond1 = Boolean::and(cs, &self.is_zero, &other.is_zero)?;
    //     let flag_cond2 = Boolean::and(cs, &x_equality_flag, &y_equality_flag)?;
    //     let zero_flag = Boolean::or(cs, &flag_cond1, &flag_cond2)?;

    //     Ok(WrappedAffinePoint {
    //         is_zero: zero_flag,
    //         point: temp,
    //     })
    // }

    // pub fn double<CS: ConstraintSystem<E>>(
    //     &mut self,
    //     cs: &mut CS,
    //     _params: &'a RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
    // ) -> Result<Self, SynthesisError> {
        
    //     //  A == O ----(true)---- A
    //     //    |
    //     //    |--------(false)--- double(A)


    //     let doubled = self.point.double(cs)?;
    //     self.point = doubled.1;

    //     let res_point = AffinePoint::select(cs, &self.is_zero, self.point, doubled.0)?;
    //     let res_flag = self.is_zero;

    //     Ok(WrappedAffinePoint {
    //         is_zero: res_flag,
    //         point: res_point,
    //     })
    // }

    // pub fn is_on_curve<CS: ConstraintSystem<E>, AD: AuxData<E>>(
    //     &self,
    //     cs: &mut CS,
    //     params: &RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
    //     aux_data: &AD,
    // ) -> Result<Boolean, SynthesisError> {

    //     // either the point is zero, or satisfies the equation y^2 = x^3+b
    //     let lhs = self.point.y.square(cs)?.0;
    //     let (mut rhs, reduced_x) = self.point.x.square(cs)?;
    //     rhs = rhs.mul(cs, reduced_x)?.0;

    //     let b = FieldElement::new_constant(aux_data.get_b(), params);
    //     rhs = rhs.add(cs, b)?.0;

    //     let eq_flag = lhs.equals(cs, &rhs)?;
    //     let is_on_curve = Boolean::or(cs, &self.is_zero, &eq_flag);

    //     is_on_curve
    // }

    pub fn subgroup_check<CS: ConstraintSystem<E>, AD: AuxData<E>>(
        &self,
        cs: &mut CS,
        params: &'a RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
        aux_data: &AD,
    ) -> Result<Boolean, SynthesisError> {
        
        // we use tricks from section 13.2.3.b and 13.2.3.d of "Handbook of Elliptic and Hyperelliptic Curve Cryptography"
        // more precisely, there is Montgomey trick that allows us to compute x and z coordinate of nP, 
        // given projective representation of P
        // the formulas in our case are even more simplified due to the fact than intial point P is affine and a = 0

        // if Q_m = (x_m, y_m, z_m), Q_n = (x_n, y_n, z_n), and Q_m - Q_n = Q_1 = P = (x, y, 1), then 
        // x_{m+n} = Q_{m+n}[x] = -4b z_m * z_n * (x_m*z_n + x_n*z_m) + (x_m * x_n)^2
        // z_{m+n} = Q_{m+n}[z] = x * (x_m * z_n - x_n * z_m)^2

        
        

        // Scalar multiplication using Montgomery’s ladder
        // INPUT: A point P on elliptic curve E and a positive integer n = (n_l...n_0) (binary decomposition of n: n_l = 1).
        // OUTPUT: The point [n]P.
        // 1. P_1 = P and P_2 = [2]P
        // 2. for i = l − 1 down to 0 do
        // 3. if n_i = 0 then
        //      P_1 = [2]P_1 and P_2 = P_1 ⊕ P_2
        //    else
        //      P_1 = P_1 ⊕ P_2 and P_2 ← [2]P_2
        // 7. return P_1

        // NB: We can check that P2-P1 (or P1-P2 correspondingly) is equal to P at each step

        let mut P_1_x = self.point.x.clone();
        let mut P_1_z = FieldElement::one(params);
        let mut P_2_x = self.point.double(cs)?.0.x;
        let mut P_2_z = FieldElement::one(params);

        let mut found_one = false;
        let exp = aux_data.get_group_order();
        let b = aux_data.get_b();

        for i in BitIterator::new(exp) {
            if found_one {

                if i {
                    // calcilate [2]P_2
                    let (P_2_doubled_x, P_2_doubled_z) = double(cs, &mut P_2_x, &mut P_2_z, params, &b)?;
                    // calculate P_1 ⊕ P_2
                    let (P_1_2_x, P_1_2_z) = add(cs, &mut P_1_x, &mut P_1_z, &mut P_2_x, &mut P_2_z, 
                        &mut self.point.x.clone(), params, &b)?;

                    P_1_x = P_1_2_x;
                    P_1_z = P_1_2_z;

                    P_2_x = P_2_doubled_x;
                    P_2_z = P_2_doubled_z;
                }
                else {
                    // calcilate [2]P_1
                    let (P_1_doubled_x, P_1_doubled_z) = double(cs, &mut P_1_x, &mut P_1_z, params, &b)?;
                    // calculate P_1 ⊕ P_2
                    let (P_1_2_x, P_1_2_z) = add(cs, &mut P_1_x, &mut P_1_z, &mut P_2_x, &mut P_2_z, 
                        &mut self.point.x.clone(), params, &b)?;

                    P_2_x = P_1_2_x;
                    P_2_z = P_1_2_z;

                    P_1_x = P_1_doubled_x;
                    P_1_z = P_1_doubled_z;
                }
                
                
                

            } else {
                found_one = i;
            }
        }

        // the point is in subgroup if any of the following holds: 
        // 1) the point was zero from the start 
        // 2) the point is zero at the end i.e. P_1_x = P_1_z = 0
        
        let temp_flag = Boolean::and(cs, &P_1_x.is_zero(cs)?, &P_1_z.is_zero(cs)?)?;
        let subgroup_check = Boolean::or(cs, &temp_flag, &self.is_zero);
        
        subgroup_check
    }
}


#[derive(Clone, Debug)]
pub struct ProofGadget<'a, E: Engine> {
    pub num_inputs: usize,
    pub n: usize,
    pub input_values: Vec<AllocatedNum<E>>,
    pub wire_commitments: Vec<AffinePoint<'a, E, E::G1Affine>>,
    pub grand_product_commitment: AffinePoint<'a, E, E::G1Affine>,
    pub quotient_poly_commitments: Vec<AffinePoint<'a, E, E::G1Affine>>,

    pub wire_values_at_z: Vec<AllocatedNum<E>>,
    pub wire_values_at_z_omega: Vec<AllocatedNum<E>>,
    pub grand_product_at_z_omega: AllocatedNum<E>,
    pub quotient_polynomial_at_z: AllocatedNum<E>,
    pub linearization_polynomial_at_z: AllocatedNum<E>,
    pub permutation_polynomials_at_z: Vec<AllocatedNum<E>>,

    pub opening_at_z_proof: AffinePoint<'a, E, E::G1Affine>,
    pub opening_at_z_omega_proof: AffinePoint<'a, E, E::G1Affine>,
}


impl<'a, E: Engine> ProofGadget<'a, E> {
    
    pub fn alloc<CS: ConstraintSystem<E>, P: PlonkConstraintSystemParams<E>>(
        cs: &mut CS,
        proof: Proof<E, P>,
        params: &'a RnsParameters<E, <E::G1Affine as CurveAffine>::Base>
    ) -> Result<Self, SynthesisError> {

        let input_values = proof.input_values.iter().map(|x| {
            AllocatedNum::alloc_input(cs, || Ok(*x))
        }).collect::<Result<Vec<_>, _>>()?;

        let wire_commitments = proof.wire_commitments.iter().map(|x| {
            AffinePoint::alloc(cs, Some(*x), params)
        }).collect::<Result<Vec<_>, _>>()?;

        let grand_product_commitment = AffinePoint::alloc(cs, Some(proof.grand_product_commitment), params)?;
        
        let quotient_poly_commitments = proof.quotient_poly_commitments.iter().map(|x| {
            AffinePoint::alloc(cs, Some(*x), params)
        }).collect::<Result<Vec<_>, _>>()?;

        let wire_values_at_z = proof.wire_values_at_z.iter().map(|x| {
            AllocatedNum::alloc(cs, || Ok(*x))
        }).collect::<Result<Vec<_>, _>>()?;

        let wire_values_at_z_omega = proof.wire_values_at_z_omega.iter().map(|x| {
            AllocatedNum::alloc(cs, || Ok(*x))
        }).collect::<Result<Vec<_>, _>>()?;

        let grand_product_at_z_omega = AllocatedNum::alloc(cs, || Ok(proof.grand_product_at_z_omega))?; 
        let quotient_polynomial_at_z = AllocatedNum::alloc(cs, || Ok(proof.quotient_polynomial_at_z))?; 
        let linearization_polynomial_at_z = AllocatedNum::alloc(cs, || Ok(proof.linearization_polynomial_at_z))?;  

        let permutation_polynomials_at_z = proof.permutation_polynomials_at_z.iter().map(|x| {
            AllocatedNum::alloc(cs, || Ok(*x))
        }).collect::<Result<Vec<_>, _>>()?;

        let opening_at_z_proof = AffinePoint::alloc(cs, Some(proof.opening_at_z_proof), params)?;
        let opening_at_z_omega_proof = AffinePoint::alloc(cs, Some(proof.opening_at_z_omega_proof), params)?;
       
        Ok(ProofGadget {
            num_inputs: proof.num_inputs,
            n: proof.n,
            input_values,
            wire_commitments,
            grand_product_commitment,
            quotient_poly_commitments,

            wire_values_at_z,
            wire_values_at_z_omega,
            grand_product_at_z_omega,
            quotient_polynomial_at_z,
            linearization_polynomial_at_z,
            permutation_polynomials_at_z,

            opening_at_z_proof,
            opening_at_z_omega_proof,
        })
    }
}


#[derive(Clone, Debug)]
pub struct VerificationKeyGagdet<'a, E: Engine> {
    pub n: usize,
    pub num_inputs: usize,
    pub selector_commitments: Vec<AffinePoint<'a, E, E::G1Affine>>,
    pub next_step_selector_commitments: Vec<AffinePoint<'a, E, E::G1Affine>>,
    pub permutation_commitments: Vec<AffinePoint<'a, E, E::G1Affine>>,
    pub non_residues: Vec<E::Fr>,
}


impl<'a, E: Engine> VerificationKeyGagdet<'a, E> {
    
    pub fn alloc<CS: ConstraintSystem<E>, P: PlonkConstraintSystemParams<E>>(
        cs: &mut CS,
        vk:  VerificationKey<E, P>,
        params: &'a RnsParameters<E, <E::G1Affine as CurveAffine>::Base>
    ) -> Result<Self, SynthesisError> {

        let selector_commitments = vk.selector_commitments.iter().map(|x| {
            AffinePoint::alloc(cs, Some(*x), params)
        }).collect::<Result<Vec<_>, _>>()?;

        let next_step_selector_commitments = vk.next_step_selector_commitments.iter().map(|x| {
            AffinePoint::alloc(cs, Some(*x), params)
        }).collect::<Result<Vec<_>, _>>()?;

        let permutation_commitments = vk.permutation_commitments.iter().map(|x| {
            AffinePoint::alloc(cs, Some(*x), params)
        }).collect::<Result<Vec<_>, _>>()?;

        Ok(VerificationKeyGagdet {
            n : vk.n,
            num_inputs : vk.num_inputs,
            selector_commitments,
            next_step_selector_commitments,
            permutation_commitments,
            non_residues: vk.non_residues,
        })
    }
}
        