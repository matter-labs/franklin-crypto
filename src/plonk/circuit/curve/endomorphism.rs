use crate::bellman::pairing::{
    Engine,
    GenericCurveAffine,
    GenericCurveProjective
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

use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::Num;

use crate::plonk::circuit::bigint::bigint::*;

// we use parameters for decomposition as 
// k = k1 - \lambda * k2
// so affine point is transformed as 
// G1 -> (beta*x, -y) to be multiplied by +k2
#[derive(Clone, Debug)]
pub struct EndomorphismParameters<E: Engine> {
    pub lambda: E::Fr,
    pub beta_g1: <<E as Engine>::G1Affine as GenericCurveAffine>::Base,
    pub a1: BigUint,
    pub a2: BigUint,
    pub minus_b1: BigUint,
    pub b2: BigUint,
    pub scalar_width: usize,
    pub target_scalar_width: usize,
}

impl <E: Engine> EndomorphismParameters<E>  {
    pub fn calculate_decomposition(&self, val: E::Fr) -> (E::Fr, E::Fr) {
        // fast variant
        let value = repr_to_biguint::<E::Fr>(&val.into_repr());

        // here we take high limbs
        let c1 = (&value * &self.a1) >> self.scalar_width;
        let c2 = (&value * &self.a2) >> self.scalar_width;

        let q1 = c1 * &self.minus_b1;
        let q2 = c2 * &self.b2;

        // this will take lowest limbs only
        let q1 = biguint_to_repr::<E::Fr>(q1);
        let q2 = biguint_to_repr::<E::Fr>(q2);
        let q1 = E::Fr::from_repr(q1).unwrap();
        let q2 = E::Fr::from_repr(q2).unwrap();

        // k1
        let mut k2 = q2;
        k2.sub_assign(&q1);

        // k1 = k2 * lambda + val
        let mut k1 = k2;
        k1.mul_assign(&self.lambda);
        k1.add_assign(&val);

        (k1, k2)
    }

    pub fn apply_to_g1_point(&self, point: E::G1Affine) -> E::G1Affine {
        let (mut x, mut y) = point.into_xy_unchecked();
        y.negate();
        x.mul_assign(&self.beta_g1);

        debug_assert!(E::G1Affine::from_xy_checked(x, y).is_ok());

        E::G1Affine::from_xy_unchecked(x, y)
    }
}

pub fn bn254_endomorphism_parameters() -> EndomorphismParameters<crate::bellman::pairing::bn256::Bn256> {
    let empty_fr_repr = crate::bellman::pairing::bn256::Fr::zero().into_repr();
    let mut lambda_repr = empty_fr_repr;
    lambda_repr.as_mut()[0] = 0x93e7cede4a0329b3;
    lambda_repr.as_mut()[1] = 0x7d4fdca77a96c167;
    lambda_repr.as_mut()[2] = 0x8be4ba08b19a750a;
    lambda_repr.as_mut()[3] = 0x1cbd5653a5661c25;
    let lambda = crate::bellman::pairing::bn256::Fr::from_raw_repr(lambda_repr).unwrap();

    let mut may_be_one = lambda;
    may_be_one.mul_assign(&lambda);
    may_be_one.mul_assign(&lambda);
    assert_eq!(may_be_one, crate::bellman::pairing::bn256::Fr::one());

    let empty_fq_repr = crate::bellman::pairing::bn256::Fq::zero().into_repr();
    let mut beta_g1_repr = empty_fq_repr;
    beta_g1_repr.as_mut()[0] = 0x71930c11d782e155;
    beta_g1_repr.as_mut()[1] = 0xa6bb947cffbe3323;
    beta_g1_repr.as_mut()[2] = 0xaa303344d4741444;
    beta_g1_repr.as_mut()[3] = 0x2c3b3f0d26594943;
    let beta_g1 = crate::bellman::pairing::bn256::Fq::from_raw_repr(beta_g1_repr).unwrap();

    let mut may_be_one = beta_g1;
    may_be_one.mul_assign(&beta_g1);
    may_be_one.mul_assign(&beta_g1);
    assert_eq!(may_be_one, crate::bellman::pairing::bn256::Fq::one());

    EndomorphismParameters::<crate::bellman::pairing::bn256::Bn256> {
        lambda: lambda,
        beta_g1: beta_g1,
        a1: BigUint::from_str_radix("2d91d232ec7e0b3d7", 16).unwrap(),
        a2: BigUint::from_str_radix("24ccef014a773d2cf7a7bd9d4391eb18d", 16).unwrap(),
        minus_b1: BigUint::from_str_radix("6f4d8248eeb859fc8211bbeb7d4f1128", 16).unwrap(),
        b2: BigUint::from_str_radix("89d3256894d213e3", 16).unwrap(),
        scalar_width: 256,
        target_scalar_width: 127
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::bellman::pairing::*;

    // #[test]
    // fn test_bn254_params() {
    //     use crate::bellman::pairing::bn256::{Fq, Bn256, Fr};

    //     use rand::{XorShiftRng, SeedableRng, Rng};
    //     let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    //     let params = bn254_endomorphism_parameters();

    //     for _ in 0..1000 {
    //         let scalar: Fr = rng.gen();
    //         let point: <Bn256 as Engine>::G1Affine = rng.gen();

    //         let naive_mul = point.mul(scalar.into_repr()).into_affine();

    //         let (k1, k2) = params.calculate_decomposition(scalar);

    //         // k = k1 - \lambda * k2
    //         let mut reconstruction = k2;
    //         reconstruction.mul_assign(&params.lambda);
    //         reconstruction.negate();
    //         reconstruction.add_assign(&k1);

    //         assert_eq!(reconstruction, scalar);

    //         let k1_bits = k1.into_repr().num_bits();
    //         assert!(k1_bits <= params.target_scalar_width as u32);
    //         let k2_bits = k2.into_repr().num_bits();
    //         assert!(k2_bits <= params.target_scalar_width as u32);
    
    //         let endo_point = params.apply_to_g1_point(point);

    //         let k1_by_point = point.mul(k1.into_repr());
    //         let k2_by_point_endo = endo_point.mul(k2.into_repr());

    //         let mut result = k1_by_point;
    //         result.add_assign(&k2_by_point_endo);

    //         let result = result.into_affine();

    //         assert_eq!(result, naive_mul);
    //     }
    // }
}