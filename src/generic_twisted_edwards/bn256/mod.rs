use super::edwards::*;

use bellman::pairing::bn256::{Bn256, Fr};
use bellman::pairing::ff::BitIterator;
use bellman::{Engine, Field, PrimeField, PrimeFieldRepr, ScalarEngine, SqrtField};
use rand::{Rand, Rng};
use std::marker::PhantomData;

#[derive(Clone, Debug, Copy)]
pub struct AltBabyJubjubParams {
    curve_params: GenericTwistedEdwardsCurveParams<Bn256>,
}

impl TwistedEdwardsCurveParams<Bn256> for AltBabyJubjubParams {
    type Fs = crate::alt_babyjubjub::fs::Fs;

    fn is_param_a_equals_minus_one(&self) -> bool {
        self.curve_params.is_param_a_equals_minus_one
    }
    fn param_d(&self) -> Fr {
        self.curve_params.param_d
    }
    fn param_a(&self) -> Fr {
        self.curve_params.param_d
    }
    fn generator(&self) -> TwistedEdwardsPoint<Bn256> {
        self.curve_params.generator
    }
    fn log_2_cofactor(&self) -> usize {
        self.curve_params.log_2_cofactor
    }
}

pub struct AltBabyJubjubBn256;
impl AltBabyJubjubBn256 {
    pub fn get_implementor() -> TwistedEdwardsCurveImplementor<Bn256, AltBabyJubjubParams> {
        TwistedEdwardsCurveImplementor::new_from_params(AltBabyJubjubParams::new())
    }
}

impl AltBabyJubjubParams {
    pub fn new() -> Self {
        // d = -(168696/168700)
        let d = <Bn256 as ScalarEngine>::Fr::from_str(
            "12181644023421730124874158521699555681764249180949974110617291017600649128846",
        )
        .expect("field element d");

        let mut a = <Bn256 as ScalarEngine>::Fr::one();
        a.negate();

        let generator_x = <Bn256 as ScalarEngine>::Fr::from_str(
            "21237458262955047976410108958495203094252581401952870797780751629344472264183",
        )
        .expect("field element");

        let generator_y = <Bn256 as ScalarEngine>::Fr::from_str(
            "2544379904535866821506503524998632645451772693132171985463128613946158519479",
        )
        .expect("field element");

        let log_2_cofactor = 3; // h = 8

        let mut generator_t = generator_x.clone();
        generator_t.mul_assign(&generator_y);

        let generator = TwistedEdwardsPoint {
            x: generator_x,
            y: generator_y,
            t: generator_t,
            z: <Bn256 as ScalarEngine>::Fr::one(),
        };
        Self {
            curve_params: GenericTwistedEdwardsCurveParams::new(d, a, generator, log_2_cofactor),
        }
    }
}

#[cfg(test)]
mod tests{
    use super::*;
    use crate::alt_babyjubjub::fs::Fs;
    use rand::{XorShiftRng, SeedableRng};
    use std::time::Instant;    

    #[test]
    fn test_conditonal_select_for_point(){
        let jubjub = AltBabyJubjubBn256::get_implementor();
        
        let p = TwistedEdwardsPoint::<Bn256>::identity();
        let q = jubjub.double(&p);

        let r1 = TwistedEdwardsPoint::conditional_select(0, &p, &q);
        assert_eq!(r1, q);
        let r1 = TwistedEdwardsPoint::conditional_select(1, &p, &q);
        assert_eq!(r1, p);
    }

    #[test]
    fn test_constant_time_mul(){
        let rng = &mut XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let jubjub = AltBabyJubjubBn256::get_implementor();

        for _ in 0..100{
            let p = jubjub.rand(rng);
            let scalar = Fs::rand(rng);
    
            let expected = jubjub.mul(&p, scalar);
    
            let actual = jubjub.ct_mul(&p, scalar);
            assert_ne!(actual, TwistedEdwardsPoint::<Bn256>::identity());
            assert_eq!(expected, actual);
        }
    }

    #[test]
    fn test_constant_time_mul_running_time(){
        let rng = &mut XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let jubjub = AltBabyJubjubBn256::get_implementor();

        for _ in 0..10{
            let p = jubjub.rand(rng);
            let scalar = Fs::rand(rng);
            
            let expected = jubjub.mul(&p, scalar);
            let now = Instant::now();            
            let actual = jubjub.ct_mul(&p, scalar);
            println!("elapsed {}", now.elapsed().as_nanos());
            assert_ne!(actual, TwistedEdwardsPoint::<Bn256>::identity());
            assert_eq!(expected, actual);
        }
    }
}
