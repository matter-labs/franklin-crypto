mod tests {
    use super::super::edwards::*;
    use super::super::bn256::*;
    use crate::bellman::plonk::better_better_cs::cs::{
        PlonkCsWidth4WithNextStepAndCustomGatesParams, TrivialAssembly, Width4MainGateWithDNext,
    };
    use crate::bellman::pairing::bn256::{Bn256, Fr};
    use crate::bellman::pairing::ff::BitIterator;
    use crate::alt_babyjubjub::fs::Fs;
    use crate::alt_babyjubjub::AltJubjubBn256;
    use crate::bellman::{Field, PrimeField};
    use crate::jubjub::edwards::Point;
    use crate::plonk::circuit::allocated_num::{AllocatedNum, Num};
    use crate::plonk::circuit::boolean::{AllocatedBit, Boolean};
    use rand::{Rand, SeedableRng, XorShiftRng};

    #[test]
    fn test_new_altjubjub_addition() {
        let rng = &mut XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let mut cs = TrivialAssembly::<
            Bn256,
            PlonkCsWidth4WithNextStepAndCustomGatesParams,
            Width4MainGateWithDNext,
        >::new();

        let params = AltJubjubBn256::new();

        for _ in 0..10 {
            let p = Point::<Bn256, _>::rand(rng, &params).mul_by_cofactor(&params);
            let (p_x, p_y) = p.into_xy();
            let p_x_num = Num::Variable(AllocatedNum::alloc(&mut cs, || Ok(p_x)).unwrap());
            let p_y_num = Num::Variable(AllocatedNum::alloc(&mut cs, || Ok(p_y)).unwrap());
            let p_allocated = CircuitTwistedEdwardsPoint {
                x: p_x_num,
                y: p_y_num,
            };

            let q = Point::<Bn256, _>::rand(rng, &params).mul_by_cofactor(&params);
            let (q_x, q_y) = q.into_xy();
            let q_x_num = Num::Variable(AllocatedNum::alloc(&mut cs, || Ok(q_x)).unwrap());
            let q_y_num = Num::Variable(AllocatedNum::alloc(&mut cs, || Ok(q_y)).unwrap());
            let q_allocated = CircuitTwistedEdwardsPoint {
                x: q_x_num,
                y: q_y_num,
            };

            let expected = p.add(&q, &params);
            let (expected_x, expected_y) = expected.into_xy();

            let curve = CircuitAltBabyJubjubBn256::get_implementor();
            let result = curve.add(&mut cs, &p_allocated, &q_allocated).unwrap();

            assert!(cs.is_satisfied());
            let actual_x = result.x.get_variable().get_value().unwrap();
            let actual_y = result.y.get_variable().get_value().unwrap();

            assert_ne!(actual_x, Fr::zero());
            assert_ne!(actual_y, Fr::zero());

            assert_eq!(actual_x, expected_x);
            assert_eq!(actual_y, expected_y);
        }
        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_new_altjubjub_doubling() {
        let rng = &mut XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let mut cs = TrivialAssembly::<
            Bn256,
            PlonkCsWidth4WithNextStepAndCustomGatesParams,
            Width4MainGateWithDNext,
        >::new();

        let params = AltJubjubBn256::new();

        for _ in 0..10 {
            let p = Point::<Bn256, _>::rand(rng, &params).mul_by_cofactor(&params);
            let (p_x, p_y) = p.into_xy();

            let expected = p.double(&params);
            let (expected_x, expected_y) = expected.into_xy();

            let p_x_num = Num::Variable(AllocatedNum::alloc(&mut cs, || Ok(p_x)).unwrap());
            let p_y_num = Num::Variable(AllocatedNum::alloc(&mut cs, || Ok(p_y)).unwrap());
            let p_allocated = CircuitTwistedEdwardsPoint {
                x: p_x_num,
                y: p_y_num,
            };

            let curve = CircuitAltBabyJubjubBn256::get_implementor();
            let result = curve.double(&mut cs, &p_allocated).unwrap();

            assert!(cs.is_satisfied());

            let actual_x = result.x.get_variable().get_value().unwrap();
            let actual_y = result.y.get_variable().get_value().unwrap();

            assert_ne!(actual_x, Fr::zero());
            assert_ne!(actual_y, Fr::zero());

            assert_eq!(actual_x, expected_x);
            assert_eq!(actual_y, expected_y);
        }
        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_new_altjubjub_multiplication() {
        let rng = &mut XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let mut cs = TrivialAssembly::<
            Bn256,
            PlonkCsWidth4WithNextStepAndCustomGatesParams,
            Width4MainGateWithDNext,
        >::new();

        let params = AltJubjubBn256::new();

        for _ in 0..10 {
            let p = Point::<Bn256, _>::rand(rng, &params).mul_by_cofactor(&params);
            let (p_x, p_y) = p.into_xy();

            let p_x_num = Num::Variable(AllocatedNum::alloc(&mut cs, || Ok(p_x)).unwrap());
            let p_y_num = Num::Variable(AllocatedNum::alloc(&mut cs, || Ok(p_y)).unwrap());
            let p_allocated = CircuitTwistedEdwardsPoint {
                x: p_x_num,
                y: p_y_num,
            };

            let s = Fs::rand(rng);

            let mut s_bits = BitIterator::new(s.into_repr()).collect::<Vec<_>>();
            s_bits.reverse();
            s_bits.truncate(Fs::NUM_BITS as usize);

            let s_bits = s_bits
                .into_iter()
                .enumerate()
                .map(|(_i, b)| AllocatedBit::alloc(&mut cs, Some(b)).unwrap())
                .map(|v| Boolean::from(v))
                .collect::<Vec<_>>();

            let expected = p.mul(s, &params);
            let (expected_x, expected_y) = expected.into_xy();

            let curve = CircuitAltBabyJubjubBn256::get_implementor();
            let result = curve.mul(&mut cs, &p_allocated, &s_bits).unwrap();

            assert!(cs.is_satisfied());

            let actual_x = result.x.get_variable().get_value().unwrap();
            let actual_y = result.y.get_variable().get_value().unwrap();

            assert_ne!(actual_x, Fr::zero());
            assert_ne!(actual_y, Fr::one());

            assert_eq!(actual_x, expected_x);
            assert_eq!(actual_y, expected_y);
        }
        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_new_altjubjub_is_on_curve() {
        let rng = &mut XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let mut cs = TrivialAssembly::<
            Bn256,
            PlonkCsWidth4WithNextStepAndCustomGatesParams,
            Width4MainGateWithDNext,
        >::new();

        let params = AltJubjubBn256::new();

        for _ in 0..10 {
            let p = Point::<Bn256, _>::rand(rng, &params).mul_by_cofactor(&params);

            let (p_x, p_y) = p.into_xy();

            let p_x_num = Num::Variable(AllocatedNum::alloc(&mut cs, || Ok(p_x)).unwrap());
            let p_y_num = Num::Variable(AllocatedNum::alloc(&mut cs, || Ok(p_y)).unwrap());
            let _p_allocated = CircuitTwistedEdwardsPoint {
                x: p_x_num,
                y: p_y_num,
            };

            let curve = CircuitAltBabyJubjubBn256::get_implementor();
            let result = curve.from_xy_assert_on_curve(&mut cs, &p_x_num, &p_y_num).unwrap();

            assert!(cs.is_satisfied());

            let actual_x = result.x.get_variable().get_value().unwrap();
            let actual_y = result.y.get_variable().get_value().unwrap();

            assert_ne!(actual_x, Fr::zero());
            assert_ne!(actual_y, Fr::one());

            assert_eq!(actual_x, p_x);
            assert_eq!(actual_y, p_y);
        }
        // TODO: test with points not on the curve
        // for _ in 0..10 {
        //     let p = Point::<Bn256, _>::rand(rng, &params).mul_by_cofactor(&params);

        //     let (p_x, p_y) = p.into_xy();

        //     let p_x_num = Num::Variable(AllocatedNum::alloc(&mut cs, || Ok(p_x)).unwrap());
        //     let p_y_num = Num::Variable(AllocatedNum::alloc(&mut cs, || Ok(p_y)).unwrap());
        //     let p_allocated = CircuitTwistedEdwardsPoint {
        //         x: p_x_num,
        //         y: p_y_num,
        //     };

        //     let curve = CircuitAltJubjub::new();
        //     let result = curve.is_on_curve(&mut cs, &p_x_num, &p_y_num).unwrap();

        //     assert!(cs.is_satisfied());

        //     let actual_x = result.x.get_variable().get_value().unwrap();
        //     let actual_y = result.y.get_variable().get_value().unwrap();

        //     assert_ne!(actual_x, Fr::zero());
        //     assert_ne!(actual_y, Fr::zero());

        //     assert_eq!(actual_x, p_x);
        //     assert_eq!(actual_y, p_y);
        // }
        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_new_altjubjub_mul_by_generator() {
        use crate::jubjub::{FixedGenerators, JubjubParams};
        let rng = &mut XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let mut cs = TrivialAssembly::<
            Bn256,
            PlonkCsWidth4WithNextStepAndCustomGatesParams,
            Width4MainGateWithDNext,
        >::new();

        let params = AltJubjubBn256::new();

        for _ in 0..1 {
            let s = Fs::rand(rng);

            let generator = params.generator(FixedGenerators::SpendingKeyGenerator);
            let expected = generator.mul(s, &params);
            let (expected_x, expected_y) = expected.into_xy();

            let mut s_bits = BitIterator::new(s.into_repr()).collect::<Vec<_>>();
            s_bits.reverse();
            s_bits.truncate(Fs::NUM_BITS as usize);

            let s_bits = s_bits
                .into_iter()
                .enumerate()
                .map(|(_i, b)| AllocatedBit::alloc(&mut cs, Some(b)).unwrap())
                .map(|v| Boolean::from(v))
                .collect::<Vec<_>>();

            let curve = CircuitAltBabyJubjubBn256::get_implementor();
            let result = curve.mul_by_generator(&mut cs, &s_bits).unwrap();

            let actual_x = result.x.get_variable().get_value().unwrap();
            let actual_y = result.y.get_variable().get_value().unwrap();

            assert!(cs.is_satisfied());

            assert_ne!(actual_x, Fr::zero());
            assert_ne!(actual_y, Fr::zero());

            assert_eq!(actual_x, expected_x);
            assert_eq!(actual_y, expected_y);
        }
        assert!(cs.is_satisfied());
    }
}
