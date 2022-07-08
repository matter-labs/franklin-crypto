mod test {
    use super::*;
    use crate::alt_babyjubjub::edwards::Point;
    use crate::alt_babyjubjub::fs::Fs;
    use crate::alt_babyjubjub::AltJubjubBn256;
    use crate::bellman::pairing::bn256::{Bn256, Fr};
    use crate::generic_twisted_edwards::bn256::*;
    use crate::generic_twisted_edwards::edwards::*;
    use bellman::ScalarEngine;
    use rand::{Rand, Rng, SeedableRng, XorShiftRng};

    #[test]
    fn test_new_edwards_addition() {
        let rng = &mut XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let jubjub = AltBabyJubjubBn256::get_implementor();
        let jubjub_params = AltJubjubBn256::new();

        for _ in 0..10 {
            let p = jubjub.rand(rng);
            let (p_x, p_y) = p.into_xy();
            let q = jubjub.rand(rng);
            let (q_x, q_y) = q.into_xy();

            let (expected_x, expected_y) = {
                let p = Point::<Bn256, _>::from_xy(p_x, p_y, &jubjub_params).expect("a point");
                let q = Point::from_xy(q_x, q_y, &jubjub_params).expect("a point");

                let expected = p.add(&q, &jubjub_params);

                let (x, y) = expected.into_xy();

                let expected_x: <Bn256 as ScalarEngine>::Fr = x;
                let expected_y: <Bn256 as ScalarEngine>::Fr = y;

                (expected_x, expected_y)
            };

            let (actual_x, actual_y) = jubjub.add(&p, &q).into_xy();

            assert_eq!(expected_x, actual_x);
            assert_eq!(expected_y, actual_y);
        }
    }

    #[test]
    fn test_new_edwards_doubling() {
        let rng = &mut XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let jubjub = AltBabyJubjubBn256::get_implementor();
        let jubjub_params = AltJubjubBn256::new();

        for _ in 0..10 {
            let p = jubjub.rand(rng);
            let (p_x, p_y) = p.into_xy();

            let (expected_x, expected_y) = {
                let p = Point::<Bn256, _>::from_xy(p_x, p_y, &jubjub_params).expect("a point");

                let expected = p.double(&jubjub_params);

                let (x, y) = expected.into_xy();

                let expected_x: <Bn256 as ScalarEngine>::Fr = x;
                let expected_y: <Bn256 as ScalarEngine>::Fr = y;

                (expected_x, expected_y)
            };

            let (actual_x, actual_y) = jubjub.double(&p).into_xy();

            assert_eq!(expected_x, actual_x);
            assert_eq!(expected_y, actual_y);
        }
    }

    #[test]
    fn test_new_edwards_mul_scalar() {
        let rng = &mut XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let jubjub = AltBabyJubjubBn256::get_implementor();
        let jubjub_params = AltJubjubBn256::new();

        for _ in 0..10 {
            let p = jubjub.rand(rng);
            let (p_x, p_y) = p.into_xy();

            let scalar = Fs::rand(rng);

            let (expected_x, expected_y) = {
                let p = Point::<Bn256, _>::from_xy(p_x, p_y, &jubjub_params).expect("a point");

                let expected = p.mul(scalar, &jubjub_params);

                let (x, y) = expected.into_xy();

                let expected_x: <Bn256 as ScalarEngine>::Fr = x;
                let expected_y: <Bn256 as ScalarEngine>::Fr = y;

                (expected_x, expected_y)
            };

            let (actual_x, actual_y) = jubjub.mul(&p, scalar).into_xy();

            assert_eq!(expected_x, actual_x);
            assert_eq!(expected_y, actual_y);
        }
    }

    #[test]
    fn test_new_edwards_negate() {
        let rng = &mut XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let jubjub = AltBabyJubjubBn256::get_implementor();
        let jubjub_params = AltJubjubBn256::new();

        for _ in 0..10 {
            let p = jubjub.rand(rng);
            let (p_x, p_y) = p.into_xy();

            let p_negate = jubjub.negate(&p);
            let (actual_x, actual_y) = p_negate.into_xy();

            let (expected_x, expected_y) = {
                let p = Point::<Bn256, _>::from_xy(p_x, p_y, &jubjub_params).expect("a point");

                let expected = p.negate();

                let (x, y) = expected.into_xy();

                let expected_x: <Bn256 as ScalarEngine>::Fr = x;
                let expected_y: <Bn256 as ScalarEngine>::Fr = y;

                (expected_x, expected_y)
            };

            assert_eq!(actual_x, expected_x);
            assert_eq!(actual_y, expected_y);
        }
    }
}
