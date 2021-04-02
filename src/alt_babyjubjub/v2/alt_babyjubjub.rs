use crate::alt_babyjubjub::v2::edwards::{
    TwistedEdwardsCurve, TwistedEdwardsPoint, TwisterEdwardsCurveParams,
};
use bellman::pairing::bn256::Bn256;
use bellman::pairing::ff::BitIterator;
use bellman::{Engine, Field, PrimeField, PrimeFieldRepr, ScalarEngine, SqrtField};
use rand::{Rand, Rng};
use std::marker::PhantomData;

#[derive(Clone, Debug)]
pub struct AltJubjub {
    curve_params: TwisterEdwardsCurveParams<Bn256>,
}

impl TwistedEdwardsCurve<Bn256> for AltJubjub {
    type Fs = crate::alt_babyjubjub::fs::Fs;

    fn add(
        &self,
        p: &TwistedEdwardsPoint<Bn256>,
        q: &TwistedEdwardsPoint<Bn256>,
    ) -> TwistedEdwardsPoint<Bn256> {
        // See "Twisted Edwards Curves Revisited"
        //     Huseyin Hisil, Kenneth Koon-Ho Wong, Gary Carter, and Ed Dawson
        //     3.1 Unified Addition in E^e

        // A = x1 * x2
        let mut a = p.x;
        a.mul_assign(&q.x);

        // B = y1 * y2
        let mut b = p.y;
        b.mul_assign(&q.y);

        // C = d * t1 * t2
        let mut c = self.curve_params.param_d.clone();
        c.mul_assign(&p.t);
        c.mul_assign(&q.t);

        // D = z1 * z2
        let mut d = p.z;
        d.mul_assign(&q.z);

        let h = if self.curve_params.is_param_a_equals_minus_one {
            // H = B + A
            let mut h = b;
            h.add_assign(&a);
            h
        } else {
            // H = B - aA
            let mut h = a.clone();
            h.mul_assign(&self.curve_params.param_a);
            h.negate();
            h.add_assign(&b);
            h
        };

        // E = (x1 + y1) * (x2 + y2) - A - B
        //   = (x1 + y1) * (x2 + y2) - H
        let mut e = p.x;
        e.add_assign(&p.y);
        {
            let mut tmp = q.x;
            tmp.add_assign(&q.y);
            e.mul_assign(&tmp);
        }
        e.sub_assign(&h);

        // F = D - C
        let mut f = d;
        f.sub_assign(&c);

        // G = D + C
        let mut g = d;
        g.add_assign(&c);

        // x3 = E * F
        let mut x3 = e;
        x3.mul_assign(&f);

        // y3 = G * H
        let mut y3 = g;
        y3.mul_assign(&h);

        // t3 = E * H
        let mut t3 = e;
        t3.mul_assign(&h);

        // z3 = F * G
        let mut z3 = f;
        z3.mul_assign(&g);

        TwistedEdwardsPoint {
            x: x3,
            y: y3,
            t: t3,
            z: z3,
        }
    }

    fn double(&self, p: &TwistedEdwardsPoint<Bn256>) -> TwistedEdwardsPoint<Bn256> {
        // See "Twisted Edwards Curves Revisited"
        //     Huseyin Hisil, Kenneth Koon-Ho Wong, Gary Carter, and Ed Dawson
        //     Section 3.3
        //     http://hyperelliptic.org/EFD/g1p/auto-twisted-extended.html#doubling-dbl-2008-hwcd

        // A = X1^2
        let mut a = p.x;
        a.square();

        // B = Y1^2
        let mut b = p.y;
        b.square();

        // C = 2*Z1^2
        let mut c = p.z;
        c.square();
        c.double();

        // D = a*A
        //   = -A
        let mut d = a;
        d.negate();

        // E = (X1+Y1)^2 - A - B
        let mut e = p.x;
        e.add_assign(&p.y);
        e.square();
        e.add_assign(&d); // -A = D
        e.sub_assign(&b);

        // G = D+B
        let mut g = d;
        g.add_assign(&b);

        // F = G-C
        let mut f = g;
        f.sub_assign(&c);

        // H = D-B
        let mut h = d;
        h.sub_assign(&b);

        // X3 = E*F
        let mut x3 = e;
        x3.mul_assign(&f);

        // Y3 = G*H
        let mut y3 = g;
        y3.mul_assign(&h);

        // T3 = E*H
        let mut t3 = e;
        t3.mul_assign(&h);

        // Z3 = F*G
        let mut z3 = f;
        z3.mul_assign(&g);

        TwistedEdwardsPoint {
            x: x3,
            y: y3,
            t: t3,
            z: z3,
        }
    }

    fn mul<S: Into<<Self::Fs as PrimeField>::Repr>>(
        &self,
        p: &TwistedEdwardsPoint<Bn256>,
        scalar: S,
    ) -> TwistedEdwardsPoint<Bn256> {
        // Standard double-and-add scalar multiplication

        let mut res = TwistedEdwardsPoint::identity();

        for b in BitIterator::new(scalar.into()) {
            res = self.double(&res);

            if b {
                res = self.add(&p, &res);
            }
        }

        res
    }

    fn ct_mul(
        &self,
        p: &TwistedEdwardsPoint<Bn256>,
        scalar: Self::Fs,
    ) -> TwistedEdwardsPoint<Bn256> {
        // construct table from point
        let table = LookupTable::from_point(&p, self);

        // change scalar to radix16
        let scalar_in_base_16 = super::util::scalar_to_radix_16::<_, Self>(&scalar);

        // iterate and select from table
        let mut q = TwistedEdwardsPoint::identity();

        for i in (0..64).rev(){            
            let s_i = scalar_in_base_16[i];
            let t = table.select(s_i, self);

            for i in 0..4{
                q = self.double(&q);
            }

            q  = self.add(&q, &t)
        }

        q
    }


    // The negative of (X:Y:T:Z) is (-X:Y:-T:Z)
    fn negate(&self, p: &TwistedEdwardsPoint<Bn256>) -> TwistedEdwardsPoint<Bn256> {
        let mut q = p.clone();
        q.x.negate();
        q.t.negate();

        q
    }

    fn mul_by_generator<S: Into<<Self::Fs as PrimeField>::Repr>>(
        &self,
        scalar: S,
    ) -> TwistedEdwardsPoint<Bn256> {
        self.mul(&self.curve_params.generator, scalar)
    }
}

impl AltJubjub {
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

        let mut generator_t = generator_x.clone();
        generator_t.mul_assign(&generator_y);

        let generator = TwistedEdwardsPoint {
            x: generator_x,
            y: generator_y,
            t: generator_t,
            z: <Bn256 as ScalarEngine>::Fr::one(),
        };
        Self {
            curve_params: TwisterEdwardsCurveParams::new(d, a, generator),
        }
    }

    fn get_for_y(
        &self,
        y: <Bn256 as ScalarEngine>::Fr,
        sign: bool,
    ) -> Option<TwistedEdwardsPoint<Bn256>> {
        // Given a y on the curve, x^2 = (y^2 - 1) / (dy^2 + 1)
        // This is defined for all valid y-coordinates,
        // as dy^2 + 1 = 0 has no solution in Fr.
        let one = <Bn256 as ScalarEngine>::Fr::one();

        // tmp1 = y^2
        let mut tmp1 = y;
        tmp1.square();

        // tmp2 = (y^2 * d) + 1
        let mut tmp2 = tmp1;
        tmp2.mul_assign(&self.curve_params.param_d);
        tmp2.add_assign(&one);

        // tmp1 = y^2 - 1
        tmp1.sub_assign(&one);

        match tmp2.inverse() {
            Some(tmp2) => {
                // tmp1 = (y^2 - 1) / (dy^2 + 1)
                tmp1.mul_assign(&tmp2);

                match tmp1.sqrt() {
                    Some(mut x) => {
                        if x.into_repr().is_odd() != sign {
                            x.negate();
                        }

                        let mut t = x;
                        t.mul_assign(&y);

                        Some(TwistedEdwardsPoint {
                            x: x,
                            y: y,
                            t: t,
                            z: one,
                        })
                    }
                    None => None,
                }
            }
            None => None,
        }
    }

    pub fn rand<R: Rng>(&self, rng: &mut R) -> TwistedEdwardsPoint<Bn256> {
        loop {
            let y = rng.gen();

            if let Some(p) = self.get_for_y(y, rng.gen()) {
                return p;
            }
        }
    }
}

// [P, 2P, 3P .. 8P]
struct LookupTable<E: Engine>(Vec<TwistedEdwardsPoint<E>>);

impl<E: Engine> LookupTable<E> {
    // precomputation
    fn from_point<C: TwistedEdwardsCurve<E>>(p: &TwistedEdwardsPoint<E>, curve: &C) -> Self {
        let mut table = vec![p.clone(); 8];

        for i in 0..7 {
            table[i + 1] = curve.add(&p, &table[i]);
        }

        Self(table)
    }

    // -8 <= x <= 8
    fn select<C: TwistedEdwardsCurve<E>>(&self, x: i8, curve: &C) -> TwistedEdwardsPoint<E> {
        if x == 0 {
            return TwistedEdwardsPoint::identity();
        }

        let xmask = x >> 7;
        let abs = (xmask + x) ^ xmask;

        let mut p = TwistedEdwardsPoint::identity();

        for i in 1..9 {
            p = TwistedEdwardsPoint::conditional_select(
                (i == abs) as u8, // TODO: constant time eq
                &self.0[(i - 1) as usize].clone(),
                &p,
            );
        }

        // conditionally assign if x is neg
        let x_is_neg = (xmask & 1) as u8;
        let p_neg = curve.negate(&p);
        let result = TwistedEdwardsPoint::conditional_select(x_is_neg, &p_neg, &p);

        result
    }
}

impl<E: Engine> PartialEq for TwistedEdwardsPoint<E> {
    fn eq(&self, other: &TwistedEdwardsPoint<E>) -> bool {
        // p1 = (x1/z1, y1/z1)
        // p2 = (x2/z2, y2/z2)
        // Deciding that these two points are equal is a matter of
        // determining that x1/z1 = x2/z2, or equivalently that
        // x1*z2 = x2*z1, and similarly for y.

        let mut x1 = self.x;
        x1.mul_assign(&other.z);

        let mut y1 = self.y;
        y1.mul_assign(&other.z);

        let mut x2 = other.x;
        x2.mul_assign(&self.z);

        let mut y2 = other.y;
        y2.mul_assign(&self.z);

        x1 == x2 && y1 == y2
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
        let jubjub = AltJubjub::new();
        
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

        let jubjub = AltJubjub::new();

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

        let jubjub = AltJubjub::new();

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
