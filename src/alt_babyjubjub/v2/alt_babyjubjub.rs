use crate::alt_babyjubjub::v2::edwards::{
    TwistedEdwardsCurve, TwistedEdwardsPoint, TwisterEdwardsCurveParams,
};
use bellman::pairing::bn256::Bn256;
use bellman::pairing::ff::BitIterator;
use bellman::{Engine, Field, PrimeField, PrimeFieldRepr, ScalarEngine, SqrtField};
use rand::{Rand, Rng};
use std::marker::PhantomData;

#[derive(Clone)]
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

        // H = B - aA
        //   = B + A
        let mut h = b;
        h.add_assign(&a);

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

        let mut res = TwistedEdwardsPoint::zero();

        for b in BitIterator::new(scalar.into()) {
            res = self.double(&res);

            if b {
                res = self.add(&p, &res);
            }
        }

        res
    }

    fn negate(&self, p: &TwistedEdwardsPoint<Bn256>) -> TwistedEdwardsPoint<Bn256> {
        let mut q = p.clone();
        q.x.negate();
        q.t.negate();

        q
    }
}

impl AltJubjub {
    pub fn new() -> Self {
        // d = -(168696/168700)
        let d = <Bn256 as ScalarEngine>::Fr::from_str(
            "12181644023421730124874158521699555681764249180949974110617291017600649128846",
        )
        .expect("field element d");

        Self {
            curve_params: TwisterEdwardsCurveParams::new(d),
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
