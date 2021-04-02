use bellman::pairing::bn256::Bn256;
use bellman::pairing::ff::BitIterator;
use bellman::{Engine, Field, PrimeField, PrimeFieldRepr, ScalarEngine, SqrtField};
use rand::{Rand, Rng};
use std::marker::PhantomData;

// [P, 2P, 3P .. 8P]
struct LookupTable<E: Engine>(Vec<TwistedEdwardsPoint<E>>);

impl<E: Engine> LookupTable<E> {
    // precomputation
    fn from_point<C: TwistedEdwardsCurveParams<E>>(p: &TwistedEdwardsPoint<E>, curve: &TwistedEdwardsCurveImplementor<E, C>) -> Self {
        let mut table = vec![p.clone(); 8];

        for i in 0..7 {
            table[i + 1] = curve.add(&p, &table[i]);
        }

        Self(table)
    }

    // -8 <= x <= 8
    fn select<C: TwistedEdwardsCurveParams<E>>(&self, x: i8, curve: &TwistedEdwardsCurveImplementor<E, C>) -> TwistedEdwardsPoint<E> {
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

impl<E: Engine> Eq for TwistedEdwardsPoint<E> {}

impl<E: Engine, C: TwistedEdwardsCurveParams<E>> TwistedEdwardsCurveImplementor<E, C> {
    pub fn add(
        &self,
        p: &TwistedEdwardsPoint<E>,
        q: &TwistedEdwardsPoint<E>,
    ) -> TwistedEdwardsPoint<E> {
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
        let mut c = self.curve_params.param_d().clone();
        c.mul_assign(&p.t);
        c.mul_assign(&q.t);

        // D = z1 * z2
        let mut d = p.z;
        d.mul_assign(&q.z);

        let h = if self.curve_params.is_param_a_equals_minus_one() {
            // H = B + A
            let mut h = b;
            h.add_assign(&a);
            h
        } else {
            // H = B - aA
            let mut h = a.clone();
            h.mul_assign(&self.curve_params.param_a());
            h.negate();
            h.add_assign(&b);
            h
        };

        // E = (x1 + y1) * (x2 + y2) - A - B
        let mut e = p.x;
        e.add_assign(&p.y);
        {
            let mut tmp = q.x;
            tmp.add_assign(&q.y);
            e.mul_assign(&tmp);
        }
        e.sub_assign(&a);
        e.sub_assign(&b);

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

    pub fn double(&self, p: &TwistedEdwardsPoint<E>) -> TwistedEdwardsPoint<E> {
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
        let d = if self.curve_params.is_param_a_equals_minus_one() {
            let mut d = a;
            d.negate();
            
            d
        } else {
            let mut d = a;
            d.mul_assign(&self.curve_params.param_a());

            d
        };

        // E = (X1+Y1)^2 - A - B
        let mut e = p.x;
        e.add_assign(&p.y);
        e.square();
        e.sub_assign(&a);
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

    pub fn mul<S: Into<<C::Fs as PrimeField>::Repr>>(
        &self,
        p: &TwistedEdwardsPoint<E>,
        scalar: S,
    ) -> TwistedEdwardsPoint<E> {
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

    pub fn ct_mul(
        &self,
        p: &TwistedEdwardsPoint<E>,
        scalar: C::Fs,
    ) -> TwistedEdwardsPoint<E> {
        // construct table from point
        let table = LookupTable::from_point(&p, self);

        // change scalar to radix16
        let scalar_in_base_16 = super::util::scalar_to_radix_16::<_, C>(&scalar);

        // iterate and select from table
        let mut q = TwistedEdwardsPoint::identity();

        for i in (0..64).rev(){            
            let s_i = scalar_in_base_16[i];
            let t = table.select(s_i, self);

            for _i in 0..4 {
                q = self.double(&q);
            }

            q  = self.add(&q, &t)
        }

        q
    }


    // The negative of (X:Y:T:Z) is (-X:Y:-T:Z)
    pub fn negate(&self, p: &TwistedEdwardsPoint<E>) -> TwistedEdwardsPoint<E> {
        let mut q = p.clone();
        q.x.negate();
        q.t.negate();

        q
    }

    pub fn mul_by_generator<S: Into<<C::Fs as PrimeField>::Repr>>(
        &self,
        scalar: S,
    ) -> TwistedEdwardsPoint<E> {
        self.mul(&self.curve_params.generator(), scalar)
    }
}

pub trait TwistedEdwardsCurveParams<E: Engine>: Clone {
    type Fs: PrimeField;

    fn is_param_a_equals_minus_one(&self) -> bool;
    fn param_d(&self) -> E::Fr;
    fn param_a(&self) -> E::Fr;
    fn generator(&self) -> TwistedEdwardsPoint<E>;
    fn log_2_cofactor(&self) -> usize;
}

pub struct TwistedEdwardsCurveImplementor<E: Engine, C: TwistedEdwardsCurveParams<E>> {
    pub curve_params: C,
    _marker: std::marker::PhantomData<E>
}

impl<E: Engine, C: TwistedEdwardsCurveParams<E>> TwistedEdwardsCurveImplementor<E, C> {
    pub fn new_from_params(params: C) -> Self {
        Self {
            curve_params: params,
            _marker: std::marker::PhantomData
        }
    }

    pub fn get_for_y(
        &self,
        y: E::Fr,
        sign: bool,
    ) -> Option<TwistedEdwardsPoint<E>> {
        // Given a y on the curve, x^2 = ((y^2 - 1) / (dy^2 + 1)) / -a
        // This is defined for all valid y-coordinates,
        // as dy^2 + 1 = 0 has no solution in Fr.
        let one = <E as ScalarEngine>::Fr::one();

        // tmp1 = y^2
        let mut tmp1 = y;
        tmp1.square();

        // tmp2 = (y^2 * d) + 1
        let mut tmp2 = tmp1;
        tmp2.mul_assign(&self.curve_params.param_d());
        tmp2.add_assign(&one);

        // tmp1 = y^2 - 1
        tmp1.sub_assign(&one);
        if !self.curve_params.is_param_a_equals_minus_one() {
            tmp1.mul_assign(&self.curve_params.param_a());
            tmp1.negate();
        }

        match tmp2.inverse() {
            Some(tmp2) => {
                // tmp1 = (y^2 - 1) / (dy^2 + 1) / (-a)
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

    pub fn rand<R: Rng>(&self, rng: &mut R) -> TwistedEdwardsPoint<E> {
        loop {
            let y = rng.gen();

            if let Some(p) = self.get_for_y(y, rng.gen()) {
                return p;
            }
        }
    }
}

pub(crate) trait ConditionalSelect<T> {
    fn conditional_select(flag: u8, first: T, second: T) -> T;
}

impl ConditionalSelect<u64> for u64 {
    fn conditional_select(flag: u8, first: u64, second: u64) -> u64 {
        let bit = flag as u64;

        bit*first + (1-bit)*second // TODO: check correctness
    }
}

#[derive(Clone, Debug)]
pub struct TwistedEdwardsPoint<E: Engine> {
    pub x: E::Fr,
    pub y: E::Fr,
    pub z: E::Fr,
    pub t: E::Fr,
}

impl<E: Engine> Copy for TwistedEdwardsPoint<E> {}

impl<E: Engine> TwistedEdwardsPoint<E> {
    pub fn into_xy(&self) -> (E::Fr, E::Fr) {
        let zinv = self.z.inverse().unwrap();

        let mut x = self.x;
        x.mul_assign(&zinv);

        let mut y = self.y;
        y.mul_assign(&zinv);

        (x, y)
    }
    // The identity element is represented by (x:y:t:z) -> (0:1:0:1)
    pub fn identity() -> TwistedEdwardsPoint<E> {
        let zero = E::Fr::zero();
        let one = E::Fr::one();

        TwistedEdwardsPoint {
            x: zero,
            y: one,
            t: zero,
            z: one,
        }
    }

    pub fn conditional_select(
        flag: u8,
        first: &Self,
        second: &Self,
    ) -> Self {
        fn conditional_select_fe<E: Engine>(flag: u8, first: &E::Fr, second: &E::Fr) -> E::Fr {
            let first_repr = first.into_raw_repr();
            let second_repr = second.into_raw_repr();
            let mut result_repr = <E::Fr as PrimeField>::Repr::default();
            
            result_repr.as_mut()[0] =  u64::conditional_select(flag, first_repr.as_ref()[0], second_repr.as_ref()[0]);
            result_repr.as_mut()[1] =  u64::conditional_select(flag, first_repr.as_ref()[1], second_repr.as_ref()[1]);
            result_repr.as_mut()[2] =  u64::conditional_select(flag, first_repr.as_ref()[2], second_repr.as_ref()[2]);
            result_repr.as_mut()[3] =  u64::conditional_select(flag, first_repr.as_ref()[3], second_repr.as_ref()[3]);

            // first and second are valid field elements so we can unwrap
            let result = E::Fr::from_raw_repr(result_repr).unwrap();

            result
        }

        let mut result = Self::identity();
        result.x = conditional_select_fe::<E>(flag, &first.x, &second.x);
        result.y = conditional_select_fe::<E>(flag, &first.y, &second.y);
        result.t = conditional_select_fe::<E>(flag, &first.t, &second.t);
        result.z = conditional_select_fe::<E>(flag, &first.z, &second.z);

        result
    }
}

#[derive(Clone, Debug)]
pub struct GenericTwistedEdwardsCurveParams<E: Engine> {
    pub is_param_a_equals_minus_one: bool,
    pub param_d: E::Fr,
    pub param_a: E::Fr,
    pub generator: TwistedEdwardsPoint<E>,
    pub log_2_cofactor: usize,
}

impl<E: Engine> Copy for GenericTwistedEdwardsCurveParams<E> {}

impl<E: Engine> GenericTwistedEdwardsCurveParams<E> {
    pub fn new(d: E::Fr, a: E::Fr, generator: TwistedEdwardsPoint<E>, log_2_cofactor: usize) -> Self {
        let mut minus_one = E::Fr::one();
        minus_one.negate();
        
        let is_param_a_equals_minus_one = a == minus_one; 

        Self { 
            param_d: d,
            param_a: a,
            is_param_a_equals_minus_one,
            generator,
            log_2_cofactor
        }
    }
}
