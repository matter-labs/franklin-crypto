use bellman::pairing::ff::{Field, PrimeField};
use bellman::Engine;
use rand::Rng;
extern crate num_bigint;
extern crate num_integer;
extern crate num_traits;
use self::num_integer::{ExtendedGcd, Integer};
use self::num_traits::{One, ToPrimitive, Zero};
use std::convert::TryInto;
use num_bigint::{BigInt};
use num_bigint::BigUint;


// Batch inverses vector of elements required for MDS matrix.
pub(crate) fn batch_inversion<E: Engine>(v: &mut [E::Fr]) {
    // Montgomery’s Trick and Fast Implementation of Masked AES
    // Genelle, Prouff and Quisquater
    // Section 3.2

    // First pass: compute [a, ab, abc, ...]
    let mut prod = Vec::with_capacity(v.len());
    let mut tmp = E::Fr::one();
    for g in v
        .iter()
        // Ignore zero elements
        .filter(|g| !g.is_zero())
    {
        tmp.mul_assign(&g);
        prod.push(tmp);
    }

    // Invert `tmp`.
    tmp = tmp.inverse().unwrap(); // Guaranteed to be nonzero.

    // Second pass: iterate backwards to compute inverses
    for (g, s) in v
        .iter_mut()
        // Backwards
        .rev()
        // Ignore normalized elements
        .filter(|g| !g.is_zero())
        // Backwards, skip last element, fill in one for last term.
        .zip(prod.into_iter().rev().skip(1).chain(Some(E::Fr::one())))
    {
        // tmp := tmp * g.z; g.z := tmp * s = 1/z
        let mut newtmp = tmp;
        newtmp.mul_assign(&g);
        *g = tmp;
        g.mul_assign(&s);
        tmp = newtmp;
    }
}

// Computes scalar product of two same length vector.
pub(crate) fn scalar_product<E: Engine>(a: &[E::Fr], b: &[E::Fr]) -> E::Fr {
    let mut acc = E::Fr::zero();
    for (a, b) in a.iter().zip(b.iter()) {
        let mut tmp = a.clone();
        tmp.mul_assign(&b);
        acc.add_assign(&tmp);
    }
    acc
}

// Construct MDS matrix which required by lineary layer of permutation function.
pub(crate) fn construct_mds_matrix<E: Engine, R: Rng, const S: usize>(
    rng: &mut R,
) -> [[E::Fr; S]; S] {
    let WIDTH = S;

    loop {
        let x: Vec<E::Fr> = (0..WIDTH).map(|_| rng.gen()).collect();
        let y: Vec<E::Fr> = (0..WIDTH).map(|_| rng.gen()).collect();

        let mut invalid = false;

        // quick and dirty check for uniqueness of x
        for i in 0..(WIDTH) {
            if invalid {
                continue;
            }
            let el = x[i];
            for other in x[(i + 1)..].iter() {
                if el == *other {
                    invalid = true;
                    break;
                }
            }
        }

        if invalid {
            continue;
        }

        // quick and dirty check for uniqueness of y
        for i in 0..(WIDTH) {
            if invalid {
                continue;
            }
            let el = y[i];
            for other in y[(i + 1)..].iter() {
                if el == *other {
                    invalid = true;
                    break;
                }
            }
        }

        if invalid {
            continue;
        }

        // quick and dirty check for uniqueness of x vs y
        for i in 0..(WIDTH) {
            if invalid {
                continue;
            }
            let el = x[i];
            for other in y.iter() {
                if el == *other {
                    invalid = true;
                    break;
                }
            }
        }

        if invalid {
            continue;
        }

        // by previous checks we can be sure in uniqueness and perform subtractions easily
        let mut mds_matrix = vec![E::Fr::zero(); WIDTH * WIDTH];
        for (i, x) in x.into_iter().enumerate() {
            for (j, y) in y.iter().enumerate() {
                let place_into = i * (WIDTH) + j;
                let mut element = x;
                element.sub_assign(y);
                mds_matrix[place_into] = element;
            }
        }

        // now we need to do the inverse
        batch_inversion::<E>(&mut mds_matrix[..]);

        let mut result = [[E::Fr::zero(); S]; S];

        mds_matrix
            .chunks_exact(S)
            .zip(result.iter_mut())
            .for_each(|(values, row)| *row = values.try_into().expect("row in const"));

        return result;
    }
}

pub(crate) fn compute_gcd<E: Engine, const N: usize>(n: u64) -> Option<[u64; N]> {
    let y = compute_gcd_vec::<E>(n);

    match y {
        Some(value) => return Some(value.try_into().unwrap()),
        _ => return None,
    }
}

// Computes GCD of an element. It basically computes inverse of alpha in given finite field.
pub(crate) fn compute_gcd_biguint<E: Engine>(n: u64) -> Option<BigUint> {
    let n_big = BigUint::from(n);

    let mut p_minus_one_biguint = BigUint::from(0u64);
    for limb in E::Fr::char().as_ref().iter().rev() {
        p_minus_one_biguint <<= 64;
        p_minus_one_biguint += BigUint::from(*limb);
    }

    p_minus_one_biguint -= BigUint::one();

    let alpha_signed = BigInt::from(n_big);
    let p_minus_one_signed = BigInt::from(p_minus_one_biguint);

    let ExtendedGcd { gcd, x: _, mut y, .. } = p_minus_one_signed.extended_gcd(&alpha_signed);
    assert!(gcd.is_one());
    if y < BigInt::zero() {
        y += p_minus_one_signed;
        
    }

    y.to_biguint()
}

pub(crate) fn compute_gcd_vec<E: Engine>(n: u64) -> Option<Vec<u64>> {
    let y = compute_gcd_biguint::<E>(n);

    match y {
        Some(value) => return Some(biguint_to_u64_vec(value)),
        _ => return None,
    }
}

pub(crate) fn biguint_to_u64_vec(mut v: BigUint) -> Vec<u64> {
    let m: BigUint = BigUint::from(1u64) << 64;
    let mut ret = vec![];

    loop {
        if v.is_zero() {
            break;
        }

        let el = (&v % &m).to_u64().unwrap();
        ret.push(el);
        v >>= 64;
    }

    assert!(v.is_zero());
    ret
}

