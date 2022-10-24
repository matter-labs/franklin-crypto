use bellman::{Engine, Field};
use std::ops::Range;

// We can reduce cost of each partial round by using an optimization from
// original Poseidon paper. Appendix-B explains details.
pub(crate) fn compute_optimized_matrixes<E: Engine, const DIM: usize, const SUBDIM: usize>(
    number_of_rounds: usize,
    original_mds: &[[E::Fr; DIM]; DIM],
) -> ([[E::Fr; DIM]; DIM], Vec<[[E::Fr; DIM]; DIM]>) {
    let original_mds = transpose::<E, DIM>(original_mds);
    let mut matrix = original_mds;
    let mut m_prime = identity::<E, DIM>();
    let mut sparse_matrixes = vec![[[E::Fr::zero(); DIM]; DIM]; number_of_rounds];
    for round in 0..number_of_rounds {
        // M'
        let m_hat = sub_matrix::<E, DIM, SUBDIM>(&matrix, 1..DIM, 1..DIM);
        m_prime = identity::<E, DIM>();
        set_sub_matrix::<E, DIM, SUBDIM>(&mut m_prime, 1..DIM, 1..DIM, &m_hat);

        // M"
        let w = sub_matrix::<E, DIM, SUBDIM>(&matrix, 1..DIM, 0..1);
        let v = sub_matrix::<E, DIM, SUBDIM>(&matrix, 0..1, 1..DIM);

        let m_hat_inv = try_inverse::<E, SUBDIM>(&m_hat).expect("inverse");
        let w_hat = multiply::<E, SUBDIM>(&m_hat_inv, &w);

        let mut sparse_matrix = identity::<E, DIM>();
        sparse_matrix[0][0] = matrix[0][0];
        set_sub_matrix::<E, DIM, SUBDIM>(&mut sparse_matrix, 0..1, 1..DIM, &v);
        set_sub_matrix::<E, DIM, SUBDIM>(&mut sparse_matrix, 1..DIM, 0..1, &w_hat);
        {
            // sanity check
            let actual = multiply::<E, DIM>(&m_prime, &sparse_matrix);
            assert_eq!(matrix, actual);
        }

        sparse_matrixes[round] = transpose::<E, DIM>(&sparse_matrix);
        matrix = multiply::<E, DIM>(&original_mds, &m_prime);
    }

    sparse_matrixes.reverse();
    sparse_matrixes
        .iter()
        .chain(&[m_prime.clone()])
        .for_each(|matrix| {
            let _ = try_inverse::<E, DIM>(matrix).expect("should have inverse");
        });

    (transpose::<E, DIM>(&m_prime), sparse_matrixes)
}

// Decontructs a sub matrix
pub(crate) fn sub_matrix<E: Engine, const DIM: usize, const SUBDIM: usize>(
    matrix: &[[E::Fr; DIM]; DIM],
    row_range: std::ops::Range<usize>,
    col_range: std::ops::Range<usize>,
) -> [[E::Fr; SUBDIM]; SUBDIM] {
    // we need following decompositions for optimized matrixes
    //          row     col
    // M' => 1..DIM   1..DIM
    // w  => 1..DIM   0..1
    // v  => 0..1     1..DIM
    assert!(
        (row_range.len() == SUBDIM || row_range.len() == 1)
            && (col_range.len() == SUBDIM || col_range.len() == 1),
        "row/col length should be in range"
    );
    let mut sub_matrix = [[E::Fr::zero(); SUBDIM]; SUBDIM];

    for (row_id, row) in matrix[row_range].iter().enumerate() {
        for (col_id, col) in row[col_range.clone()].iter().enumerate() {
            sub_matrix[row_id][col_id] = *col;
        }
    }

    sub_matrix
}

// Injects a lower dimension matrix into higher one.
pub(crate) fn set_sub_matrix<E: Engine, const DIM: usize, const SUBDIM: usize>(
    matrix: &mut [[E::Fr; DIM]; DIM],
    row_range: Range<usize>,
    col_range: Range<usize>,
    sub_matrix: &[[E::Fr; SUBDIM]; SUBDIM],
) {
    for (row_a, row_b) in matrix[row_range].iter_mut().zip(sub_matrix.iter()) {
        for (col_a, col_b) in row_a[col_range.clone()].iter_mut().zip(row_b.iter()) {
            *col_a = *col_b;
        }
    }
}

// Multiplies matrix with a vector  and assigns result into same vector.
pub(crate) fn mmul_assign<E: Engine, const DIM: usize>(
    matrix: &[[E::Fr; DIM]; DIM],
    vector: &mut [E::Fr; DIM],
) {
    // [M]xv
    let mut result = [E::Fr::zero(); DIM];
    for col in 0..DIM {
        result[col] = super::super::common::utils::scalar_product::<E>(vector, &matrix[col]);
    }
    vector.copy_from_slice(&result[..]);
}

// Multiplies two same dimension matrixes.
pub(crate) fn multiply<E: Engine, const DIM: usize>(
    m1: &[[E::Fr; DIM]; DIM],
    m2: &[[E::Fr; DIM]; DIM],
) -> [[E::Fr; DIM]; DIM] {
    let transposed_m2 = transpose::<E, DIM>(m2);

    let mut result = [[E::Fr::zero(); DIM]; DIM];

    for (i, rv) in m1.iter().enumerate() {
        for (j, cv) in transposed_m2.iter().enumerate() {
            result[i][j] = super::super::common::utils::scalar_product::<E>(rv, cv);
        }
    }

    result
}
// Transpose of a matrix.
pub(crate) fn transpose<E: Engine, const DIM: usize>(
    matrix: &[[E::Fr; DIM]; DIM],
) -> [[E::Fr; DIM]; DIM] {
    let mut values = [[E::Fr::zero(); DIM]; DIM];
    for i in 0..DIM {
        for j in 0..DIM {
            values[j][i] = matrix[i][j];
        }
    }

    values
}

// Computes inverse of 2-d or 3-d matrixes.
// We need inverse of matrix for optimized poseidon 
pub(crate) fn try_inverse<E: Engine, const DIM: usize>(
    m: &[[E::Fr; DIM]; DIM],
) -> Option<[[E::Fr; DIM]; DIM]> {
    match DIM {
        2 => try_inverse_dim_2::<E, DIM>(m),
        3 => try_inverse_dim_3::<E, DIM>(m),
        _ => unimplemented!("unsupported matrix dimension"),
    }
}

// Computes inverse of 2x2 matrix.
fn try_inverse_dim_2<E: Engine, const DIM: usize>(
    m: &[[E::Fr; DIM]; DIM],
) -> Option<[[E::Fr; DIM]; DIM]> {
    assert_eq!(DIM, 2);
    let determinant = {
        let mut a = m[0][0];
        a.mul_assign(&m[1][1]);

        let mut b = m[1][0];
        b.mul_assign(&m[0][1]);

        a.sub_assign(&b);

        a
    };

    let mut result = [[E::Fr::zero(); DIM]; DIM];
    let det_inv = if let Some(inv) = determinant.inverse() {
        inv
    } else {
        return None;
    };

    // m22 / determinant;
    result[0][0] = {
        let mut tmp = m[1][1];
        tmp.mul_assign(&det_inv);
        tmp
    };
    // -m12 / determinant;
    result[0][1] = {
        let mut tmp = m[0][1];
        tmp.negate();
        tmp.mul_assign(&det_inv);
        tmp
    };
    // -m21 / determinant;
    result[1][0] = {
        let mut tmp = m[1][0];
        tmp.negate();
        tmp.mul_assign(&det_inv);
        tmp
    };
    // m11 / determinant;
    result[1][1] = {
        let mut tmp = m[0][0];
        tmp.mul_assign(&det_inv);
        tmp
    };

    Some(result)
}

// Computes inverse of 3x3 matrix.
fn try_inverse_dim_3<E: Engine, const DIM: usize>(
    m: &[[E::Fr; DIM]; DIM],
) -> Option<[[E::Fr; DIM]; DIM]> {
    assert_eq!(DIM, 3);
    // m22 * m33 - m32 * m23;
    let minor_m12_m23 = {
        let mut a = m[1][1];
        a.mul_assign(&m[2][2]);

        let mut b = m[2][1];
        b.mul_assign(&m[1][2]);

        a.sub_assign(&b);

        a
    };

    //  m21 * m33 - m31 * m23;
    let minor_m11_m23 = {
        let mut a = m[1][0];
        a.mul_assign(&m[2][2]);

        let mut b = m[2][0];
        b.mul_assign(&m[1][2]);

        a.sub_assign(&b);

        a
    };
    // m21 * m32 - m31 * m22;
    let minor_m11_m22 = {
        let mut a = m[1][0];
        a.mul_assign(&m[2][1]);

        let mut b = m[2][0];
        b.mul_assign(&m[1][1]);

        a.sub_assign(&b);

        a
    };

    // m11 * minor_m12_m23 - m12 * minor_m11_m23 + m13 * minor_m11_m22;
    let determinant = {
        let mut a = m[0][0];
        a.mul_assign(&minor_m12_m23);

        let mut b = m[0][1];
        b.mul_assign(&minor_m11_m23);

        let mut c = m[0][2];
        c.mul_assign(&minor_m11_m22);

        a.sub_assign(&b);
        a.add_assign(&c);

        a
    };

    if determinant.is_zero() {
        // matrix is not invertible
        return None;
    }

    let mut result = [[E::Fr::zero(); DIM]; DIM];
    let det_inv = if let Some(inv) = determinant.inverse() {
        inv
    } else {
        return None;
    };
    //  minor_m12_m23 / determinant;
    result[0][0] = {
        let mut tmp = minor_m12_m23.clone();
        tmp.mul_assign(&det_inv);

        tmp
    };

    // (m13 * m32 - m33 * m12) / determinant;
    result[0][1] = {
        let mut a = m[0][2];
        a.mul_assign(&m[2][1]);

        let mut b = m[2][2];
        b.mul_assign(&m[0][1]);

        a.sub_assign(&b);

        a.mul_assign(&det_inv);

        a
    };

    // (m12 * m23 - m22 * m13) / determinant;
    result[0][2] = {
        let mut a = m[0][1];
        a.mul_assign(&m[1][2]);

        let mut b = m[1][1];
        b.mul_assign(&m[0][2]);

        a.sub_assign(&b);

        a.mul_assign(&det_inv);

        a
    };
    // -minor_m11_m23 / determinant;
    result[1][0] = {
        let mut tmp = minor_m11_m23;
        tmp.negate();
        tmp.mul_assign(&det_inv);

        tmp
    };
    // (m11 * m33 - m31 * m13) / determinant;
    result[1][1] = {
        let mut a = m[0][0];
        a.mul_assign(&m[2][2]);

        let mut b = m[2][0];
        b.mul_assign(&m[0][2]);

        a.sub_assign(&b);

        a.mul_assign(&det_inv);

        a
    };
    // (m13 * m21 - m23 * m11) / determinant;
    result[1][2] = {
        let mut a = m[0][2];
        a.mul_assign(&m[1][0]);

        let mut b = m[1][2];
        b.mul_assign(&m[0][0]);

        a.sub_assign(&b);

        a.mul_assign(&det_inv);

        a
    };
    // minor_m11_m22 / determinant;
    result[2][0] = {
        let mut tmp = minor_m11_m22;
        tmp.mul_assign(&det_inv);

        tmp
    };
    // m12 * m31 - m32 * m11) / determinant;
    result[2][1] = {
        let mut a = m[0][1];
        a.mul_assign(&m[2][0]);

        let mut b = m[2][1];
        b.mul_assign(&m[0][0]);

        a.sub_assign(&b);

        a.mul_assign(&det_inv);

        a
    };
    // (m11 * m22 - m21 * m12) / determinant;
    result[2][2] = {
        let mut a = m[0][0];
        a.mul_assign(&m[1][1]);

        let mut b = m[1][0];
        b.mul_assign(&m[0][1]);

        a.sub_assign(&b);

        a.mul_assign(&det_inv);

        a
    };

    Some(result)
}

// Computes identity of given dimension.
fn identity<E: Engine, const DIM: usize>() -> [[E::Fr; DIM]; DIM] {
    let mut identity = [[E::Fr::zero(); DIM]; DIM];
    for i in 0..DIM {
        for j in 0..DIM {
            let el = if i == j { E::Fr::one() } else { E::Fr::zero() };
            identity[i][j] = el;
        }
    }

    identity
}

// #[cfg(test)]
// mod test {
//     use super::super::super::tests::init_rng;

//     use super::*;
//     use franklin_crypto::bellman::bn256::{Bn256, Fr};
//     use franklin_crypto::bellman::PrimeField;
//     use rand::Rand;
//     #[test]
//     fn test_matrix_inverese() {
//         let one = Fr::one();
//         let mut two = one.clone();
//         two.add_assign(&one);
//         let mut three = two.clone();
//         three.add_assign(&one);

//         const DIM: usize = 3;
//         let values = [[two, one, one], [three, two, one], [two, one, two]];

//         let _ = try_inverse::<Bn256, DIM>(&values);

//         assert_eq!(
//             identity::<Bn256, DIM>(),
//             multiply::<Bn256, DIM>(
//                 &try_inverse::<Bn256, DIM>(&values).expect("inverse"),
//                 &values
//             )
//         );
//     }

//     #[test]
//     fn test_matrix_deconstruction() {
//         let one = Fr::one();
//         let mut two = one.clone();
//         two.add_assign(&one);
//         let mut three = two.clone();
//         three.add_assign(&one);

//         const DIM: usize = 3;
//         const SUBDIM: usize = 2;

//         let matrix = [[two, one, one], [three, two, one], [two, one, two]];

//         {
//             let expected = [[two, one], [one, two]];
//             let actual = sub_matrix::<Bn256, DIM, SUBDIM>(&matrix, 1..3, 1..3);
//             assert_eq!(expected, actual);
//         }
//     }

//     #[test]
//     fn test_inject_sub_matrix() {
//         let zero = Fr::zero();
//         let one = Fr::one();
//         let mut two = one.clone();
//         two.add_assign(&one);
//         let mut three = two.clone();
//         three.add_assign(&one);

//         const DIM: usize = 3;
//         const SUBDIM: usize = 2;

//         let mut matrix = [[two, one, one], [three, two, one], [two, one, two]];
//         let sub_matrix = [[zero, zero], [zero, zero]];

//         let expected_matrix = [[two, one, one], [three, zero, zero], [two, zero, zero]];

//         set_sub_matrix::<Bn256, DIM, SUBDIM>(&mut matrix, 1..3, 1..3, &sub_matrix);
//         assert_eq!(expected_matrix, matrix);
//     }

//     #[test]
//     fn test_matrix_transpose() {
//         let rng = &mut init_rng();

//         const DIM: usize = 3;
//         for _ in 0..10 {
//             let mut matrix = [[Fr::zero(); DIM]; DIM];
//             for i in 0..DIM {
//                 for j in 0..DIM {
//                     matrix[i][j] = Fr::rand(rng);
//                 }
//             }
//             assert_eq!(
//                 transpose::<Bn256, DIM>(&transpose::<Bn256, DIM>(&matrix)),
//                 matrix
//             );
//         }
//     }

//     #[test]
//     fn test_optimized_matrixes() {
//         let rng = &mut init_rng();

//         const DIM: usize = 3;
//         const SUBDIM: usize = 2;

//         let original_mds = crate::common::utils::construct_mds_matrix::<Bn256, _, DIM>(rng);

//         let (_, _) = compute_optimized_matrixes::<Bn256, DIM, SUBDIM>(5, &original_mds);
//     }

//     fn int_to_fe<E: Engine>(elements: &[i8]) -> Vec<E::Fr> {
//         elements
//             .iter()
//             .map(|el| {
//                 let mut repr = <E::Fr as PrimeField>::Repr::default();
//                 repr.as_mut()[0] = *el as u64;
//                 let mut fe = E::Fr::from_repr(repr).expect("valid fe");
//                 if *el < 0 {
//                     fe.negate();
//                 }
//                 fe
//             })
//             .collect::<Vec<E::Fr>>()
//     }
// }
