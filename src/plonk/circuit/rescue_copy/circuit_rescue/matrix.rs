use bellman::{Engine, SynthesisError};
use plonk::circuit::linear_combination::LinearCombination;
// Computes matrix vector product and assigns result into same vector.
pub(crate) fn matrix_vector_product<E: Engine, const DIM: usize>(
    matrix: &[[E::Fr; DIM]; DIM],
    vector: &mut [LinearCombination<E>; DIM],
) -> Result<(), SynthesisError> {
    let vec_cloned = vector.clone();

    for (idx, row) in matrix.iter().enumerate() {
        // [fr, fr, fr] * [lc, lc, lc]
        vector[idx] = LinearCombination::zero();
        for (factor, lc) in row.iter().zip(&vec_cloned) {
            vector[idx].add_assign_scaled(lc, *factor)
        }
    }

    Ok(())
}

// Computes sparse matrix - vector by exploiting sparsity of optimized matrixes.
pub(crate) fn mul_by_sparse_matrix<E: Engine, const DIM: usize>(
    matrix: &[[E::Fr; DIM]; DIM],
    vector: &mut [LinearCombination<E>; DIM],
) {
    assert_eq!(DIM, 3, "valid only for 3x3 matrix");

    let vec_cloned = vector.clone();

    // we will assign result into input vector so set each to zero
    for lc in vector.iter_mut() {
        *lc = LinearCombination::zero();
    }    

    for (a, b) in vec_cloned.iter().zip(matrix[0].iter()) {
        vector[0].add_assign_scaled(a, *b);
    }

    vector[1].add_assign_scaled(&vec_cloned[0], matrix[1][0]);
    vector[1].add_assign(&vec_cloned[1]);

    vector[2].add_assign_scaled(&vec_cloned[0], matrix[2][0]);
    vector[2].add_assign(&vec_cloned[2]);
}

// #[cfg(test)]
// mod test {
//     use super::super::tests::{init_cs, init_rng};
//     use bellman::Field;
//     use {
//         bellman::pairing::bn256::{Bn256, Fr},
//         plonk::circuit::{allocated_num::AllocatedNum, linear_combination::LinearCombination},
//     };
//     use rand::Rand;
//     use std::convert::TryInto;

//     #[test]
//     fn test_matrix_product() {
//         let cs = &mut init_cs::<Bn256>();
//         let rng = &mut init_rng();

//         const DIM: usize = 3;

//         let mut vector_fe: [Fr; DIM] = [Fr::rand(rng); DIM];

//         let mut vector_lc: [LinearCombination<_>; DIM] = (0..DIM)
//             .map(|_| LinearCombination::zero())
//             .collect::<Vec<LinearCombination<_>>>()
//             .try_into()
//             .expect("vector of lc");
//         vector_fe
//             .iter()
//             .zip(vector_lc.iter_mut())
//             .for_each(|(src, dst)| {
//                 *dst = LinearCombination::from(AllocatedNum::alloc(cs, || Ok(*src)).unwrap())
//             });

//         let mut matrix = [[Fr::zero(); DIM]; DIM];
//         (0..9)
//             .map(|_| Fr::rand(rng))
//             .collect::<Vec<Fr>>()
//             .chunks_exact(3)
//             .zip(matrix.iter_mut())
//             .for_each(|(src, dst)| *dst = src.try_into().expect("static vector"));

//         matrix[1][1] = Fr::one();
//         matrix[1][2] = Fr::zero();
//         matrix[2][1] = Fr::zero();
//         matrix[2][2] = Fr::one();

//         crate::common::matrix::mmul_assign::<Bn256, DIM>(&matrix, &mut vector_fe);
//         super::mul_by_sparse_matrix(&matrix, &mut vector_lc);

//         vector_fe.iter().zip(vector_lc.iter()).for_each(|(fe, lc)| {
//             let actual = lc.clone().into_num(cs).unwrap().get_value().unwrap();
//             assert_eq!(*fe, actual);
//         });
//     }
// }
