use crate::bellman::pairing::{
    Engine,
};

use crate::bellman::pairing::ff::{
    Field,
    PrimeField,
    PrimeFieldRepr,
    BitIterator
};

use crate::bellman::SynthesisError;
use crate::bellman::worker::Worker;
use crate::bellman::plonk::better_better_cs::cs::*;
use crate::bellman::plonk::polynomials::*;
use crate::bellman::plonk::fft::cooley_tukey_ntt::*;

use crate::circuit::{
    Assignment
};

#[derive(Clone, Debug, Hash, Default)]
pub struct TwoBitDecompositionRangecheckCustomGate;

impl<E: Engine> GateInternal<E> for TwoBitDecompositionRangecheckCustomGate {
    fn name(&self) -> &'static str {
        "Two bit decomposition gate for width 4"
    }
    fn can_include_public_inputs(&self) -> bool {
        false
    }

    fn put_public_inputs_into_selector_id(&self) -> Option<usize> {
        None
    }

    fn degree(&self) -> usize {
        4
    }

    fn all_queried_polynomials(&self) -> Vec<PolynomialInConstraint> {
        vec![
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(0)),
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(1)),
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(2)),
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(3)),
            PolynomialInConstraint::from_id_and_dilation(PolyIdentifier::VariablesPolynomial(3), 1),
        ]
    }

    fn setup_polynomials(&self) -> Vec<PolyIdentifier> {
        vec![
        ]
    }

    fn variable_polynomials(&self) -> Vec<PolyIdentifier> {
        vec![
            PolyIdentifier::VariablesPolynomial(0),
            PolyIdentifier::VariablesPolynomial(1),
            PolyIdentifier::VariablesPolynomial(2),
            PolyIdentifier::VariablesPolynomial(3),
        ]
    }

    fn benefits_from_linearization(&self) -> bool {
        false
    }

    fn linearizes_over(&self) -> Vec<PolynomialInConstraint> {
        vec![
        ]
    }

    fn needs_opened_for_linearization(&self) -> Vec<PolynomialInConstraint> {
        vec![
        ]
    }

    fn num_quotient_terms(&self) -> usize {
        4
    }

    fn verify_on_row(&self, row: usize, poly_storage: &AssembledPolynomialStorage<E>, last_row: bool) -> E::Fr {
        assert!(last_row == false, "can not be applied at the last row");
        let a_value = poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(0), row);
        let b_value = poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(1), row);
        let c_value = poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(2), row);
        let d_value = poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(3), row);
        let d_next_value = poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(3), row+1);

        let one = E::Fr::one();
        let mut two = one;
        two.double();
        let mut three = two;
        three.add_assign(&one);
        let mut four = two;
        four.double();

        for (high, high_and_low) in [
            (d_value, c_value),
            (c_value, b_value),
            (b_value, a_value),
            (a_value, d_next_value),
        ].iter() {
            let mut shifted_high = *high;
            shifted_high.mul_assign(&four);

            let mut low = *high_and_low;
            low.sub_assign(&shifted_high);

            let mut total = low;
            
            let mut tmp = low;
            tmp.sub_assign(&one);
            total.mul_assign(&tmp);

            let mut tmp = low;
            tmp.sub_assign(&two);
            total.mul_assign(&tmp);

            let mut tmp = low;
            tmp.sub_assign(&three);
            total.mul_assign(&tmp);

            if !total.is_zero() {
                return total;
            }
        }

        E::Fr::zero()
    }

    fn contribute_into_quotient(
        &self, 
        domain_size: usize,
        poly_storage: &mut AssembledPolynomialStorage<E>,
        monomials_storage: & AssembledPolynomialStorageForMonomialForms<E>,
        challenges: &[E::Fr],
        omegas_bitreversed: &BitReversedOmegas<E::Fr>,
        _omegas_inv_bitreversed: &OmegasInvBitreversed<E::Fr>,
        worker: &Worker
    ) -> Result<Polynomial<E::Fr, Values>, SynthesisError> {
        assert!(domain_size.is_power_of_two());
        assert_eq!(challenges.len(), <Self as GateInternal<E>>::num_quotient_terms(&self));

        let lde_factor = poly_storage.lde_factor;
        assert!(lde_factor.is_power_of_two());

        assert!(poly_storage.is_bitreversed);

        let coset_factor = E::Fr::multiplicative_generator();
       
        for p in <Self as GateInternal<E>>::all_queried_polynomials(&self).into_iter() {
            ensure_in_map_or_create(&worker, 
                p, 
                domain_size, 
                omegas_bitreversed, 
                lde_factor, 
                coset_factor, 
                monomials_storage, 
                poly_storage
            )?;
        }

        let ldes_storage = &*poly_storage;

        let a_ref = get_from_map_unchecked(
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(0)),
            ldes_storage
        );

        let mut tmp = a_ref.clone(); // just allocate, we don't actually use it
        drop(a_ref);

        let a_raw_ref = get_from_map_unchecked(
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(0)),
            ldes_storage
        ).as_ref();

        let b_raw_ref = get_from_map_unchecked(
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(1)),
            ldes_storage
        ).as_ref();

        let c_raw_ref = get_from_map_unchecked(
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(2)),
            ldes_storage
        ).as_ref();

        let d_raw_ref = get_from_map_unchecked(
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(3)),
            ldes_storage
        ).as_ref();

        let d_next_raw_ref = get_from_map_unchecked(
            PolynomialInConstraint::from_id_and_dilation(PolyIdentifier::VariablesPolynomial(3), 1),
            ldes_storage
        ).as_ref();

        let one = E::Fr::one();
        let mut two = one;
        two.double();
        let mut three = two;
        three.add_assign(&one);
        let mut four = two;
        four.double();

        // c - 4d \in [0, 4)
        // b - 4c \in [0, 4)
        // a - 4b \in [0, 4)
        // d_next - 4a \in [0, 4)

        tmp.map_indexed(&worker,
            |i, el| {
                let a_value = a_raw_ref[i];
                let b_value = b_raw_ref[i];
                let c_value = c_raw_ref[i];
                let d_value = d_raw_ref[i];
                let d_next_value = d_next_raw_ref[i];

                let mut result = E::Fr::zero();

                for (contribution_idx, (high, high_and_low)) in [
                    (d_value, c_value),
                    (c_value, b_value),
                    (b_value, a_value),
                    (a_value, d_next_value),
                ].iter().enumerate() {
                    let mut shifted_high = *high;
                    shifted_high.mul_assign(&four);

                    let mut low = *high_and_low;
                    low.sub_assign(&shifted_high);

                    let mut total = low;
                    
                    let mut tmp = low;
                    tmp.sub_assign(&one);
                    total.mul_assign(&tmp);

                    let mut tmp = low;
                    tmp.sub_assign(&two);
                    total.mul_assign(&tmp);

                    let mut tmp = low;
                    tmp.sub_assign(&three);
                    total.mul_assign(&tmp);

                    total.mul_assign(&challenges[contribution_idx]);

                    result.add_assign(&total);
                }

                *el = result;
            }, 
        );

        // {
        //     let mut t = tmp.clone();
        //     t.bitreverse_enumeration(&worker);
        //     let mons = t.icoset_fft_for_generator(&worker, &coset_factor);
        //     let values = mons.fft(&worker);
        //     for i in 0..values.as_ref().len() {
        //         if i % 4 == 0 {
        //             dbg!(values.as_ref()[i]);
        //         }
        //     }
            
        // }

        Ok(tmp)
    }

    fn contribute_into_linearization(
        &self, 
        _domain_size: usize,
        _at: E::Fr,
        _queried_values: &std::collections::HashMap<PolynomialInConstraint, E::Fr>,
        _monomials_storage: & AssembledPolynomialStorageForMonomialForms<E>,
        _challenges: &[E::Fr],
        _worker: &Worker
    ) -> Result<Polynomial<E::Fr, Coefficients>, SynthesisError> {
        unreachable!("this gate does not contribute into linearization");
    }
    fn contribute_into_verification_equation(
        &self, 
        _domain_size: usize,
        _at: E::Fr,
        queried_values: &std::collections::HashMap<PolynomialInConstraint, E::Fr>,
        challenges: &[E::Fr],
    ) -> Result<E::Fr, SynthesisError> {
        assert_eq!(challenges.len(), <Self as GateInternal<E>>::num_quotient_terms(&self));

        let a_value = *queried_values.get(&PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(0)))
            .ok_or(SynthesisError::AssignmentMissing)?;
        let b_value = *queried_values.get(&PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(1)))
            .ok_or(SynthesisError::AssignmentMissing)?;
        let c_value = *queried_values.get(&PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(2)))
            .ok_or(SynthesisError::AssignmentMissing)?;
        let d_value = *queried_values.get(&PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(3)))
            .ok_or(SynthesisError::AssignmentMissing)?;
        let d_next_value = *queried_values.get(&PolynomialInConstraint::from_id_and_dilation(PolyIdentifier::VariablesPolynomial(3), 1))
            .ok_or(SynthesisError::AssignmentMissing)?;
        
        let mut result = E::Fr::zero();

        let one = E::Fr::one();
        let mut two = one;
        two.double();
        let mut three = two;
        three.add_assign(&one);
        let mut four = two;
        four.double();

        for (contribution_idx, (high, high_and_low)) in [
            (d_value, c_value),
            (c_value, b_value),
            (b_value, a_value),
            (a_value, d_next_value),
        ].iter().enumerate() {
            let mut shifted_high = *high;
            shifted_high.mul_assign(&four);

            let mut low = *high_and_low;
            low.sub_assign(&shifted_high);

            let mut total = low;
            
            let mut tmp = low;
            tmp.sub_assign(&one);
            total.mul_assign(&tmp);

            let mut tmp = low;
            tmp.sub_assign(&two);
            total.mul_assign(&tmp);

            let mut tmp = low;
            tmp.sub_assign(&three);
            total.mul_assign(&tmp);

            total.mul_assign(&challenges[contribution_idx]);

            result.add_assign(&total);
        }

        Ok(result)
    }

    fn box_clone(&self) -> Box<dyn GateInternal<E>> {
        Box::from(self.clone())
    }

    fn contribute_into_linearization_commitment(
        &self, 
        _domain_size: usize,
        _at: E::Fr,
        _queried_values: &std::collections::HashMap<PolynomialInConstraint, E::Fr>,
        _commitments_storage: &std::collections::HashMap<PolyIdentifier, E::G1Affine>,
        _challenges: &[E::Fr],
    ) -> Result<E::G1, SynthesisError> {
        unreachable!("this gate does not contribute into linearization");
    }
}

impl<E: Engine> Gate<E> for TwoBitDecompositionRangecheckCustomGate {}
