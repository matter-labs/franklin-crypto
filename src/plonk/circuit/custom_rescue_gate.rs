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

use super::allocated_num::{
    AllocatedNum
};

use super::linear_combination::{
    LinearCombination
};

use crate::rescue::*;

#[derive(Clone, Debug, Hash, Default)]
pub struct Rescue5CustomGate;

impl<E: Engine> GateInternal<E> for Rescue5CustomGate {
    fn name(&self) -> &'static str {
        "Alpha=5 custom gate for Rescue/Poseidon"
    }

    fn degree(&self) -> usize {
        2
    }

    fn can_include_public_inputs(&self) -> bool {
        false
    }

    fn all_queried_polynomials(&self) -> Vec<PolynomialInConstraint> {
        vec![
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(0)),
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(1)),
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(2)),
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(3)),
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
        3
    }

    fn verify_on_row(&self, row: usize, poly_storage: &AssembledPolynomialStorage<E>, last_row: bool) -> E::Fr {
        let a_value = poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(0), row);
        let b_value = poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(1), row);
        let c_value = poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(2), row);
        let d_value = poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(3), row);
        
        let mut tmp = a_value;
        tmp.square();
        tmp.sub_assign(&b_value);

        if !tmp.is_zero() {
            return tmp;
        }

        let mut tmp = b_value;
        tmp.square();
        tmp.sub_assign(&c_value);

        if !tmp.is_zero() {
            return tmp;
        }

        let mut tmp = c_value;
        tmp.mul_assign(&a_value);
        tmp.sub_assign(&d_value);

        tmp
    }

    fn put_public_inputs_into_selector_id(&self) -> Option<usize> {
        None
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

        let one = E::Fr::one();

        tmp.map_indexed(&worker,
            |i, el| {
                let a_value = a_raw_ref[i];
                let b_value = b_raw_ref[i];
                let c_value = c_raw_ref[i];
                let d_value = d_raw_ref[i];

                // a^2 - b = 0
                let mut result = a_value;
                result.square();
                result.sub_assign(&b_value);

                result.mul_assign(&challenges[0]);

                // b^2 - c = 0
                let mut tmp = b_value;
                tmp.square();
                tmp.sub_assign(&c_value);

                tmp.mul_assign(&challenges[1]);

                result.add_assign(&tmp);

                // c*a - d = 0;
                let mut tmp = c_value;
                tmp.mul_assign(&a_value);
                tmp.sub_assign(&d_value);

                tmp.mul_assign(&challenges[2]);

                result.add_assign(&tmp);

                *el = result;
            }, 
        );

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

        // a^2 - b = 0
        let mut result = a_value;
        result.square();
        result.sub_assign(&b_value);

        result.mul_assign(&challenges[0]);

        // b^2 - c = 0
        let mut tmp = b_value;
        tmp.square();
        tmp.sub_assign(&c_value);

        tmp.mul_assign(&challenges[1]);

        result.add_assign(&tmp);

        // c*a - d = 0;
        let mut tmp = c_value;
        tmp.mul_assign(&a_value);
        tmp.sub_assign(&d_value);

        tmp.mul_assign(&challenges[2]);

        result.add_assign(&tmp);

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

impl<E: Engine> Gate<E> for Rescue5CustomGate {}

pub fn apply_5th_power<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    el: &AllocatedNum<E>,
    existing_5th: Option<AllocatedNum<E>>,
) -> Result<AllocatedNum<E>, SynthesisError> {

    let squared = AllocatedNum::alloc(
        cs, 
        || {
            let mut val = *el.get_value().get()?;
            val.square();

            Ok(val)
        }
    )?;

    let quad = AllocatedNum::alloc(
        cs, 
        || {
            let mut val = *squared.get_value().get()?;
            val.square();

            Ok(val)
        }
    )?;

    let fifth = if let Some(f) = existing_5th {
        f
    } else {
        AllocatedNum::alloc(
            cs, 
            || {
                let mut val = *quad.get_value().get()?;
                val.mul_assign(el.get_value().get()?);

                Ok(val)
            }
        )?
    };

    let one = E::Fr::one();
    let mut minus_one = one;
    minus_one.negate();

    // we take a value and make 5th power from it
    cs.new_single_gate_for_trace_step(
        &Rescue5CustomGate::default(), 
        &[], 
        &[el.get_variable(), squared.get_variable(), quad.get_variable(), fifth.get_variable()], 
        &[]
    )?;

    Ok(fifth)
}

