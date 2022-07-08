use super::super::permutation_network::*;

use std::collections::HashMap;
use num_traits::Zero;
use plonk::circuit::boolean::Boolean;
use num_bigint::BigUint;
use plonk::circuit::curve::AffinePoint;
use plonk::circuit::allocated_num::Num;
use plonk::circuit::bigint::FieldElement;
use plonk::circuit::SynthesisError;
use crate::bellman::pairing::{Engine, GenericCurveAffine, GenericCurveProjective};
use crate::bellman::pairing::ff::{BitIterator, Field, PrimeField, PrimeFieldRepr, ScalarEngine};
use super::super::allocated_num::{AllocatedNum};
use super::super::linear_combination::LinearCombination;
use plonk::circuit::bigint::RnsParameters;

use crate::bellman::plonk::better_better_cs::cs::{
    ArithmeticTerm, Coefficient, ConstraintSystem, Gate, GateInternal, LinearCombinationOfTerms,
    MainGate, MainGateTerm, PlonkConstraintSystemParams, PlonkCsWidth4WithNextStepParams,
    PolynomialInConstraint, PolynomialMultiplicativeTerm, TimeDilation, TrivialAssembly, Variable,
    Width4MainGateWithDNext,
};

pub struct Memory<'a, E: Engine, G: GenericCurveAffine> 
where
    <G as GenericCurveAffine>::Base: PrimeField,
{
    pub block: Vec<(u64, AffinePoint<'a, E, G>)>,

    pub witness_map: HashMap<u64 ,AffinePoint<'a, E, G>>

}

impl<'a, E: Engine, G: GenericCurveAffine> Memory<'a, E, G>
where
    <G as GenericCurveAffine>::Base: PrimeField,
{
    pub fn new() -> Self{
        Self {
            block: vec![],
            witness_map: HashMap::new()
        }
    }
    pub fn read_and_alloc<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS, addr: u64, params: &'a RnsParameters<E, G::Base>) -> Result<AffinePoint<E, G>, SynthesisError>{

        let existing = self.witness_map.get(&addr).unwrap().clone();
        let witness_alloc = AffinePoint::alloc(cs, existing.value, params).unwrap();

        self.block.push((addr, witness_alloc));

        Ok(existing)

    }

    pub fn insert_witness(&mut self, addr: u64, point: AffinePoint<'a, E, G>){
        self.witness_map.insert(addr, point);
    }


    pub fn waksman_permutation<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError>{

        let size = self.block.len();
        let permutation = Self::calculate_permutation(&self.block);
        let permutation = if let Some(permutation) = permutation {
            permutation
        } else {
            IntegerPermutation::new(size)
        };

        let switches = order_into_switches_set(cs, &permutation)?;
        let mut total_num_switches = 0;
        for layer in switches.iter() {
            total_num_switches += layer.len();
        }

        use plonk::circuit::bigint::compute_shifts;
        let shifts = compute_shifts::<E::Fr>();
        let mut original_values = vec![];
        let mut original_indexes = vec![];

        let mut sorted_values = vec![];
        let mut sorted_indexes = vec![];
        

        let mut packed_original_values = vec![];
        let mut packed_sorted_values = vec![];


        for (addr, value ) in self.block.iter() {

            let value = value.clone();
            let y = FieldElement::into_limbs(value.y.clone());
            let x = FieldElement::into_limbs(value.x.clone());
            let step_for_y = 256 / y.len();
            let step_for_x = 256 / x.len();
            let mut i = 0;
            let mut j = 0;
            let mut lc_low = LinearCombination::zero(); 
            for l in 0..y.len()/2{
                lc_low.add_assign_number_with_coeff(&y[l].num, shifts[i]);
                i+= step_for_y;

            }
            for l in 0..x.len()/2{
                lc_low.add_assign_number_with_coeff(&x[l].num, shifts[j]);
                j+= step_for_x;

            }
            let value_low = lc_low.into_num(cs)?.get_variable();
            i=0;
            j=0;

            let mut lc_high = LinearCombination::zero();
            for m in y.len()/2..y.len(){
                lc_high.add_assign_number_with_coeff(&y[m].num, shifts[i]);
                i+= step_for_y;
            }
            for m in x.len()/2..x.len(){
                lc_high.add_assign_number_with_coeff(&x[m].num, shifts[j]);
                j+= step_for_x;
            }
            let value_high = lc_high.into_num(cs)?.get_variable();

            packed_original_values.push([value_low, value_high]);
            original_values.push(value);
            original_indexes.push(addr);

        }

        for index in permutation.elements.iter() {

            let value = original_values[*index].clone();
            let addr = original_indexes[*index].clone();
            sorted_values.push(value.clone());
            sorted_indexes.push(addr.clone());

            let value = value.clone();
            let y = FieldElement::into_limbs(value.y.clone());
            let x = FieldElement::into_limbs(value.x.clone());
            let step_for_y = 256 / y.len();
            let step_for_x = 256 / x.len();
            let mut i = 0;
            let mut j = 0;
            let mut lc_low = LinearCombination::zero(); 
            for l in 0..y.len()/2{
                lc_low.add_assign_number_with_coeff(&y[l].num, shifts[i]);
                i+= step_for_y;

            }
            for l in 0..x.len()/2{
                lc_low.add_assign_number_with_coeff(&x[l].num, shifts[j]);
                j+= step_for_x;

            }
            let value_low = lc_low.into_num(cs)?.get_variable();
            i=0;
            j=0;

            let mut lc_high = LinearCombination::zero();
            for m in y.len()/2..y.len(){
                lc_high.add_assign_number_with_coeff(&y[m].num, shifts[i]);
                i+= step_for_y;
            }
            for m in x.len()/2..x.len(){
                lc_high.add_assign_number_with_coeff(&x[m].num, shifts[j]);
                j+= step_for_x;
            }
            let value_high = lc_high.into_num(cs)?.get_variable();

            packed_sorted_values.push([value_low, value_high]);

        }
        let o0: Vec<_> = packed_original_values.iter().map(|el| el[0]).collect();
        let o1: Vec<_> = packed_original_values.into_iter().map(|el| el[1]).collect();
        let s0: Vec<_> = packed_sorted_values.iter().map(|el| el[0]).collect();
        let s1: Vec<_> = packed_sorted_values.into_iter().map(|el| el[1]).collect();

        prove_permutation_using_switches_witness(
            cs, 
            &o0,
            &s0,
            &switches
        )?;

        prove_permutation_using_switches_witness(
            cs, 
            &o1,
            &s1,
            &switches
        )?;


        let mut first_read_in_this_cell = Boolean::constant(true);
        let mut new_cell = Boolean::constant(true);

        let mut value_addr_iter = sorted_values.into_iter().zip(sorted_indexes.into_iter());
        let (value, addr) = value_addr_iter.next().unwrap();
        let mut pre_value = value.clone();
        let mut pre_addr = addr.clone();

        for (value, addr) in value_addr_iter{
            if addr == pre_addr{
                let (unchanged, _) = AffinePoint::equals(cs, value, pre_value.clone())?;
            }
            else{
                pre_addr = addr.clone();
                pre_value = value.clone();
            }
            
        }

        Ok(())

    }

    fn calculate_permutation(row: &Vec<(u64, AffinePoint<'a, E, G>)>) -> Option<IntegerPermutation> {
        
        let mut keys = vec![];
        for (addr, _) in row.iter() {
            let idx = keys.len();
            keys.push((idx, addr));
        }

        keys.sort_by(|a, b| a.1.cmp(&b.1));
        let integer_permutation: Vec<_> = keys.iter().map(|el| el.0).collect();

        let integer_permutation = IntegerPermutation::new_from_permutation(integer_permutation);

        Some(integer_permutation)
    }





} 

mod test {
    use super::*;

    use crate::bellman::pairing::bn256::{Bn256, Fq, Fr, G1Affine};
    use crate::plonk::circuit::*;

    #[test]
    fn test_add_on_random_witnesses() {
        use rand::{Rng, SeedableRng, XorShiftRng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

        let mut ram = Memory::new();
        let mut addres = 0 as u64;
        let mut vec_verif = vec![];
        let mut cs = TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();
        for i in 0..2 {

            let a_f: G1Affine = rng.gen();
            let a = AffinePoint::alloc(&mut cs, Some(a_f), &params).unwrap();

            vec_verif.push(a.clone());

            ram.block.push((addres, a.clone()));
            ram.witness_map.insert(addres, a.clone()); 
            addres+= 1 as u64;
        }

        let mut addr_get = 0 as u64; 
        for j in 0..2{
            let point = ram.read_and_alloc(&mut cs, addr_get, &params).unwrap();
            assert_eq!(vec_verif[j].value.unwrap(), point.value.unwrap());
            addr_get+= 1 as u64;
            
        }

        ram.waksman_permutation(&mut cs);



    }
}