use super::super::permutation_network::*;

use std::collections::HashMap;
use digest::generic_array::typenum::array;
use num_traits::Zero;
use plonk::circuit::boolean::Boolean;
use num_bigint::BigUint;
use plonk::circuit::curve::AffinePoint;
use plonk::circuit::bigint::FieldElement;
use plonk::circuit::SynthesisError;
use crate::bellman::pairing::{Engine, GenericCurveAffine, GenericCurveProjective};
use crate::bellman::pairing::ff::{BitIterator, Field, PrimeField, PrimeFieldRepr, ScalarEngine};
use super::super::allocated_num::*;
use plonk::circuit::linear_combination::*;
use plonk::circuit::bigint::RnsParameters;
use std::cell::RefCell;
use plonk::circuit::curve::structual_eq::CircuitEq;
use plonk::circuit::curve::structual_eq::CircuitSelectable;
use plonk::circuit::utils::u64_to_fe;
use std::convert::TryInto;
use plonk::circuit::curve::sponge::*;
use plonk::circuit::rescue_copy::traits::HashParams;
use plonk::circuit::rescue_copy::sponge::generic_round_function;
use plonk::circuit::rescue_copy::circuit_rescue::sponge::circuit_generic_round_function;

use crate::bellman::plonk::better_better_cs::cs::{
    ArithmeticTerm, Coefficient, ConstraintSystem, Gate, GateInternal,
    MainGate, MainGateTerm, PlonkConstraintSystemParams, PlonkCsWidth4WithNextStepParams,
    PolynomialInConstraint, PolynomialMultiplicativeTerm, TimeDilation, TrivialAssembly, Variable,
    Width4MainGateWithDNext,
};
use plonk::circuit::bigint::fe_to_biguint;

pub trait CircuitArithmeticRoundFunction<E: Engine, const AWIDTH: usize, const SWIDTH: usize>: Clone + Eq {
    type StateElement: Clone + CircuitEq<E> + CircuitSelectable<E>;

    fn simulate_round_function(
        &self,
        state: [E::Fr; SWIDTH]
    ) -> [E::Fr; SWIDTH];

    fn simulate_absorb(
        &self,
        state: [E::Fr; SWIDTH],
        input: &[E::Fr]
    ) -> [E::Fr; SWIDTH] {
        assert!(input.len() < SWIDTH);
        let mut state = state;
        for (s, inp) in state.iter_mut().zip(input.iter()) {
            s.add_assign(inp);
        }

        self.simulate_round_function(state)
    }
    #[track_caller]
    fn simulate_apply_length_specialization(
        &self, state: [E::Fr; SWIDTH], length: usize
    ) -> [E::Fr; SWIDTH] {
        assert!(state == self.simulate_empty_state());
        let mut state = state;
        let idx = state.len() - 1;
        state[idx] = u64_to_fe(length as u64);

        state
    }
    #[track_caller]
    fn apply_length_specialization(
        &self, state: [Self::StateElement; SWIDTH], _length: usize
    ) -> [Self::StateElement; SWIDTH] {
        assert!(state.eq(&Self::empty_state()));
        unimplemented!();
    }

    fn empty_state() -> [Self::StateElement; SWIDTH];

    fn simulate_absorb_into_empty_with_specialization(
        &self,
        input: &[E::Fr]
    ) -> [E::Fr; SWIDTH] {
        let input_length = input.len();
        let state = self.simulate_apply_length_specialization(self.simulate_empty_state(), input_length);
        self.simulate_absorb(state, input)
    }

    fn simulate_absorb_multiple_rounds(
        &self,
        state: [E::Fr; SWIDTH],
        input: &[E::Fr]
    ) -> Vec<([E::Fr; SWIDTH],[E::Fr; SWIDTH])>;

    fn num_absorbtion_rounds_for_input_length(
        &self,
        length: usize
    ) -> usize;

    fn simulate_absorb_multiple_rounds_into_empty_with_specialization(
        &self,
        input: &[E::Fr]
    ) -> Vec<([E::Fr; SWIDTH],[E::Fr; SWIDTH])> {
        let input_length = input.len();
        let state = self.simulate_apply_length_specialization(self.simulate_empty_state(), input_length);
        self.simulate_absorb_multiple_rounds(state, input)
    }

    fn simulate_empty_state(
        &self,
    ) -> [E::Fr; SWIDTH]{
        [E::Fr::zero(); SWIDTH]
    }

    fn round_function<CS: ConstraintSystem<E>>(
        &self, cs: &mut CS, state: [Self::StateElement; SWIDTH]
    ) -> Result<[Self::StateElement; SWIDTH], SynthesisError>;

    fn round_function_absorb_nums<CS: ConstraintSystem<E>>(
        &self, cs: &mut CS, state: [Self::StateElement; SWIDTH], input: &[Num<E>]
    ) -> Result<[Self::StateElement; SWIDTH], SynthesisError>;

    fn round_function_absorb_nums_multiple_rounds<CS: ConstraintSystem<E>>(
        &self, cs: &mut CS, state: [Self::StateElement; SWIDTH], input: &[Num<E>]
    ) -> Result<[Self::StateElement; SWIDTH], SynthesisError> {
        assert!(input.len() % AWIDTH == 0);
        let mut state = state;
        for chunk in input.chunks_exact(AWIDTH) {
            state = self.round_function_absorb_nums(cs, state, chunk)?
        }

        Ok(state)
    }

    fn state_into_commitment(
        state: [Self::StateElement; SWIDTH]
    ) -> Result<Num<E>, SynthesisError>;

    fn simulate_state_into_commitment(
        state: [E::Fr; SWIDTH]
    ) -> E::Fr;

    fn chunk_and_pad_input(
        &self,
        input: &[Num<E>]
    ) -> Vec<Vec<Num<E>>>;
}

impl<E: Engine, P: HashParams<E, AWIDTH, SWIDTH>, const AWIDTH: usize, const SWIDTH: usize> CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH> for GenericHasher<E, P, AWIDTH, SWIDTH>
{
    type StateElement = Num<E>;

    fn simulate_round_function(
        &self,
        state: [E::Fr; SWIDTH]
    ) -> [E::Fr; SWIDTH] {
        
        let mut new_state = state;

        generic_round_function(&self.params, &mut new_state);

        new_state
    }

    fn num_absorbtion_rounds_for_input_length(
        &self,
        length: usize
    ) -> usize {
        let mut num_rounds = length / AWIDTH;
        if length % AWIDTH != 0 {
            num_rounds += 1;
        }

        num_rounds
    }

    fn simulate_absorb_multiple_rounds(
        &self,
        state: [E::Fr; SWIDTH],
        input: &[E::Fr]
    ) -> Vec<([E::Fr; SWIDTH], [E::Fr; SWIDTH])> {
        let padding = E::Fr::one();
        let length = input.len();
        let rate = AWIDTH;
        let num_rounds = self.num_absorbtion_rounds_for_input_length(length);

        let pad_by = rate - length % rate;
        let mut it = input.iter().chain(std::iter::repeat(&padding).take(pad_by));
        let mut state = state;

        let mut round_outputs = vec![];

        let iterable = &mut it;
        for _ in 0..num_rounds {
            for (s, inp) in state.iter_mut().zip(iterable.take(rate)) {
                s.add_assign(inp);
            }
            let initial_state = state;
            state = self.simulate_round_function(state);
            round_outputs.push((initial_state, state));
        }
        
        round_outputs
    }

    #[track_caller]
    fn simulate_apply_length_specialization(
        &self, state: [E::Fr; SWIDTH], length: usize
    ) -> [E::Fr; SWIDTH] {
        assert!(state == self.simulate_empty_state());
        let mut state = state;
        let idx = state.len() - 1;
        state[idx] = u64_to_fe(length as u64);

        state
    }

    fn empty_state() -> [Self::StateElement; SWIDTH] {
        [Num::zero(); SWIDTH]
    }

    fn apply_length_specialization(
        &self, state: [Self::StateElement; SWIDTH], length: usize
    ) -> [Self::StateElement; SWIDTH]{
        assert!(state.eq(&Self::empty_state()));

        let mut state = state;
        *state.last_mut().expect("is some") = Num::Constant(u64_to_fe(length as u64));

        state
    }

    fn round_function<CS: ConstraintSystem<E>>(
        &self, cs: &mut CS, state: [Self::StateElement; SWIDTH]
    ) -> Result<[Self::StateElement; SWIDTH], SynthesisError> {

        let mut state_lcs = vec![];
        for s in state.iter() {
            let lc = LinearCombination::from(*s);
            state_lcs.push(lc);
        }


        let mut state_lcs = state_lcs.try_into().expect("state width should match");

        circuit_generic_round_function(
            cs,
            &mut state_lcs,
            &self.params
        )?;


        let mut new_state = [Num::Constant(E::Fr::zero()); SWIDTH];
        for (a, b) in new_state.iter_mut().zip(state_lcs.iter()){
            *a = b.clone().into_num(cs)?;
        }

        Ok(new_state)
    }

    fn round_function_absorb_nums<CS: ConstraintSystem<E>>(
        &self, cs: &mut CS, state: [Self::StateElement; SWIDTH], input: &[Num<E>]
    ) -> Result<[Self::StateElement; SWIDTH], SynthesisError> {
        assert_eq!(input.len(), AWIDTH);

        let mut state_lcs = vec![];
        for (s, inp) in state[..input.len()].iter().zip(input.iter())  {
            let mut lc = LinearCombination::from(*s);
            lc.add_assign_number_with_coeff(&inp, E::Fr::one());
            state_lcs.push(lc);
        }

        for s in state[input.len()..].iter() {
            let lc = LinearCombination::from(*s);
            state_lcs.push(lc);
        }

        let mut state_lcs = state_lcs.try_into().expect("state width should match");
        
        circuit_generic_round_function(cs, &mut state_lcs, &self.params)?;

        let mut new_state = [Num::Constant(E::Fr::zero()); SWIDTH];
        for (a, b) in new_state.iter_mut().zip(state_lcs.iter()) {
            *a = b.clone().into_num(cs)?;
        }

        Ok(new_state)
    }

    // fn round_function_absorb_lcs<CS: ConstraintSystem<E>, const N: usize>(
    //     cs: &mut CS, state: [Self::StateElement; N], input: &[LinearCombination<E>]
    // ) -> Result<[Self::StateElement; N], SynthesisError>;

    fn state_into_commitment(
        state: [Self::StateElement; SWIDTH]
    ) -> Result<Num<E>, SynthesisError> {
        Ok(state[0])
    }

    fn simulate_state_into_commitment(
        state: [E::Fr; SWIDTH]
    ) -> E::Fr {
        state[0]
    }

    fn chunk_and_pad_input(
        &self,
        input: &[Num<E>]
    ) -> Vec<Vec<Num<E>>> {
        let mut result = vec![];
        let num_rounds = self.num_absorbtion_rounds_for_input_length(input.len());
        let rate = AWIDTH;
        let mut chunks_it = input.chunks(rate);
        for _ in 0..num_rounds {
            let mut chunk = chunks_it.next().expect("is some").to_vec();
            chunk.resize(rate, Num::Constant(E::Fr::one()));
            result.push(chunk);
        }

        result
    }
}
pub fn variable_length_absorb_into_state<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    const AWIDTH: usize,
    const SWIDTH: usize,
>(
    cs: &mut CS,
    input: &[Num<E>],
    into_state: &[R::StateElement; SWIDTH],
    round_function: &R,
) -> Result<[R::StateElement; SWIDTH], SynthesisError> {
    let mut state = *into_state;
    for chunk in input.chunks(AWIDTH) {
        let padding_els = AWIDTH - chunk.len();
        let input_fixed_len: [Num<E>; AWIDTH] = if padding_els == 0 {
            chunk.try_into().expect("length must match")
        } else {
            let tmp = Num::one();
            let it = chunk.iter().chain(std::iter::repeat(&tmp).take(padding_els));

            it.copied()
            .collect::<Vec<_>>()
            .as_slice()
            .try_into()
            .expect("length must match")
        };

        state = round_function.round_function_absorb_nums(cs, state, &input_fixed_len)?;
    }

    Ok(state)
}
pub fn variable_length_absorb_into_empty_state<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    const AWIDTH: usize,
    const SWIDTH: usize
>(
    cs: &mut CS,
    input: &[Num<E>],
    round_function: &R
) -> Result<[Num<E>; SWIDTH], SynthesisError> {
    let state = R::empty_state();
    let state = round_function.apply_length_specialization(state, input.len());
    let state = variable_length_absorb_into_state(
        cs,
        &input[..],
        &state,
        round_function
    )?;

    Ok(state)
}

pub fn variable_length_hash<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    const AWIDTH: usize,
    const SWIDTH: usize
>(
    cs: &mut CS,
    input: &[Num<E>],
    round_function: &R
) -> Result<Num<E>, SynthesisError> {
    let state = variable_length_absorb_into_empty_state(cs, input, round_function)?;

    let committment = R::state_into_commitment(state)?;

    Ok(committment)
}
pub fn variable_length_hash_using_optimizer<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    const AWIDTH: usize,
    const SWIDTH: usize
>(
    cs: &mut CS,
    input: &[Num<E>],
    id: u64,
    execute: Boolean,
    optimizer: &mut SpongeOptimizer<E, R, AWIDTH, SWIDTH>
) -> Result<Num<E>, SynthesisError> {
    let state = variable_length_hash_into_empty_state_using_optimizer(
        cs,
        input,
        id,
        execute,
        optimizer
    )?;

    let committment = R::state_into_commitment(state)?;

    Ok(committment)
}
pub fn variable_length_hash_into_empty_state_using_optimizer<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    const AWIDTH: usize,
    const SWIDTH: usize,
>(
    cs: &mut CS,
    input: &[Num<E>],
    id: u64,
    execute: Boolean,
    optimizer: &mut SpongeOptimizer<E, R, AWIDTH, SWIDTH>
) -> Result<[R::StateElement; SWIDTH], SynthesisError> {
    let empty_state = R::empty_state();
    let len = input.len();
    let specialized_state = optimizer.round_function.apply_length_specialization(empty_state, len);

    variable_length_absorb_into_state_using_optimizer(
        cs,
        input,
        &specialized_state,
        id,
        execute,
        optimizer
    )
}
pub fn variable_length_absorb_into_state_using_optimizer<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    const AWIDTH: usize,
    const SWIDTH: usize,
>(
    cs: &mut CS,
    input: &[Num<E>],
    into_state: &[R::StateElement; SWIDTH],
    id: u64,
    execute: Boolean,
    optimizer: &mut SpongeOptimizer<E, R, AWIDTH, SWIDTH>
) -> Result<[R::StateElement; SWIDTH], SynthesisError> {
    let len = input.len();
    let input_witness = Num::get_value_for_slice(&input);
    let state_witness = Num::get_value_multiple(&into_state);

    let intermediate_states = match (input_witness, state_witness) {
        (Some(input_witness), Some(state_witness)) => {
            let intemediates = optimizer.round_function.simulate_absorb_multiple_rounds(state_witness, &input_witness[..]);

            Some(intemediates)
        },
        _ => None
    };

    let num_rounds = optimizer.round_function.num_absorbtion_rounds_for_input_length(len);
    let input_chunks = optimizer.round_function.chunk_and_pad_input(input);

    let last_round_idx = num_rounds - 1;
    let mut last_state = *into_state;
    assert_eq!(input_chunks.len(), num_rounds);

    for round_id in 0..num_rounds {
        let witness = intermediate_states.as_ref().map(|el| el[round_id].1);
        let intermediate = Num::alloc_multiple(cs, witness)?;

        let feed_forward = if round_id != last_round_idx {
            Boolean::constant(true)
        } else {
            Boolean::constant(false)
        };

        let initial_state = last_state;

        let chunk = &input_chunks[round_id][..];

        let padding_els = AWIDTH - chunk.len();
        let input_fixed_len: [Num<E>; AWIDTH] = if padding_els == 0 {
            chunk.try_into().expect("length must match")
        } else {
            let tmp = Num::one();
            let it = chunk.iter().chain(std::iter::repeat(&tmp).take(padding_els));

            it.copied()
            .collect::<Vec<_>>()
            .as_slice()
            .try_into()
            .expect("length must match")
        };
        
        let request = SpongeRoundRequest {
            initial_state,
            values_to_absorb: input_fixed_len,
            claimed_final_state: intermediate,
            feed_forward,
        };

        optimizer.add_request(request, execute, id);
        
        last_state = intermediate;
    }

    Ok(last_state)
}

pub fn bit_window_decompose(window: usize) -> usize{
    let mut bit_window = 0;
    let two = 2 as u32;
    for i in 0..window{
        bit_window += two.pow(i as u32);
    }
    bit_window as usize
}
pub fn can_not_be_false_if_flagged<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    condition: &Boolean,
    condition_must_be_valid: &Boolean,
) -> Result<(), SynthesisError> {
    // only forbidden combination is condition is false and condition_must_be_valid == true
    match (condition.get_value(), condition_must_be_valid.get_value()) {
        (Some(c), Some(f)) => {
            let valid = if f {
                c
            } else {
                true
            };
            assert!(valid, "condition is broken: condition = {}, while enforcing flag = {}", c, f);
        },
        _ => {}
    }

    // TODO: we can trivially optimize here
    let invalid = Boolean::and(cs, &condition.not(), &condition_must_be_valid)?;
    Boolean::enforce_equal(cs, &invalid, &Boolean::constant(false))?;

    Ok(())
}
#[derive(Clone, Debug)]
pub struct Memory<'a, E: Engine, G: GenericCurveAffine> 
where
    <G as GenericCurveAffine>::Base: PrimeField,
{
    pub block: Vec<(Num<E>, AffinePoint<'a, E, G>)>,

    pub witness_map: HashMap<BigUint , RefCell<AffinePoint<'a, E, G>>>

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
    pub fn read_and_alloc<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS, addr: Num<E>, params: &'a RnsParameters<E, G::Base>) -> Result<AffinePoint<'a, E, G>, SynthesisError>{

        let addres = fe_to_biguint(&addr.get_value().unwrap());

        let existing = self.witness_map.get(&addres).unwrap().clone();
        let witness_alloc = AffinePoint::alloc(cs, existing.clone().into_inner().value.clone(), params).unwrap();

        self.block.push((addr, witness_alloc.clone()));

        Ok(witness_alloc)
    }

    pub fn insert_witness(&mut self, addr: Num<E>, point: AffinePoint<'a, E, G>){
        let addres = fe_to_biguint(&addr.get_value().unwrap());
        let value = RefCell::new(point);
        self.witness_map.insert(addres, value);
    }


    pub fn ram_permutation_entry_point<CS: ConstraintSystem<E>, R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>>(&self, cs: &mut CS, round_function: &R) -> Result<(), SynthesisError>{
        
        let size = self.block.len();
        let permutation = Self::calculate_permutation(&self.block);
        let permutation = if let Some(permutation) = permutation {
            permutation
        } else {
            IntegerPermutation::new(size)
        };
        use plonk::circuit::bigint_new::compute_shifts;
        let shifts = compute_shifts::<E::Fr>();
        let mut original_values = vec![];
        let mut original_indexes = vec![];

        let mut sorted_values = vec![];
        let mut sorted_indexes = vec![];

        // let mut packed_left_colum = vec![];
        // let mut packed_right_colum = vec![];


        let mut vec_mul_left = vec![];
        let mut vec_mul_right = vec![];

        let mut unsorted_value_low = vec![];
        let mut unsorted_value_high = vec![];
        let mut sorted_value_low = vec![];
        let mut sorted_value_high = vec![];

        for (addr, value) in self.block.iter() {
            let value = value.clone();
            let x = FieldElement::into_limbs(value.clone().x.clone());

            let chunk = value.x.representation_params.binary_limbs_bit_widths[0];
            let iter = value.x.representation_params.binary_limbs_bit_widths.clone().into_iter();
            
            let chunk_x = 253 / chunk;
            let mut i = 0;
            let mut lc_low = LinearCombination::zero(); 
            for l in 0..chunk_x{
                lc_low.add_assign_number_with_coeff(&x[l].num, shifts[i]);
                i+= iter.clone().next().unwrap();

            }
            let value_low = lc_low.into_num(cs)?;
            let mut lc_high = LinearCombination::zero();
            i = 0;
            for l in chunk_x..x.len(){
                lc_high.add_assign_number_with_coeff(&x[l].num, shifts[i]);
                i+= iter.clone().next().unwrap();
            }

            let (odd_y, _) = value.clone().point_compression(cs)?;
            lc_high.add_assign_boolean_with_coeff(&odd_y, shifts[i]);  // point compression
            i+= 1;
            lc_high.add_assign_number_with_coeff(&addr, shifts[i]);

            let value_high = lc_high.into_num(cs)?;
            original_values.push(value);
            original_indexes.push(addr);
            unsorted_value_low.push(value_low);
            unsorted_value_high.push(value_high);
        }

        for index in permutation.elements.iter() {
            let value = original_values[*index].clone();
            let addr = original_indexes[*index].clone();
            sorted_values.push(value.x.clone());
            sorted_indexes.push(addr.clone());

            let value_from_sorted = value.clone();
            let x = FieldElement::into_limbs(value_from_sorted.clone().x.clone());

            let chunk = value_from_sorted.x.representation_params.binary_limbs_bit_widths[0];
            let iter = value_from_sorted.x.representation_params.binary_limbs_bit_widths.clone().into_iter();
            
            let chunk_x = 253 / chunk;
            let mut i = 0;
            let mut lc_low = LinearCombination::zero(); 
            for l in 0..chunk_x{
                lc_low.add_assign_number_with_coeff(&x[l].num, shifts[i]);
                i+= iter.clone().next().unwrap();

            }
            let value_low_sorted = lc_low.into_num(cs)?;
            i=0;

            let mut lc_high = LinearCombination::zero();
            for l in chunk_x..x.len(){
                lc_high.add_assign_number_with_coeff(&x[l].num, shifts[i]);
                i+= iter.clone().next().unwrap();
            }

            let (odd_y, _) = value_from_sorted.clone().point_compression(cs)?;
            lc_high.add_assign_boolean_with_coeff(&odd_y, shifts[i]);  // point compression
            i+= 1;

            lc_high.add_assign_number_with_coeff(&addr, shifts[i]);

            let value_high_sorted = lc_high.into_num(cs)?;
            sorted_value_low.push(value_low_sorted);
            sorted_value_high.push(value_high_sorted);

        }

        let mut array_for_len_hash = vec![];
        for left_unsort in unsorted_value_low.clone().into_iter(){
            array_for_len_hash.push(left_unsort);
        }
        for left_sort in sorted_value_low.clone().into_iter(){
            array_for_len_hash.push(left_sort);
        }

        for right_unsort in unsorted_value_high.clone().into_iter(){
            array_for_len_hash.push(right_unsort);
        }
        for right_sort in sorted_value_high.clone().into_iter(){
            array_for_len_hash.push(right_sort);
        }

        let state1 = variable_length_absorb_into_empty_state(cs, &array_for_len_hash, round_function)?;
        let chaleng_a = R::state_into_commitment(state1)?;
        let state2 = variable_length_absorb_into_state(cs, &[], &state1, round_function)?;
        let chaleng_b = R::state_into_commitment(state2)?;

        let mut minus_one = E::Fr::one();
        minus_one.negate();

        for (value_unsorted_low, value_unsorted_high) in unsorted_value_low.iter().zip(unsorted_value_high.iter()){
            let mut left_polinom = LinearCombination::zero(); 
            left_polinom.add_assign_number_with_coeff(&chaleng_a.clone(), E::Fr::one());
            left_polinom.add_assign_number_with_coeff(&value_unsorted_low, minus_one);
            let b_mul_chalenge = value_unsorted_high.mul(cs, &chaleng_b)?;
            left_polinom.add_assign_number_with_coeff(&b_mul_chalenge, minus_one);
            let multiplier= left_polinom.into_num(cs)?;
            vec_mul_left.push(multiplier);
        }

        for (value_sorted_low, value_sorted_high) in sorted_value_low.iter().zip(sorted_value_high.iter()){
            let mut right_polinom = LinearCombination::zero(); 
            right_polinom.add_assign_number_with_coeff(&chaleng_a.clone(), E::Fr::one());
            right_polinom.add_assign_number_with_coeff(&value_sorted_low, minus_one);
            let b_mul_chalenge = value_sorted_high.mul(cs, &chaleng_b)?;
            right_polinom.add_assign_number_with_coeff(&b_mul_chalenge, minus_one);
            let multiplier_other= right_polinom.into_num(cs)?;
            vec_mul_right.push(multiplier_other);
        }

        let mut left_polinom = Num::Constant(E::Fr::one());
        let mut right_polinom = Num::Constant(E::Fr::one());
        for (right, left) in vec_mul_right.iter().zip(vec_mul_left.iter()){
            left_polinom = left_polinom.mul(cs, left)?;
            right_polinom = right_polinom.mul(cs, right)?;
        }
        left_polinom.enforce_equal(cs, &right_polinom)?;

        Ok(())

    }
    pub fn waksman_permutation<CS: ConstraintSystem<E>>(&self, cs: &mut CS, window: usize) -> Result<(), SynthesisError>{

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

        use plonk::circuit::bigint_new::compute_shifts;
        let shifts = compute_shifts::<E::Fr>();
        let mut original_values = vec![];
        let mut original_indexes = vec![];
        // let mut original_addres = vec![];

        let mut sorted_values = vec![];
        let mut sorted_indexes = vec![];
        // let mut original_addres = vec![];
        

        let mut packed_original_values = vec![];
        let mut packed_sorted_values = vec![];


        for (addr, value ) in self.block.iter() {

            let value = value.clone();
            let x = FieldElement::into_limbs(value.clone().x.clone());

            let chunk = value.x.representation_params.binary_limbs_bit_widths[0];
            let iter = value.x.representation_params.binary_limbs_bit_widths.clone().into_iter();
            
            let chunk_x = 253 / chunk;
            let mut i = 0;
            let mut lc_low = LinearCombination::zero(); 
            for l in 0..chunk_x{
                lc_low.add_assign_number_with_coeff(&x[l].num, shifts[i]);
                i+= iter.clone().next().unwrap();

            }
            let value_low = lc_low.into_num(cs)?.get_variable();
            i=0;

            let mut lc_high = LinearCombination::zero();
            for l in chunk_x..x.len(){
                lc_high.add_assign_number_with_coeff(&x[l].num, shifts[i]);
                i+= iter.clone().next().unwrap();
            }
            let (odd_y, _) = value.clone().point_compression(cs)?;
            lc_high.add_assign_boolean_with_coeff(&odd_y, shifts[i]);  // point compression
            i+= 1;

            lc_high.add_assign_number_with_coeff(&addr, shifts[i]);

            let value_high = lc_high.into_num(cs)?.get_variable();

            packed_original_values.push([value_low, value_high]);
            original_values.push(value);
            original_indexes.push(addr);

        }

        for index in permutation.elements.iter() {

            let value = original_values[*index].clone();
            let addr = original_indexes[*index].clone();
            sorted_values.push(value.x.clone());
            sorted_indexes.push(addr.clone());

            let value = value.clone();
            let x = FieldElement::into_limbs(value.clone().x.clone());

            let chunk = value.x.representation_params.binary_limbs_bit_widths[0];
            let iter = value.x.representation_params.binary_limbs_bit_widths.clone().into_iter();
            
            let chunk_x = 253 / chunk;
            let mut i = 0;
            let mut lc_low = LinearCombination::zero(); 
            for l in 0..chunk_x{
                lc_low.add_assign_number_with_coeff(&x[l].num, shifts[i]);
                i+= iter.clone().next().unwrap();

            }
            let value_low = lc_low.into_num(cs)?.get_variable();
            i=0;

            let mut lc_high = LinearCombination::zero();
            for l in chunk_x..x.len(){
                lc_high.add_assign_number_with_coeff(&x[l].num, shifts[i]);
                i+= iter.clone().next().unwrap();
            }

            let (odd_y, _) = value.clone().point_compression(cs)?;
            lc_high.add_assign_boolean_with_coeff(&odd_y, shifts[i]);  // point compression
            i+= 1;

            lc_high.add_assign_number_with_coeff(&addr, shifts[i]);

            let value_high = lc_high.into_num(cs)?.get_variable();

            packed_sorted_values.push([value_low, value_high]);

        }
        let o0: Vec<_> = packed_original_values.iter().map(|el| el[0]).collect();
        let o1: Vec<_> = packed_original_values.into_iter().map(|el| el[1]).collect();
        let s0: Vec<_> = packed_sorted_values.clone().iter().map(|el| el[0]).collect();
        let s1: Vec<_> = packed_sorted_values.clone().into_iter().map(|el| el[1]).collect();

        prove_permutation_using_switches_witness(
            cs, 
            &s0,
            &o0,
            &switches
        )?;

        prove_permutation_using_switches_witness(
            cs, 
            &s1,
            &o1,
            &switches
        )?;

        use plonk::circuit::utils::u64_to_fe;
        let mut lc_count = LinearCombination::<E>::zero(); 
        let bit_window = (2 as u64).pow(window as u32);
        // let constanta = bit_window_decompose(window)*bit_window_decompose(window);
        let constanta =  bit_window * bit_window-1;
        let constant = Num::Constant(u64_to_fe(constanta as u64));
        lc_count.add_assign_number_with_coeff(&constant, E::Fr::one());
        let mut pre_value_1 = packed_sorted_values[0][0].clone();
        let mut pre_value_2= packed_sorted_values[0][1].clone();
        let mut minus_one = E::Fr::one();
        minus_one.negate();
        for i in packed_sorted_values.into_iter(){
            let is_equal_1 = AllocatedNum::equals(cs, &pre_value_1, &i[0])?;
            let is_equal_2 = AllocatedNum::equals(cs, &pre_value_2, &i[1])?;
            let condition = Boolean::and(cs, &is_equal_1, &is_equal_2)?;
            let count = Num::mask(cs, &Num::Constant(E::Fr::one()), &condition.not())?;
            lc_count.add_assign_number_with_coeff(&count, minus_one);
            pre_value_1 = i[0];
            pre_value_2 = i[1];
        }

        lc_count.enforce_zero(cs)?;

        Ok(())

    }

    fn calculate_permutation(row: &Vec<(Num<E>, AffinePoint<'a, E, G>)>) -> Option<IntegerPermutation> {
        
        let mut keys = vec![];
        for (addr, _) in row.iter() {
            let addres = fe_to_biguint(&addr.get_value().unwrap());
            let idx = keys.len();
            keys.push((idx, addres));
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
    use plonk::circuit::tables::inscribe_combined_bitwise_ops_and_range_table;

    #[test]
    fn test_ram_waksman() {
        
        use rand::{Rng, SeedableRng, XorShiftRng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

        let mut ram = Memory::new();
        let mut vec_verif = vec![];
        let mut cs = TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();
        inscribe_combined_bitwise_ops_and_range_table(&mut cs, 8).unwrap();
        let mut array_addr = vec![];
        for _ in 0..100 {

            let a_f: G1Affine = rng.gen();
            let a_fr: Fr = rng.gen();

            let a = AffinePoint::alloc(&mut cs, Some(a_f), &params).unwrap();
            let num_adr =Num::alloc(&mut cs, Some(a_fr)).unwrap();
            array_addr.push(num_adr);


            vec_verif.push(a.clone());

            ram.block.push((num_adr, a.clone()));
            let biguint = fe_to_biguint(&a_fr);
            ram.witness_map.insert(biguint, RefCell::new(a.clone())); 
        }
        for j in 0..1{
            let addres = array_addr[j];
            
            let _point = ram.read_and_alloc(&mut cs, addres, &params).unwrap();
            // assert_eq!(vec_verif[j].value.unwrap(), point.value.unwrap());

            
        }

        ram.waksman_permutation(&mut cs, 2);

    }
    #[test]
    fn test_ram_hash_permut() {
        
        use rand::{Rng, SeedableRng, XorShiftRng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

        let mut ram = Memory::new();
        let mut vec_verif = vec![];
        let mut cs = TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();
        inscribe_combined_bitwise_ops_and_range_table(&mut cs, 8).unwrap();
        let mut array_addr = vec![];
        for _ in 0..100 {

            let a_f: G1Affine = rng.gen();
            let a_fr: Fr = rng.gen();

            let a = AffinePoint::alloc(&mut cs, Some(a_f), &params).unwrap();
            let num_adr =Num::alloc(&mut cs, Some(a_fr)).unwrap();
            array_addr.push(num_adr);


            vec_verif.push(a.clone());

            ram.block.push((num_adr, a.clone()));
            let biguint = fe_to_biguint(&a_fr);
            ram.witness_map.insert(biguint, RefCell::new(a.clone())); 
        }
        for j in 0..100{
            let addres = array_addr[j];
            
            let point = ram.read_and_alloc(&mut cs, addres, &params).unwrap();
            println!("{:?}", point);
            // assert_eq!(vec_verif[j].value.unwrap(), point.value.unwrap());

            
        }
        const RATE: usize = 2;
        const WIDTH: usize = 3;
        const INPUT_LENGTH: usize = 1;
        use plonk::circuit::rescue_copy::sponge::GenericSponge;
        use plonk::circuit::rescue_copy::rescue::params::RescueParams;
        // let mut params = crate::utils::bn254_rescue_params();
        let rescue_params = RescueParams::<Bn256, RATE, WIDTH>::default();
        let committer = GenericHasher::<Bn256, RescueParams<Bn256, 2, 3>, 2, 3>::new_from_params(&rescue_params);
        ram.ram_permutation_entry_point(&mut cs, &committer);



    }
}