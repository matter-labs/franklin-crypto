use super::*;


use crate::bellman::plonk::better_better_cs::cs::{Variable, Index, ConstraintSystem};
use crate::bellman::pairing::{Engine, GenericCurveAffine, GenericCurveProjective};
use plonk::circuit::{boolean::Boolean, SynthesisError, allocated_num::AllocatedNum, smart_op::* };
use plonk::circuit::simple_term::Term;
use itertools::partition;
use bellman::PrimeField;
use plonk::circuit::curve::point_ram::CircuitArithmeticRoundFunction;
use plonk::circuit::utils::u64_to_fe;
use plonk::circuit::curve::structual_eq::CircuitSelectable;
use plonk::circuit::curve::point_ram::can_not_be_false_if_flagged;
use plonk::circuit::curve::structual_eq::CircuitEq;
use super::super::allocated_num::*;
use plonk::circuit::rescue_copy::traits::HashParams;
use plonk::circuit::rescue_copy::sponge::GenericSponge;

// #[derive(Derivative)]
// #[derivative(Clone, Debug)]
#[derive(Clone, Debug)]
pub struct Sponge<
    E: Engine, 
    R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH>,
    const AWIDTH: usize,
    const SWIDTH: usize
>{
    // #[derivative(Debug="ignore")]
    pub(crate) round_function: R,
    // #[derivative(Debug="ignore")]
    pub(crate) state: [R::StateElement; SWIDTH]
}

impl<
    E: Engine, 
    R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    const AWIDTH: usize,
    const SWIDTH: usize
>Sponge<E, R, AWIDTH, SWIDTH>{
    pub fn new(round_function: R) -> Self {
        Self {
            round_function,
            state: R::empty_state()
        }
    }

    pub fn specialize_for_length<CS: ConstraintSystem<E>>(
        &mut self,
        _cs: &mut CS,
        length: usize
    ) -> Result<(), SynthesisError> {
        assert!(AWIDTH < SWIDTH);
        assert!(self.state.eq(&R::empty_state()));

        let idx = SWIDTH - 1;
        self.state[idx] = Num::Constant(u64_to_fe(length as u64));

        Ok(())
    }

    pub fn absorb_single_round_nums<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        values: &[Num<E>]
    ) -> Result<(), SynthesisError> {
        assert!(AWIDTH < SWIDTH);
        assert_eq!(values.len(), AWIDTH);

        let mut state = self.state;
        for (inp, s) in values.iter().zip(state.iter_mut()) {
            *s = s.add(cs, inp)?;
        }
        let state = self.round_function.round_function(cs, state)?;
        self.state = state;

        Ok(())
    }

    // pub fn absorb_multiple_with_optimizer<CS: ConstraintSystem<E>, const N: usize>(
    //     &mut self,
    //     cs: &mut CS,
    //     id: u64,
    //     values: &[Num<E>; N],
    //     execute: &Boolean,
    //     optimizer: &mut SpongeOptimizer<E, R, AWIDTH, SWIDTH>
    // ) -> Result<(), SynthesisError> {
    //     use crate::glue::optimizable_queue::fixed_width_hash_into_state_using_optimizer;
        
    //     self.state = fixed_width_hash_into_state_using_optimizer(
    //         cs,
    //         values,
    //         id,
    //         *execute,
    //         optimizer
    //     )?;

    //     Ok(())
    // }

    pub fn squeeze_single(&self) -> Result<Num<E>, SynthesisError> {
        R::state_into_commitment(self.state)
    }
}

impl<
    E: Engine, 
    R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    const AWIDTH: usize,
    const SWIDTH: usize
> CircuitSelectable<E> for Sponge<E, R, AWIDTH, SWIDTH>{
    fn conditionally_select<CS: ConstraintSystem<E>>(cs: &mut CS, flag: &Boolean, a: &Self, b: &Self) -> Result<Self, SynthesisError> {
        let mut new = a.clone();
        assert!(a.round_function == b.round_function);

        for ((a, b), r) in a.state.iter().zip(b.state.iter()).zip(new.state.iter_mut()) {
            *r = Num::conditionally_select(cs, flag, a, b)?;
        }

        Ok(new)
    }
}
// #[derive(Derivative)]
#[derive(Clone, Debug)]
pub struct SpongeRoundRequest<
    E: Engine,
    const AWIDTH: usize,
    const SWIDTH: usize,
>{
    pub initial_state: [Num<E>; SWIDTH],
    pub values_to_absorb: [Num<E>; AWIDTH],
    pub claimed_final_state: [Num<E>; SWIDTH],
    pub feed_forward: Boolean,
}

impl<
    E: Engine,
    const AWIDTH: usize,
    const SWIDTH: usize,
> Copy for SpongeRoundRequest<E, AWIDTH, SWIDTH> {}

impl<
    E: Engine,
    const AWIDTH: usize,
    const SWIDTH: usize,
> CircuitSelectable<E> for SpongeRoundRequest<E, AWIDTH, SWIDTH> {
    fn conditionally_select<CS: ConstraintSystem<E>>(cs: &mut CS, flag: &Boolean, a: &Self, b: &Self) -> Result<Self, SynthesisError> {
        let mut new = *a;
        for ((a, b), r) in a.initial_state.iter().zip(b.initial_state.iter()).zip(new.initial_state.iter_mut()) {
            *r = Num::conditionally_select(cs, flag, a, b)?;
        }
        for ((a, b), r) in a.values_to_absorb.iter().zip(b.values_to_absorb.iter()).zip(new.values_to_absorb.iter_mut()) {
            *r = Num::conditionally_select(cs, flag, a, b)?;
        }
        for ((a, b), r) in a.claimed_final_state.iter().zip(b.claimed_final_state.iter()).zip(new.claimed_final_state.iter_mut()) {
            *r = Num::conditionally_select(cs, flag, a, b)?;
        }
        new.feed_forward = Boolean::conditionally_select(cs, flag, &a.feed_forward, &b.feed_forward)?;

        Ok(new)
    }
}

pub struct SpongeOptimizer<
    E: Engine, 
    R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH>,
    const AWIDTH: usize,
    const SWIDTH: usize,
>{
    pub(crate) round_function: R,
    pub(crate) requests: std::collections::HashMap<u64, Vec<(SpongeRoundRequest<E, AWIDTH, SWIDTH>, Boolean)>>,
    pub(crate) limit: usize,
    pub(crate) _marker: std::marker::PhantomData<E>
}

impl<
    E: Engine, 
    R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    const AWIDTH: usize,
    const SWIDTH: usize
> SpongeOptimizer<E, R, AWIDTH, SWIDTH> {
    pub fn new(round_function: R, limit: usize) -> Self {
        Self {
            round_function,
            requests: std::collections::HashMap::new(),
            limit,
            _marker: std::marker::PhantomData
        }
    }

    pub fn capacity(&self) -> usize {
        self.limit
    }

    pub fn add_request(
        &mut self, 
        request: SpongeRoundRequest<E, AWIDTH, SWIDTH>,
        applies: Boolean,
        id: u64
    ) {
        if let Some(existing_vector) = self.requests.get_mut(&id) {
            assert!(existing_vector.len() < self.limit, "over capacity: capacity is {}", self.limit);
            existing_vector.push((request, applies));
        } else {
            let vector = vec![(request, applies)];
            self.requests.insert(id, vector);
        }
    }

    pub fn enforce<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<(), SynthesisError> {
        let mut layout = vec![];
        let mut keys: Vec<_> = self.requests.keys().cloned().collect();
        keys.sort();
        for _ in 0..self.limit {
            let mut per_round_requests = vec![];
            for k in keys.iter() {
                let requests_per_id = self.requests.get_mut(k).expect("is some");
                if !requests_per_id.is_empty() {
                    let el = requests_per_id.drain(0..1).next().expect("is some");
                    per_round_requests.push(el);
                }
            }

            let len = per_round_requests.len();
            if len > 1 {
                let mut applicability_flags = vec![];
                let mut it = per_round_requests.into_iter();
                let (item, execute) = (&mut it).next().expect("is some");
                applicability_flags.push(execute);
                let mut current = item;
                for el in it.into_iter() {
                    let (el, flag) = el;
                    current = SpongeRoundRequest::conditionally_select(cs, &flag, &el, &current)?;
                    applicability_flags.push(flag);
                }
                // this is kind of debug assert
                let mut encountered_true = false;
                for f in applicability_flags.iter() {
                    if let Some(f) = f.get_value() {
                        if f {
                            if encountered_true {
                                panic!("not exclusive branches in optimizer")
                            } else {
                                encountered_true = true;
                            }
                        }
                    }
                }
                let applies = smart_or(cs, &applicability_flags)?;
                layout.push((current, applies));
            } else if len == 1 {
                layout.push(per_round_requests[0]);
            }
        }
        self.requests.clear();

        assert!(layout.len() <= self.limit);
        let mut last_state = None;
        for (l, applies) in layout.into_iter() {
            // first select over empty and claimed initial state
            let mut initial_state = l.initial_state;
            if let Some((state, feed)) = last_state.take() {
                initial_state = <[Num::<E>; SWIDTH] as CircuitSelectable<E>>::conditionally_select(cs, &feed, &state, &initial_state)?;
            }
            let application_result = self.round_function.round_function_absorb_nums(cs, initial_state, &l.values_to_absorb)?;
            let mut eq_flags = vec![];
            for (res, claimed) in application_result.iter().zip(l.claimed_final_state.iter()) {
                let e = Num::equals(cs, res, claimed)?;
                eq_flags.push(e);
            }
            let eq = smart_and(cs, &eq_flags)?;
            can_not_be_false_if_flagged(cs, &eq, &applies)?;

            last_state = Some((application_result, l.feed_forward));
        }

        if let Some((_state, feed)) = last_state.take() {
            if let Some(feed) = feed.get_value() {
                assert_eq!(feed, false, "wants to feed further, but we did not");
            }
        }

        Ok(())
    }
}

impl<
    E: Engine, 
    R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH>,
    const AWIDTH: usize,
    const SWIDTH: usize
> Drop for SpongeOptimizer<E, R, AWIDTH, SWIDTH> {
    fn drop(&mut self) {
        assert!(self.requests.is_empty(), "requests were not enforced!");
    }
}

pub trait ArithmeticEncodable<E: Engine>: Clone + Send + Sync {
    fn encoding_length_is_constant() -> bool {
        true
    }
    fn encoding_length() -> usize;
    fn encode(&self) -> Result<Vec<E::Fr>, SynthesisError>;
    fn encoding_length_for_instance(&self) -> usize {
        if Self::encoding_length_is_constant() {
            Self::encoding_length()
        } else {
            unimplemented!()
        }
    }
}

pub trait ArithmeticDecodable<E: Engine>: Clone + Send + Sync {
    fn parse(values: &[E::Fr]) -> Result<Self, SynthesisError>;
}

pub trait FixedLengthEncodable<E: Engine, const N: usize>: Clone + std::fmt::Debug{
    fn encode(&self) -> [E::Fr; N];
    fn placeholder() -> Self;
}

pub trait FixedLengthDecodable<E: Engine, const N: usize>: Clone + Send + Sync {
    fn parse(values: &[E::Fr; N]) -> Self;
    fn parse_conditionally(values: &[E::Fr; N], should_execute: bool) -> Self;
}

pub trait ArithmeticCommitter<E: Engine>: Clone + Send + Sync {
    fn commit(&self, values: &[E::Fr]) -> Result<Vec<E::Fr>, SynthesisError>;
}

#[derive(serde::Serialize, serde::Deserialize)]
#[derive(Clone, Debug)]
#[serde(bound = "")]
pub struct GenericHasher<E: Engine, P: HashParams<E, AWIDTH, SWIDTH>, const AWIDTH: usize, const SWIDTH: usize> {
    pub(crate) params: P,
    #[serde(skip)]
    _m : std::marker::PhantomData<E>,
}

impl<E: Engine, P: HashParams<E, AWIDTH, SWIDTH>, const AWIDTH: usize, const SWIDTH: usize> std::cmp::PartialEq for GenericHasher<E, P, AWIDTH, SWIDTH> {
    fn eq(&self, other: &Self) -> bool {
        self.params.hash_family() == other.params.hash_family()
    }
}

impl<E: Engine, P: HashParams<E, AWIDTH, SWIDTH>, const AWIDTH: usize, const SWIDTH: usize> std::cmp::Eq for GenericHasher<E, P, AWIDTH, SWIDTH> {}

impl<E: Engine, P: HashParams<E, AWIDTH, SWIDTH>, const AWIDTH: usize, const SWIDTH: usize> GenericHasher<E, P, AWIDTH, SWIDTH> {
    pub fn new_from_params(params: &P) -> Self {
        Self {
            params: params.clone(),
            _m: std::marker::PhantomData,
        }
    }
}

impl<E: Engine, P: HashParams<E, AWIDTH, SWIDTH>, const AWIDTH: usize, const SWIDTH: usize> ArithmeticCommitter<E> for GenericHasher<E, P, AWIDTH, SWIDTH> {
    fn commit(&self, values: &[E::Fr]) -> Result<Vec<E::Fr>, SynthesisError> {
        let output = GenericSponge::hash(values, &self.params, None).to_vec();

        Ok(output)
    }
}

pub trait ArithmeticCommitable<E: Engine>: ArithmeticEncodable<E> {
    fn commit<C: ArithmeticCommitter<E>>(&self, committer: &C) -> Result<E::Fr, SynthesisError> {
        let encoding = self.encode()?;
        let result = committer.commit(&encoding)?;

        Ok(result[0])
    }
}
