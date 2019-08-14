extern crate bit_vec;

use self::bit_vec::BitVec;

use bellman::pairing::{
    Engine,
};

use bellman::pairing::ff::{
    Field,
    PrimeField,
    PrimeFieldRepr
};

use bellman::{
    LinearCombination,
    SynthesisError,
    ConstraintSystem,
    Variable,
    Index
};

use std::collections::HashMap;
use std::fmt::Write;

use byteorder::{BigEndian, ByteOrder};
use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::collections::HashSet;

/// Constraint system for testing purposes.
pub struct DensityCountingTestConstraintSystem<E: Engine> {
    pub a_aux_density: DensityTracker,
    pub b_input_density: DensityTracker,
    pub b_aux_density: DensityTracker,
    pub constraints: usize,
    pub inputs: usize,
    pub aux: usize,

    _marker: std::marker::PhantomData<E>
}

fn eval_lc<E: Engine>(
    lc: &LinearCombination<E>,
    mut input_density: Option<&mut DensityTracker>,
    mut aux_density: Option<&mut DensityTracker>,
)
{
    for &(index, _) in lc.as_ref().iter() {
        match index.get_unchecked() {
            Index::Input(i) => {
                if let Some(ref mut v) = input_density {
                    v.inc(i);
                }
            },
            Index::Aux(i) => {
                if let Some(ref mut v) = aux_density {
                    v.inc(i);
                }
            }
        }
    }
}

impl<E: Engine> DensityCountingTestConstraintSystem<E> {
    pub fn new() -> DensityCountingTestConstraintSystem<E> {
        let mut this = DensityCountingTestConstraintSystem {
            a_aux_density: DensityTracker::new(),
            b_input_density: DensityTracker::new(),
            b_aux_density: DensityTracker::new(),
            constraints: 0,
            inputs: 0,
            aux: 0,

            _marker: std::marker::PhantomData
        };

        this.alloc_input(|| "", || Ok(E::Fr::one())).unwrap();

        this
    }
}

impl<E: Engine> ConstraintSystem<E> for DensityCountingTestConstraintSystem<E> {
    type Root = Self;

    fn alloc<F, A, AR>(
        &mut self,
        _: A,
        _: F
    ) -> Result<Variable, SynthesisError>
        where F: FnOnce() -> Result<E::Fr, SynthesisError>, A: FnOnce() -> AR, AR: Into<String>
    {
        let index = self.aux;
        let var = Variable::new_unchecked(Index::Aux(index));
        self.aux += 1;

        self.a_aux_density.add_element();
        self.b_aux_density.add_element();

        Ok(var)
    }

    fn alloc_input<F, A, AR>(
        &mut self,
        _: A,
        _: F
    ) -> Result<Variable, SynthesisError>
        where F: FnOnce() -> Result<E::Fr, SynthesisError>, A: FnOnce() -> AR, AR: Into<String>
    {
        let index = self.inputs;
        let var = Variable::new_unchecked(Index::Input(index));
        self.inputs += 1;

        self.b_input_density.add_element();

        Ok(var)
    }

    fn enforce<A, AR, LA, LB, LC>(
        &mut self,
        _: A,
        a: LA,
        b: LB,
        c: LC
    )
        where A: FnOnce() -> AR, AR: Into<String>,
              LA: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
              LB: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
              LC: FnOnce(LinearCombination<E>) -> LinearCombination<E>
    {
        self.constraints += 1;

        let a = a(LinearCombination::zero());
        let b = b(LinearCombination::zero());
        let c = c(LinearCombination::zero());

        eval_lc(
            &a,
            None,
            Some(&mut self.a_aux_density),
        );

        eval_lc(
            &b,
            Some(&mut self.b_input_density),
            Some(&mut self.b_aux_density),
        );

        eval_lc(
            &c,
            None,
            None,
        );

    }

    fn push_namespace<NR, N>(&mut self, name_fn: N)
    where NR: Into<String>, N: FnOnce() -> NR
    {

    }

    fn pop_namespace(&mut self)
    {

    }

    fn get_root(&mut self) -> &mut Self::Root
    {
        self
    }
}

#[derive(Clone)]
pub struct DensityTracker {
    bv: BitVec,
    total_density: usize
}

impl DensityTracker {
    pub fn new() -> DensityTracker {
        DensityTracker {
            bv: BitVec::new(),
            total_density: 0
        }
    }

    pub fn get_query_size(self) -> Option<usize> {
        Some(self.bv.len())
    }

    pub fn add_element(&mut self) {
        self.bv.push(false);
    }

    pub fn inc(&mut self, idx: usize) {
        if !self.bv.get(idx).unwrap() {
            self.bv.set(idx, true);
            self.total_density += 1;
        }
    }

    pub fn get_total_density(&self) -> usize {
        self.total_density
    }
}