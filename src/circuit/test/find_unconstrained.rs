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
#[derive(Debug)]
pub struct ConstraintVerifyingTestConstraintSystem<E: Engine> {
    pub constraints: usize,
    pub inputs: usize,
    pub aux: usize,

    pub set: HashSet<usize>,

    _marker: std::marker::PhantomData<E>
}

fn eval_lc<E: Engine>(
    set: &mut HashSet<usize>,
    terms: &[(Variable, E::Fr)],
)
{
    for &(var, _) in terms {
        match var.get_unchecked() {
            Index::Aux(idx) => {
                set.remove(&idx);
            },
            _ => {

            }
        }
    }
}

impl<E: Engine> ConstraintVerifyingTestConstraintSystem<E> {
    pub fn new() -> ConstraintVerifyingTestConstraintSystem<E> {
        ConstraintVerifyingTestConstraintSystem {
            constraints: 0,
            inputs: 1,
            aux: 0,
            set: HashSet::new(),

            _marker: std::marker::PhantomData
        }
    }

    pub fn is_fully_constrained(&self) -> bool {
        if self.set.len() != 0 {
            println!("Unconstrained set: {:?}", self.set);

            return false;
        }
        
        true
    }
}

impl<E: Engine> ConstraintSystem<E> for ConstraintVerifyingTestConstraintSystem<E> {
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
        self.set.insert(index);
        self.aux += 1;

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
        // self.set.insert(var);

        self.inputs += 1;

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

        eval_lc::<E>(&mut self.set, a.as_ref());
        eval_lc::<E>(&mut self.set, b.as_ref());
        eval_lc::<E>(&mut self.set, c.as_ref());
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