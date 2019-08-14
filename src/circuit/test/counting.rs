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
pub struct CountingTestConstraintSystem<E: Engine> {
    pub constraints: usize,
    pub inputs: usize,
    pub aux: usize,

    _marker: std::marker::PhantomData<E>
}

fn eval_lc<E: Engine>(
    terms: &[(Variable, E::Fr)],
    inputs: &[(E::Fr, String)],
    aux: &[(E::Fr, String)]
) -> E::Fr
{
    let mut acc = E::Fr::zero();

    for &(var, ref coeff) in terms {
        let mut tmp = match var.get_unchecked() {
            Index::Input(index) => inputs[index].0,
            Index::Aux(index) => aux[index].0
        };

        tmp.mul_assign(&coeff);
        acc.add_assign(&tmp);
    }

    acc
}

impl<E: Engine> CountingTestConstraintSystem<E> {
    pub fn new() -> CountingTestConstraintSystem<E> {
        CountingTestConstraintSystem {
            constraints: 0,
            inputs: 1,
            aux: 0,

            _marker: std::marker::PhantomData
        }
    }
}

impl<E: Engine> ConstraintSystem<E> for CountingTestConstraintSystem<E> {
    type Root = Self;

    fn alloc<F, A, AR>(
        &mut self,
        _: A,
        f: F
    ) -> Result<Variable, SynthesisError>
        where F: FnOnce() -> Result<E::Fr, SynthesisError>, A: FnOnce() -> AR, AR: Into<String>
    {
        let index = self.aux;
        let var = Variable::new_unchecked(Index::Aux(index));
        self.aux += 1;

        f()?;

        Ok(var)
    }

    fn alloc_input<F, A, AR>(
        &mut self,
        _: A,
        f: F
    ) -> Result<Variable, SynthesisError>
        where F: FnOnce() -> Result<E::Fr, SynthesisError>, A: FnOnce() -> AR, AR: Into<String>
    {
        let index = self.inputs;
        let var = Variable::new_unchecked(Index::Input(index));
        self.inputs += 1;

        f()?;

        Ok(var)
    }

    fn enforce<A, AR, LA, LB, LC>(
        &mut self,
        _: A,
        _: LA,
        _: LB,
        _: LC
    )
        where A: FnOnce() -> AR, AR: Into<String>,
              LA: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
              LB: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
              LC: FnOnce(LinearCombination<E>) -> LinearCombination<E>
    {
        self.constraints += 1;
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