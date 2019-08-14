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
pub struct DuplicateFinderTestConstraintSystem<E: Engine> {
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

impl<E: Engine> DuplicateFinderTestConstraintSystem<E> {
    pub fn new() -> DuplicateFinderTestConstraintSystem<E> {
        DuplicateFinderTestConstraintSystem {
            constraints: 0,
            inputs: 1,
            aux: 0,

            _marker: std::marker::PhantomData
        }
    }
}

impl<E: Engine> ConstraintSystem<E> for DuplicateFinderTestConstraintSystem<E> {
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

        Ok(var)
    }

    fn enforce<A, AR, LA, LB, LC>(
        &mut self,
        annotation: A,
        a: LA,
        b: LB,
        c: LC
    )
        where A: FnOnce() -> AR, AR: Into<String>,
              LA: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
              LB: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
              LC: FnOnce(LinearCombination<E>) -> LinearCombination<E>
    {
        fn check_unique<E: Engine>(
            l: LinearCombination<E>,
        ) -> Option<usize>
        {
            // let mut input_set = HashSet::new();
            let mut aux_set = HashSet::new();
            for (index, coeff) in l.as_ref().iter() {
                match index.get_unchecked() {
                    Index::Input(id) => {
                        // if let Some(idx) = input_set.get(&id) {
                        //     return Some(*idx);
                        // } else {
                        //     input_set.insert(id);
                        // }
                    },
                    Index::Aux(id) => {
                        if let Some(idx) = aux_set.get(&id) {
                            if id != 0 {
                                return Some(*idx);
                            }
                        } else {
                            aux_set.insert(id);
                        }
                    }
                }
            }

            None
        }

        let ann: String = annotation().into();

        if ann != "x3 computation" 
            && ann != "y-coordinate lookup" 
            && ann != "y3 computation" 
            && ann != "xor constraint"
            && ann != "maj computation" {
            if let Some(non_unique) = check_unique(a(LinearCombination::zero())) {
                println!("Non-unique term with variable (most likely auxilary) {} in constraint in A with name ending as {}", non_unique, ann);
            }
            if let Some(non_unique) = check_unique(b(LinearCombination::zero())) {
                println!("Non-unique term with variable (most likely auxilary) {} in constraint in B with name ending as {}", non_unique, ann);
            }
            if let Some(non_unique) = check_unique(c(LinearCombination::zero())) {
                println!("Non-unique term with variable (most likely auxilary) {} in constraint in C with name ending as {}", non_unique, ann);
            }
        }

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