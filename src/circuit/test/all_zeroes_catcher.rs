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
pub struct ZeroCatchingTestConstraintSystem<E: Engine> {
    at_inputs: Vec<Vec<(E::Fr, usize)>>,
    bt_inputs: Vec<Vec<(E::Fr, usize)>>,
    ct_inputs: Vec<Vec<(E::Fr, usize)>>,
    at_aux: Vec<Vec<(E::Fr, usize)>>,
    bt_aux: Vec<Vec<(E::Fr, usize)>>,
    ct_aux: Vec<Vec<(E::Fr, usize)>>,
    pub constraints: usize,
    pub inputs: usize,
    pub aux: usize,

    _marker: std::marker::PhantomData<E>
}

fn find<E: Engine>(
    aux: &[Vec<(E::Fr, usize)>]
) -> HashSet<usize> {
    let zero = E::Fr::zero();
    let mut result = HashSet::new();
    // iterate over all columns
    for (idx, var) in aux.iter().enumerate() {
        let mut found_non_zero = false;
        // iterate over all the coefficients in different constraints
        for (coeff, _) in var.iter() {
            if *coeff != zero {
                found_non_zero = true;
                break;
            }
        }

        if !found_non_zero {
            result.insert(idx);
        }
    }

    result
}

fn find_in_multiple_only<E: Engine>(
    aux: &[Vec<(E::Fr, usize)>]
) -> HashSet<usize> {
    let zero = E::Fr::zero();
    let mut result = HashSet::new();
    // iterate over all columns
    for (idx, var) in aux.iter().enumerate() {
        if var.len() == 0 {
            continue;
        }
        let mut found_non_zero = false;
        // iterate over all the coefficients in different constraints
        for (coeff, _) in var.iter() {
            if *coeff != zero {
                found_non_zero = true;
                break;
            }
        }

        if !found_non_zero {
            result.insert(idx);
        }
    }

    result
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

impl<E: Engine> ZeroCatchingTestConstraintSystem<E> {
    pub fn new() -> ZeroCatchingTestConstraintSystem<E> {
        let mut this = ZeroCatchingTestConstraintSystem {
            at_inputs: vec![],
            bt_inputs: vec![],
            ct_inputs: vec![],
            at_aux: vec![],
            bt_aux: vec![],
            ct_aux: vec![],
            constraints: 0,
            inputs: 0,
            aux: 0,

            _marker: std::marker::PhantomData
        };

        this.alloc_input(|| "", || Ok(E::Fr::one())).unwrap();

        this
    }

    pub fn check_for_zero_columns_inputs(&self) -> HashSet<usize> {
        let mut result: HashSet<usize> = HashSet::new();
        result.extend(find::<E>(&self.at_inputs));

        let result: HashSet<usize> = result.intersection(&find::<E>(&self.bt_inputs)).map(|el| *el).collect();
        let result: HashSet<usize> = result.intersection(&find::<E>(&self.ct_inputs)).map(|el| *el).collect();

        result
    }

    pub fn check_for_zero_columns_aux(&self) -> HashSet<usize> {
        let mut result = HashSet::new();
        result.extend(find::<E>(&self.at_aux));

        let result: HashSet<usize> = result.intersection(&find::<E>(&self.bt_aux)).map(|el| *el).collect();
        let result: HashSet<usize> = result.intersection(&find::<E>(&self.ct_aux)).map(|el| *el).collect();

        result
    }

    pub fn check_for_zero_columns_aux_in_a(&self) -> HashSet<usize> {
        find::<E>(&self.at_aux)
    }

    pub fn check_for_zero_columns_aux_in_a_multiple_only(&self) -> HashSet<usize> {
        find_in_multiple_only::<E>(&self.at_aux)
    }

    pub fn check_for_zero_columns_aux_in_a_and_b(&self) -> HashSet<usize> {
        let mut result = HashSet::new();
        result.extend(find::<E>(&self.at_aux));

        let result: HashSet<usize> = result.intersection(&find::<E>(&self.bt_aux)).map(|el| *el).collect();

        result
    }

    pub fn check_for_zero_columns_aux_in_a_and_c(&self) -> HashSet<usize> {
        let mut result = HashSet::new();
        result.extend(find::<E>(&self.at_aux));

        let result: HashSet<usize> = result.intersection(&find::<E>(&self.ct_aux)).map(|el| *el).collect();

        result
    }

    pub fn check_for_zero_columns_aux_in_b_and_c(&self) -> HashSet<usize> {
        let mut result = HashSet::new();
        result.extend(find::<E>(&self.bt_aux));

        let result: HashSet<usize> = result.intersection(&find::<E>(&self.ct_aux)).map(|el| *el).collect();

        result
    }
}

impl<E: Engine> ConstraintSystem<E> for ZeroCatchingTestConstraintSystem<E> {
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

        self.at_aux.push(vec![]);
        self.bt_aux.push(vec![]);
        self.ct_aux.push(vec![]);

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

        self.at_inputs.push(vec![]);
        self.bt_inputs.push(vec![]);
        self.ct_inputs.push(vec![]);

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

        fn eval<E: Engine>(
            l: LinearCombination<E>,
            inputs: &mut [Vec<(E::Fr, usize)>],
            aux: &mut [Vec<(E::Fr, usize)>],
            this_constraint: usize
        )
        {
            for (index, coeff) in l.as_ref().iter() {
                match index.get_unchecked() {
                    Index::Input(id) => inputs[id].push((*coeff, this_constraint)),
                    Index::Aux(id) => aux[id].push((*coeff, this_constraint))
                }
            }
        }

        eval(a(LinearCombination::zero()), &mut self.at_inputs, &mut self.at_aux, self.constraints);
        eval(b(LinearCombination::zero()), &mut self.bt_inputs, &mut self.bt_aux, self.constraints);
        eval(c(LinearCombination::zero()), &mut self.ct_inputs, &mut self.ct_aux, self.constraints);

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