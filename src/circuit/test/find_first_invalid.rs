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

use blake2_rfc::blake2s::Blake2s;

#[derive(Debug)]
enum NamedObject {
    Constraint(usize),
    Var(Variable),
    Namespace
}

/// Constraint system for testing purposes.
pub struct FindFirstInvalidConstraintSystem<E: Engine> {
    named_objects: HashMap<String, NamedObject>,
    current_namespace: Vec<String>,
    num_constraints: usize,
    found_error: Option<String>,
    inputs: Vec<(E::Fr, String)>,
    aux: Vec<(E::Fr, String)>
}

#[derive(Clone, Copy)]
struct OrderedVariable(Variable);

impl Eq for OrderedVariable {}
impl PartialEq for OrderedVariable {
    fn eq(&self, other: &OrderedVariable) -> bool {
        match (self.0.get_unchecked(), other.0.get_unchecked()) {
            (Index::Input(ref a), Index::Input(ref b)) => a == b,
            (Index::Aux(ref a), Index::Aux(ref b)) => a == b,
            _ => false
        }
    }
}
impl PartialOrd for OrderedVariable {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for OrderedVariable {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self.0.get_unchecked(), other.0.get_unchecked()) {
            (Index::Input(ref a), Index::Input(ref b)) => a.cmp(b),
            (Index::Aux(ref a), Index::Aux(ref b)) => a.cmp(b),
            (Index::Input(_), Index::Aux(_)) => Ordering::Less,
            (Index::Aux(_), Index::Input(_)) => Ordering::Greater
        }
    }
}

fn proc_lc<E: Engine>(
    terms: &[(Variable, E::Fr)],
) -> BTreeMap<OrderedVariable, E::Fr>
{
    let mut map = BTreeMap::new();
    for &(var, coeff) in terms {
        map.entry(OrderedVariable(var))
           .or_insert(E::Fr::zero())
           .add_assign(&coeff);
    }

    // Remove terms that have a zero coefficient to normalize
    let mut to_remove = vec![];
    for (var, coeff) in map.iter() {
        if coeff.is_zero() {
            to_remove.push(*var)
        }
    }

    for var in to_remove {
        map.remove(&var);
    }

    map
}

fn hash_lc<E: Engine>(
    terms: &[(Variable, E::Fr)],
    h: &mut Blake2s
)
{
    let map = proc_lc::<E>(terms);

    let mut buf = [0u8; 9 + 32];
    BigEndian::write_u64(&mut buf[0..8], map.len() as u64);
    h.update(&buf[0..8]);

    for (var, coeff) in map {
        match var.0.get_unchecked() {
            Index::Input(i) => {
                buf[0] = b'I';
                BigEndian::write_u64(&mut buf[1..9], i as u64);
            },
            Index::Aux(i) => {
                buf[0] = b'A';
                BigEndian::write_u64(&mut buf[1..9], i as u64);
            }
        }
        
        coeff.into_repr().write_be(&mut buf[9..]).unwrap();

        h.update(&buf);
    }
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

impl<E: Engine> FindFirstInvalidConstraintSystem<E> {
    pub fn new() -> FindFirstInvalidConstraintSystem<E> {
        let mut map = HashMap::new();
        map.insert("ONE".into(), NamedObject::Var(FindFirstInvalidConstraintSystem::<E>::one()));

        FindFirstInvalidConstraintSystem {
            named_objects: map,
            current_namespace: vec![],
            num_constraints: 0,
            found_error: None,
            inputs: vec![(E::Fr::one(), "ONE".into())],
            aux: vec![]
        }
    }

    pub fn which_is_unsatisfied(&self) -> Option<&str> {
        if let Some(err) = self.found_error.as_ref() {
            Some(err)
        } else {
            None
        }
    }

    pub fn is_satisfied(&self) -> bool
    {
        self.which_is_unsatisfied().is_none()
    }

    pub fn num_constraints(&self) -> usize
    {
        self.num_constraints
    }

    pub fn num_inputs(&self) -> usize {
        self.inputs.len()
    }

    pub fn get_input(&mut self, index: usize, path: &str) -> E::Fr
    {
        let (assignment, name) = self.inputs[index].clone();

        assert_eq!(path, name);

        assignment
    }

    pub fn get(&mut self, path: &str) -> E::Fr
    {
        match self.named_objects.get(path) {
            Some(&NamedObject::Var(ref v)) => {
                match v.get_unchecked() {
                    Index::Input(index) => self.inputs[index].0,
                    Index::Aux(index) => self.aux[index].0
                }
            }
            Some(e) => panic!("tried to get value of path `{}`, but `{:?}` exists there (not a variable)", path, e),
            _ => panic!("no variable exists at path: {}", path)
        }
    }

    pub fn get_aux_name_by_index(&mut self, idx: usize) -> String
    {
        let (_, name) = &self.aux[idx];

        name.clone()
    }

    fn set_named_obj(&mut self, path: String, to: NamedObject) {
        if self.named_objects.contains_key(&path) {
            panic!("tried to create object at existing path: {}", path);
        }

        self.named_objects.insert(path, to);
    }
}

fn compute_path(ns: &[String], this: String) -> String {
    if this.chars().any(|a| a == '/') {
        panic!("'/' is not allowed in names");
    }

    let mut name = String::new();

    let mut needs_separation = false;
    for ns in ns.iter().chain(Some(&this).into_iter())
    {
        if needs_separation {
            name += "/";
        }

        name += ns;
        needs_separation = true;
    }

    name
}

impl<E: Engine> ConstraintSystem<E> for FindFirstInvalidConstraintSystem<E> {
    type Root = Self;

    fn alloc<F, A, AR>(
        &mut self,
        annotation: A,
        f: F
    ) -> Result<Variable, SynthesisError>
        where F: FnOnce() -> Result<E::Fr, SynthesisError>, A: FnOnce() -> AR, AR: Into<String>
    {
        let index = self.aux.len();
        let path = compute_path(&self.current_namespace, annotation().into());
        self.aux.push((f()?, path));
        let var = Variable::new_unchecked(Index::Aux(index));
        // self.set_named_obj(path, NamedObject::Var(var));

        Ok(var)
    }

    fn alloc_input<F, A, AR>(
        &mut self,
        annotation: A,
        f: F
    ) -> Result<Variable, SynthesisError>
        where F: FnOnce() -> Result<E::Fr, SynthesisError>, A: FnOnce() -> AR, AR: Into<String>
    {
        let index = self.inputs.len();
        let path = compute_path(&self.current_namespace, annotation().into());
        self.inputs.push((f()?, path));
        let var = Variable::new_unchecked(Index::Input(index));
        // self.set_named_obj(path, NamedObject::Var(var));

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
        if self.found_error.is_some() {
            // skip everything else after first error
            return;
        }
        let path = compute_path(&self.current_namespace, annotation().into());
        let index = self.num_constraints;
        self.set_named_obj(path.clone(), NamedObject::Constraint(index));

        let a = a(LinearCombination::zero());
        let b = b(LinearCombination::zero());
        let c = c(LinearCombination::zero());

        let mut a = eval_lc::<E>(a.as_ref(), &self.inputs, &self.aux);
        let b = eval_lc::<E>(b.as_ref(), &self.inputs, &self.aux);
        let c = eval_lc::<E>(c.as_ref(), &self.inputs, &self.aux);

        a.mul_assign(&b);

        if a != c {
            self.found_error = Some(path);
        }

        self.num_constraints += 1;
    }

    fn push_namespace<NR, N>(&mut self, name_fn: N)
    where NR: Into<String>, N: FnOnce() -> NR
    {
        let name = name_fn().into();
        let path = compute_path(&self.current_namespace, name.clone());
        self.set_named_obj(path, NamedObject::Namespace);
        self.current_namespace.push(name);
    }

    fn pop_namespace(&mut self)
    {
        assert!(self.current_namespace.pop().is_some());
    }

    fn get_root(&mut self) -> &mut Self::Root
    {
        self
    }
}