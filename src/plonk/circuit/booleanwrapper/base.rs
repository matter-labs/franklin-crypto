use super::*;
use crate::bellman::pairing::Engine;
use crate::bellman::plonk::better_better_cs::cs::*;
use crate::bellman::SynthesisError;
use crate::plonk::circuit::boolean::{AllocatedBit, Boolean};
use crate::plonk::circuit::booleanwrapper::base::Index::*;
use plonk::circuit::booleanwrapper::utils::{smart_and, smart_or};
use serde::de::value::BoolDeserializer;
use std::clone::Clone;
use std::collections::HashMap;
use std::ops::{BitAnd, Deref};
use std::sync::Mutex;
use std::{cmp::Ordering, collections::BTreeSet};

use std::ops::BitXor;
use std::ops::Not;

lazy_static! {
    static ref GLOBAL_STORAGE: Mutex<Storage> = Mutex::new(Storage::new());
}

//The BooleanWrapper structure is a wrapper to the Boulevard structure.
//Its main idea is not to allow duplicates of constraints when calling Boolean methods.
#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
pub enum StringForKey {
    Xor,
    And,
    Or,
    ConditionallySelect,
}

#[derive(Debug, Clone, Copy)]
pub struct BooleanWrapper(pub Boolean);

impl From<Boolean> for BooleanWrapper {
    fn from(item: Boolean) -> Self {
        BooleanWrapper(item)
    }
}

impl Deref for BooleanWrapper {
    type Target = Boolean;
    fn deref(&self) -> &Boolean {
        &self.0
    }
}
impl BooleanWrapper {
    //Inside the structure, Boolean itself is called
    //Also call the methods of the local Storage, which checks whether there is already such
    // a key with the desired constraint in the database.
    pub fn xor<E, CS>(
        cs: &mut CS,
        a: &BooleanWrapper,
        b: &BooleanWrapper,
    ) -> Result<Self, SynthesisError>
    where
        E: Engine,
        CS: ConstraintSystem<E>,
    {
        match (a, b) {
            (&BooleanWrapper(Boolean::Constant(true)), a)
            | (a, &BooleanWrapper(Boolean::Constant(true)))
            | (&BooleanWrapper(Boolean::Constant(false)), a)
            | (a, &BooleanWrapper(Boolean::Constant(false))) => {
                Ok(BooleanWrapper(Boolean::xor(cs, &a, &b).unwrap()))
            }

            (_, _) => {
                let mut sec_array = BTreeSet::new();
                sec_array.insert(a.clone());
                sec_array.insert(b.clone());
                if GLOBAL_STORAGE
                    .lock()
                    .unwrap()
                    .check_storage(&(sec_array.clone(), StringForKey::Xor))
                {
                    Ok(GLOBAL_STORAGE
                        .lock()
                        .unwrap()
                        .return_value(&(sec_array.clone(), StringForKey::Xor)))
                } else {
                    let value = BooleanWrapper(Boolean::xor(cs, &a, &b).unwrap());
                    GLOBAL_STORAGE
                        .lock()
                        .unwrap()
                        .insert_value(&(sec_array.clone(), StringForKey::Xor), &value);
                    Ok(value)
                }
            }
        }
    }

    pub fn and<E, CS>(
        cs: &mut CS,
        a: &BooleanWrapper,
        b: &BooleanWrapper,
    ) -> Result<Self, SynthesisError>
    where
        E: Engine,
        CS: ConstraintSystem<E>,
    {
        match (a, b) {
            (&BooleanWrapper(Boolean::Constant(true)), a)
            | (a, &BooleanWrapper(Boolean::Constant(true)))
            | (&BooleanWrapper(Boolean::Constant(false)), a)
            | (a, &BooleanWrapper(Boolean::Constant(false))) => {
                Ok(BooleanWrapper(Boolean::and(cs, &a, &b).unwrap()))
            }

            (_, _) => {
                let mut sec_array = BTreeSet::new();
                sec_array.insert(a.clone());
                sec_array.insert(b.clone());
                if GLOBAL_STORAGE
                    .lock()
                    .unwrap()
                    .check_storage(&(sec_array.clone(), StringForKey::And))
                {
                    Ok(GLOBAL_STORAGE
                        .lock()
                        .unwrap()
                        .return_value(&(sec_array.clone(), StringForKey::And)))
                } else {
                    let value = BooleanWrapper(Boolean::and(cs, &a, &b).unwrap());
                    GLOBAL_STORAGE
                        .lock()
                        .unwrap()
                        .insert_value(&(sec_array.clone(), StringForKey::And), &value);
                    Ok(value)
                }
            }
        }
    }

    pub fn or<E, CS>(
        cs: &mut CS,
        a: &BooleanWrapper,
        b: &BooleanWrapper,
    ) -> Result<Self, SynthesisError>
    where
        E: Engine,
        CS: ConstraintSystem<E>,
    {
        match (a, b) {
            (&BooleanWrapper(Boolean::Constant(true)), a)
            | (a, &BooleanWrapper(Boolean::Constant(true)))
            | (&BooleanWrapper(Boolean::Constant(false)), a)
            | (a, &BooleanWrapper(Boolean::Constant(false))) => {
                Ok(BooleanWrapper(Boolean::or(cs, &a, &b).unwrap()))
            }

            (_, _) => {
                let mut sec_array = BTreeSet::new();
                sec_array.insert(a.clone());
                sec_array.insert(b.clone());
                if GLOBAL_STORAGE
                    .lock()
                    .unwrap()
                    .check_storage(&(sec_array.clone(), StringForKey::Or))
                {
                    Ok(GLOBAL_STORAGE
                        .lock()
                        .unwrap()
                        .return_value(&(sec_array.clone(), StringForKey::Or)))
                } else {
                    let value = BooleanWrapper(Boolean::or(cs, &a, &b).unwrap());
                    GLOBAL_STORAGE
                        .lock()
                        .unwrap()
                        .insert_value(&(sec_array.clone(), StringForKey::Or), &value);
                    Ok(value)
                }
            }
        }
    }

    pub fn conditionally_select<E: Engine, CS: ConstraintSystem<E>>(
        cs: &mut CS,
        flag: &BooleanWrapper,
        a: &BooleanWrapper,
        b: &BooleanWrapper,
    ) -> Result<Self, SynthesisError> {
        match (a, b) {
            (&BooleanWrapper(Boolean::Constant(true)), a)
            | (a, &BooleanWrapper(Boolean::Constant(true)))
            | (&BooleanWrapper(Boolean::Constant(false)), a)
            | (a, &BooleanWrapper(Boolean::Constant(false))) => Ok(BooleanWrapper(
                Boolean::sha256_ch(cs, &flag, &a, &b).unwrap(),
            )),

            (_, _) => {
                let mut sec_array = BTreeSet::new();
                sec_array.insert(a.clone());
                sec_array.insert(b.clone());
                if GLOBAL_STORAGE
                    .lock()
                    .unwrap()
                    .check_storage(&(sec_array.clone(), StringForKey::ConditionallySelect))
                {
                    Ok(GLOBAL_STORAGE
                        .lock()
                        .unwrap()
                        .return_value(&(sec_array.clone(), StringForKey::ConditionallySelect)))
                } else {
                    let value = BooleanWrapper(Boolean::sha256_ch(cs, &flag, &a, &b).unwrap());
                    GLOBAL_STORAGE.lock().unwrap().insert_value(
                        &(sec_array.clone(), StringForKey::ConditionallySelect),
                        &value,
                    );
                    Ok(value)
                }
            }
        }
    }

    pub fn alloc<E: Engine, CS: ConstraintSystem<E>>(
        cs: &mut CS,
        witness: Option<bool>,
    ) -> Result<Self, SynthesisError> {
        Ok(BooleanWrapper(Boolean::alloc(cs, witness).unwrap()))
    }

    pub fn smart_and<E: Engine, CS: ConstraintSystem<E>>(
        cs: &mut CS,
        bools: &[BooleanWrapper],
    ) -> Result<Self, SynthesisError> {
        //if all elements are constants, perform the function without optimization
        let mut storage = GLOBAL_STORAGE.lock().unwrap();
        if bools.iter().all(|x| x.is_constant()) {
            let boolean: Vec<Boolean> = bools.into_iter().map(|x| x.convert()).collect();
            Ok(BooleanWrapper(smart_and(cs, boolean.as_slice()).unwrap()))
        } else {
            let mut sec_array = BTreeSet::new();
            sec_array.extend(bools.into_iter());
            let exact_key = sec_array.clone();
            assert_eq!(sec_array.is_empty(), false);
            
            //check if storage is empty
            if storage.keys().is_empty(){
                let boolean: Vec<Boolean> = bools.into_iter().map(|x| x.convert()).collect();
                let value = BooleanWrapper(smart_and(cs, &boolean).unwrap());
                sec_array.extend(bools.into_iter());
                storage.insert_value(&(sec_array.clone(), StringForKey::And), &value);

                return Ok(value);
            }

            //check Storage if there was already such a variable with such a value
            if storage.check_storage(&(sec_array.clone(), StringForKey::And)) {
                Ok(storage.return_value(&(sec_array.clone(), StringForKey::And)))
            }

            // Optimization algorithm
            else {
                let mut new_bools = vec![];
                for key in storage.keys() {
                    if key.1 == StringForKey::And {
                        let set = key.0;
                        let intersection = sec_array.bitand(&set);

                        if intersection.len() > 1 && storage.check_storage(&(intersection.clone(), StringForKey::And))==true{
                            // new_bools.clear();
                            let value_of_intersec = storage.return_value(&(intersection.clone(), StringForKey::And));
                            let mut tree_set = sec_array.bitxor(&intersection);
                            tree_set.insert(value_of_intersec);
                            new_bools = tree_set.clone().into_iter().collect();
                            sec_array = tree_set;
                        } else {
                            new_bools = sec_array.clone().into_iter().collect();
                        }
                    }
                }
                let boolean: Vec<Boolean> = new_bools.iter().map(|x| x.convert()).collect();
                let bools = boolean.as_slice();
                let value = BooleanWrapper(smart_and(cs, &bools).unwrap());
                storage.insert_value(&(exact_key, StringForKey::And), &value);
                Ok(value)
            }
        }
    }
    pub fn smart_or<E: Engine, CS: ConstraintSystem<E>>(
        cs: &mut CS,
        bools: &[BooleanWrapper],
    ) -> Result<Self, SynthesisError> {
        //if all elements are constants, perform the function without optimization
        let mut storage = GLOBAL_STORAGE.lock().unwrap();
        if bools.iter().all(|x| x.is_constant()) {
            let boolean: Vec<Boolean> = bools.into_iter().map(|x| x.convert()).collect();
            Ok(BooleanWrapper(smart_or(cs, boolean.as_slice()).unwrap()))
        } else {
            let mut sec_array = BTreeSet::new();
            sec_array.extend(bools.into_iter());
            let exact_key = sec_array.clone();
            assert_eq!(sec_array.is_empty(), false);
            
            //check if storage is empty
            if storage.keys().is_empty(){
                let boolean: Vec<Boolean> = bools.into_iter().map(|x| x.convert()).collect();
                let value = BooleanWrapper(smart_or(cs, &boolean).unwrap());
                sec_array.extend(bools.into_iter());
                storage.insert_value(&(sec_array.clone(), StringForKey::Or), &value);

                return Ok(value);
            }

            //check Storage if there was already such a variable with such a value
            if storage.check_storage(&(sec_array.clone(), StringForKey::Or)) {
                Ok(storage.return_value(&(sec_array.clone(), StringForKey::Or)))
            }

            // Optimization algorithm
            else {
                let mut new_bools = vec![];
                for key in storage.keys() {
                    if key.1 == StringForKey::Or {
                        let set = key.0;
                        let intersection = sec_array.bitand(&set);

                        if intersection.len() > 1 && storage.check_storage(&(intersection.clone(), StringForKey::Or))==true{
                            // new_bools.clear();
                            let value_of_intersec = storage.return_value(&(intersection.clone(), StringForKey::Or));
                            let mut tree_set = sec_array.bitxor(&intersection);
                            tree_set.insert(value_of_intersec);
                            new_bools = tree_set.clone().into_iter().collect();
                            sec_array = tree_set;
                        } else {
                            new_bools = sec_array.clone().into_iter().collect();
                        }
                    }
                }
                let boolean: Vec<Boolean> = new_bools.iter().map(|x| x.convert()).collect();
                let bools = boolean.as_slice();
                let value = BooleanWrapper(smart_or(cs, &bools).unwrap());
                storage.insert_value(&(exact_key, StringForKey::Or), &value);
                Ok(value)
            }
        }
    }

    pub fn convert(&self) -> Boolean {
        self.0
    }

    pub fn finalize() {
        todo!();
    }
}
impl PartialEq for BooleanWrapper {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (BooleanWrapper(Boolean::Is(a)), BooleanWrapper(Boolean::Is(b))) => {
                a.get_variable() == b.get_variable()
            }
            (BooleanWrapper(Boolean::Not(a)), BooleanWrapper(Boolean::Not(b))) => {
                a.get_variable() == b.get_variable()
            }
            _ => false,
        }
    }
}
impl Eq for BooleanWrapper {}

use std::hash::{Hash, Hasher};
impl Hash for BooleanWrapper {
    #[inline]
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        match self {
            BooleanWrapper(Boolean::Constant(_)) => unimplemented!(),
            BooleanWrapper(Boolean::Is(x)) => {
                x.get_variable().hash(hasher);
            }
            BooleanWrapper(Boolean::Not(y)) => {
                y.get_variable().hash(hasher);
            }
        }
    }
}

impl PartialOrd for BooleanWrapper {
    fn partial_cmp(&self, other: &Self) -> Option<::std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for BooleanWrapper {
    #[inline]
    fn cmp(&self, other: &Self) -> ::std::cmp::Ordering {
        match (self, other) {
            (BooleanWrapper(Boolean::Constant(a)), BooleanWrapper(Boolean::Constant(b))) => {
                a.cmp(&b)
            }
            (BooleanWrapper(Boolean::Constant(_a)), _) => std::cmp::Ordering::Less,
            (BooleanWrapper(Boolean::Is(..)), BooleanWrapper(Boolean::Constant(..))) => {
                std::cmp::Ordering::Greater
            }
            (BooleanWrapper(Boolean::Not(..)), BooleanWrapper(Boolean::Constant(..))) => {
                std::cmp::Ordering::Greater
            }
            (BooleanWrapper(Boolean::Is(..)), BooleanWrapper(Boolean::Not(..))) => {
                std::cmp::Ordering::Less
            }
            (BooleanWrapper(Boolean::Is(a)), BooleanWrapper(Boolean::Is(b))) => {
                let idx_a = a.get_variable().get_unchecked();
                let idx_b = b.get_variable().get_unchecked();

                match (idx_a, idx_b) {
                    (Index::Aux(v), Index::Aux(m)) => v.cmp(&m),
                    _ => unimplemented!(),
                }
            }
            (BooleanWrapper(Boolean::Not(..)), BooleanWrapper(Boolean::Is(..))) => {
                std::cmp::Ordering::Greater
            }
            (BooleanWrapper(Boolean::Not(a)), BooleanWrapper(Boolean::Not(b))) => {
                let idx_a = a.get_variable().get_unchecked();
                let idx_b = b.get_variable().get_unchecked();

                match (idx_a, idx_b) {
                    (Index::Aux(v), Index::Aux(m)) => v.cmp(&m),
                    _ => unimplemented!(),
                }
            }
        }
    }
}

use std::collections::hash_map::Keys;
use std::fmt::Debug;
pub struct Storage {
    pub inner: std::collections::HashMap<(BTreeSet<BooleanWrapper>, StringForKey), BooleanWrapper>,
}

impl Storage {
    pub fn new() -> Self {
        Self {
            inner: HashMap::new(),
        }
    }

    pub fn insert_value(
        &mut self,
        key: &(BTreeSet<BooleanWrapper>, StringForKey),
        value: &BooleanWrapper,
    ) {
        self.inner.insert(key.clone(), value.clone());
    }

    pub fn check_storage(&self, key: &(BTreeSet<BooleanWrapper>, StringForKey)) -> bool {
        self.inner.contains_key(&key)
    }
    pub fn return_value(&self, key: &(BTreeSet<BooleanWrapper>, StringForKey)) -> BooleanWrapper {
        *self.inner.get(key).unwrap()
    }

    pub fn clear_storage(&mut self) {
        self.inner.clear();
    }

    pub fn keys(&self) -> Vec<(BTreeSet<BooleanWrapper>, StringForKey)> {
        self.inner.keys().cloned().collect()
    }
}

#[cfg(test)]
mod test {

    use super::*;
    use crate::bellman::pairing::bn256::Bn256;
    use crate::plonk::circuit::boolean::AllocatedBit;
    #[test]
    fn test_xor() {
        for a_val in [false, true].iter() {
            for b_val in [false, true].iter() {
                let mut cs = TrivialAssembly::<
                    Bn256,
                    PlonkCsWidth4WithNextStepParams,
                    Width4MainGateWithDNext,
                >::new();
                let a = AllocatedBit::alloc(&mut cs, Some(*a_val)).unwrap();
                let b = AllocatedBit::alloc(&mut cs, Some(*b_val)).unwrap();
                let c = BooleanWrapper::xor(
                    &mut cs,
                    &BooleanWrapper(Boolean::Is(a)),
                    &BooleanWrapper(Boolean::Is(b)),
                )
                .unwrap();
                let cd = BooleanWrapper::xor(
                    &mut cs,
                    &BooleanWrapper(Boolean::Constant(a_val.clone())),
                    &BooleanWrapper(Boolean::Constant(b_val.clone())),
                )
                .unwrap();
                println!("const_xor = {:?}", cd);
                println!("c_xor = {:?}", c);

                assert!(
                    cs.is_satisfied(),
                    "unsatisfied for a = {}, b = {}",
                    a_val,
                    b_val
                );
                GLOBAL_STORAGE.lock().unwrap().clear_storage();
            }
        }
    }
    #[test]
    fn test_and() {
        for a_val in [false, true].iter() {
            for b_val in [false, true].iter() {
                let mut cs = TrivialAssembly::<
                    Bn256,
                    PlonkCsWidth4WithNextStepParams,
                    Width4MainGateWithDNext,
                >::new();
                let a = AllocatedBit::alloc(&mut cs, Some(*a_val)).unwrap();
                let b = AllocatedBit::alloc(&mut cs, Some(*b_val)).unwrap();
                let c = BooleanWrapper::and(
                    &mut cs,
                    &BooleanWrapper(Boolean::Is(a)),
                    &BooleanWrapper(Boolean::Is(b)),
                )
                .unwrap();
                let cd = BooleanWrapper::and(
                    &mut cs,
                    &BooleanWrapper(Boolean::Constant(a_val.clone())),
                    &BooleanWrapper(Boolean::Constant(b_val.clone())),
                )
                .unwrap();
                println!("const_and = {:?}", cd);
                println!("c_and = {:?}", c);

                assert!(
                    cs.is_satisfied(),
                    "unsatisfied for a = {}, b = {}",
                    a_val,
                    b_val
                );
                GLOBAL_STORAGE.lock().unwrap().clear_storage();
            }
        }
    }
    #[test]
    fn test_or() {
        for a_val in [false, true].iter() {
            for b_val in [false, true].iter() {
                let mut cs = TrivialAssembly::<
                    Bn256,
                    PlonkCsWidth4WithNextStepParams,
                    Width4MainGateWithDNext,
                >::new();
                let a = AllocatedBit::alloc(&mut cs, Some(*a_val)).unwrap();
                let b = AllocatedBit::alloc(&mut cs, Some(*b_val)).unwrap();
                let c = BooleanWrapper::or(
                    &mut cs,
                    &BooleanWrapper(Boolean::Is(a)),
                    &BooleanWrapper(Boolean::Is(b)),
                )
                .unwrap();
                let cd = BooleanWrapper::or(
                    &mut cs,
                    &BooleanWrapper(Boolean::Constant(a_val.clone())),
                    &BooleanWrapper(Boolean::Constant(b_val.clone())),
                )
                .unwrap();
                println!("const_or = {:?}", cd);
                println!("c_or = {:?}", c);

                assert!(
                    cs.is_satisfied(),
                    "unsatisfied for a = {}, b = {}",
                    a_val,
                    b_val
                );
                GLOBAL_STORAGE.lock().unwrap().clear_storage();
            }
        }
    }
    #[test]
    fn test_conditionally() {
        for a_val in [false, true].iter() {
            for b_val in [false, true].iter() {
                let mut cs = TrivialAssembly::<
                    Bn256,
                    PlonkCsWidth4WithNextStepParams,
                    Width4MainGateWithDNext,
                >::new();
                let a = AllocatedBit::alloc(&mut cs, Some(*a_val)).unwrap();
                let b = AllocatedBit::alloc(&mut cs, Some(*b_val)).unwrap();
                let c = BooleanWrapper::conditionally_select(
                    &mut cs,
                    &BooleanWrapper(Boolean::Constant(true)),
                    &BooleanWrapper(Boolean::Is(a)),
                    &BooleanWrapper(Boolean::Is(b)),
                )
                .unwrap();
                let cd = BooleanWrapper::conditionally_select(
                    &mut cs,
                    &BooleanWrapper(Boolean::Constant(false)),
                    &BooleanWrapper(Boolean::Constant(a_val.clone())),
                    &BooleanWrapper(Boolean::Constant(b_val.clone())),
                )
                .unwrap();
                println!("const_select = {:?}", cd);
                println!("c_select = {:?}", c);

                assert!(
                    cs.is_satisfied(),
                    "unsatisfied for a = {}, b = {}",
                    a_val,
                    b_val
                );
                GLOBAL_STORAGE.lock().unwrap().clear_storage();
            }
        }
    }

    #[test]
    fn test_smart_and() {
        for a_val in [false, true].iter() {
            for b_val in [false, true].iter() {
                for c_val in [false, true].iter() {
                    for d_val in [false, true].iter() {
                        let mut cs = TrivialAssembly::<
                            Bn256,
                            PlonkCsWidth4WithNextStepParams,
                            Width4MainGateWithDNext,
                        >::new();
                        let a = AllocatedBit::alloc(&mut cs, Some(*a_val)).unwrap();
                        let b = AllocatedBit::alloc(&mut cs, Some(*b_val)).unwrap();
                        let c = AllocatedBit::alloc(&mut cs, Some(*c_val)).unwrap();
                        let d = AllocatedBit::alloc(&mut cs, Some(*d_val)).unwrap();

                        let bools = [
                            BooleanWrapper(Boolean::Is(a)),
                            BooleanWrapper(Boolean::Not(b)),
                            BooleanWrapper(Boolean::Is(c)),
                            BooleanWrapper(Boolean::Is(d)),
                        ];
                        let result = BooleanWrapper::smart_and(&mut cs, &bools);
                        println!("{:?}", result);

                        assert!(
                            cs.is_satisfied(),
                            "unsatisfied for a = {}, b = {}, c = {}, d = {}",
                            a_val,
                            b_val,
                            c_val,
                            d_val
                        );
                        GLOBAL_STORAGE.lock().unwrap().clear_storage();
                    }
                }
            }
        }
    }
}
