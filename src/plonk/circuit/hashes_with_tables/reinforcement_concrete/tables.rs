use super::super::utils::*;
use crate::bellman::pairing::ff::*;
use crate::bellman::plonk::better_better_cs::cs::*;
use crate::bellman::plonk::better_better_cs::lookup_tables::*;
use crate::bellman::plonk::better_better_cs::utils;
use crate::bellman::Engine;
use crate::bellman::SynthesisError;
use itertools::Itertools;
use std::iter::FromIterator;

pub const DIGIT_SEP: usize = 3;

// the columns of the table are all triples of the form: | s_0 | s_1 | z |
// subject to the following conditions:
// z - is boolean: z \in {0, 1}
// s_0 and s_1 are all possible state transitions in the following finite state machine:
//
//    |<-----|      |<-----|       |<-------|
//    |      |      |      |       |        |
//    |--->[ 0 ]----|--->[ 1 ]<----|----->[ 2 ]
//
// the only valid state transitions are: 0 -> 0, 0 -> 1, 1 -> 1, 1 -> 2, 2 -> 1, 2 -> 2
#[derive(Clone)]
pub struct ReinforcementConcreterHelperTable0<E: Engine> {
    table_entries: [Vec<E::Fr>; 3],
    valid_state_transitions: std::collections::HashSet<(E::Fr, E::Fr)>,
    table_len: usize,
    name: &'static str,
}

impl<E: Engine> ReinforcementConcreterHelperTable0<E> {
    pub fn new(name: &'static str) -> Self {
        let valid_state_transitions = std::collections::HashSet::<_>::from_iter(
            std::array::IntoIter::new([(0, 0), (0, 1), (1, 1), (1, 2), (2, 1), (2, 2)])
                .map(|(x, y)| (u64_to_ff::<E::Fr>(x), u64_to_ff::<E::Fr>(y))),
        );
        let table_len = valid_state_transitions.len() * 2;
        let mut column0 = Vec::with_capacity(table_len);
        let mut column1 = Vec::with_capacity(table_len);
        let mut column2 = Vec::with_capacity(table_len);

        let iter = valid_state_transitions
            .iter()
            .cartesian_product(std::array::IntoIter::new([E::Fr::zero(), E::Fr::one()]));
        for ((s0, s1), z) in iter {
            column0.push(s0.clone());
            column1.push(s1.clone());
            column2.push(z.clone());
        }

        Self {
            table_entries: [column0, column1, column2],
            valid_state_transitions,
            table_len,
            name,
        }
    }
}

impl<E: Engine> std::fmt::Debug for ReinforcementConcreterHelperTable0<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ReinforcementConcreterHelperTable0")
            .finish()
    }
}

impl<E: Engine> LookupTableInternal<E> for ReinforcementConcreterHelperTable0<E> {
    fn name(&self) -> &'static str {
        self.name
    }
    fn table_size(&self) -> usize {
        self.table_len
    }
    fn num_keys(&self) -> usize {
        3
    }
    fn num_values(&self) -> usize {
        0
    }
    fn allows_combining(&self) -> bool {
        true
    }
    fn get_table_values_for_polys(&self) -> Vec<Vec<E::Fr>> {
        vec![
            self.table_entries[0].clone(),
            self.table_entries[1].clone(),
            self.table_entries[2].clone(),
        ]
    }
    fn table_id(&self) -> E::Fr {
        table_id_from_string(self.name)
    }
    fn sort(&self, _values: &[E::Fr], _column: usize) -> Result<Vec<E::Fr>, SynthesisError> {
        unimplemented!()
    }
    fn box_clone(&self) -> Box<dyn LookupTableInternal<E>> {
        Box::from(self.clone())
    }
    fn column_is_trivial(&self, _column_num: usize) -> bool {
        false
    }

    fn is_valid_entry(&self, keys: &[E::Fr], values: &[E::Fr]) -> bool {
        assert!(keys.len() == self.num_keys());
        assert!(values.len() == self.num_values());

        let check_booleanity =
            |fr: &E::Fr| -> bool { (*fr == E::Fr::zero()) || (*fr == E::Fr::one()) };
        let trns = (keys[0].clone(), keys[1].clone());
        self.valid_state_transitions.contains(&trns) && check_booleanity(&keys[2])
    }

    fn query(&self, _keys: &[E::Fr]) -> Result<Vec<E::Fr>, SynthesisError> {
        Err(SynthesisError::Unsatisfiable)
    }
}

// Special ReinForcement Concrete table has the following column structure: |  x  |   sig_seq  |  f(x) |
// where x is, roughly speaking, is the input of S_box (for Bars round), f(x) is the result of S box
// and signal sequence is auxiliary number which indicates both the index of the current S_box and
// tracks the elements of x, s.t. x < p
// each S_box S_i is associated with unique modulus s_i, s.t. p < s_i,
// and S_i(x) = f(x), if x < p, and x othersiwe
// these means that all S boxes operate identiacally on the subset of x < p, a
// the actual tables for the table are the following:
// x | f(x) | 0, for all x_p
// for each S box S_i with two used numbers s_i, u_i, p < u_i < s_i
// x | x  | i1, for all p <= x < u_u
// u_i | u_i   | i0
// u_i |  u_i  | i2
// x   |   x|   i2
#[derive(Clone)]
pub struct ReinforcementConcreterHelperTable1<E: Engine> {
    table_entries: [Vec<E::Fr>; 3],
    table_lookup_map: std::collections::HashMap<(E::Fr, E::Fr), E::Fr>,
    table_len: usize,
    name: &'static str,
}

impl<E: Engine> ReinforcementConcreterHelperTable1<E> {
    pub fn new<F: Fn(u16) -> u16>(
        p: u16,
        perm_f: F,
        s_arr: &[u16],
        u_arr: &[u16],
        name: &'static str,
    ) -> Self {
        let mut table_len = (p + s_arr.iter().map(|s| *s - p).sum::<u16>()) as usize;
        table_len -= (s_arr[0] - u_arr[0]) as usize;

        let mut column0 = Vec::with_capacity(table_len);
        let mut column1 = Vec::with_capacity(table_len);
        let mut column2 = Vec::with_capacity(table_len);
        let mut map = std::collections::HashMap::with_capacity(table_len);

        for x in 0..p {
            let x_fr = u64_to_ff::<E::Fr>(x as u64);
            let y_fr = E::Fr::one();
            let z_fr = u64_to_ff::<E::Fr>(perm_f(x) as u64);

            column0.push(x_fr);
            column1.push(y_fr);
            column2.push(z_fr);
            map.insert((x_fr, y_fr), z_fr);
        }

        for (i, (s_i, u_i)) in s_arr.iter().zip(u_arr).enumerate() {
            // we first add all columns of the form: (x_i | i * DIGIT_SEP + 1, x_i)
            // for all x_i in the range [p_i; u_i)
            // also add line: (u_i, i * DIGIT_SEP + 0, u_i)
            // for all i >= 2 (and also for i == 1) if flag is false
            // fo all x_i in the range [u_i; s_i) we appenf column of the form:
            // (x_i | i * DIGIT_SEP + 2 | x_i)
            for x in p..*u_i {
                let x = u64_to_ff::<E::Fr>(x as u64);
                let y = u64_to_ff::<E::Fr>(((i + 1) * DIGIT_SEP + 1) as u64);
                let z = x.clone();

                column0.push(x);
                column1.push(y);
                column2.push(z);
                map.insert((x, y), z);
            }

            let x = u64_to_ff::<E::Fr>(*u_i as u64);
            let y = u64_to_ff::<E::Fr>(((i + 1) * DIGIT_SEP + 0) as u64);
            let z = x.clone();

            column0.push(x);
            column1.push(y);
            column2.push(z);
            map.insert((x, y), z);

            if i == 0 {
                continue;
            }

            for x in *u_i..*s_i {
                let x = u64_to_ff::<E::Fr>(x as u64);
                let y = u64_to_ff::<E::Fr>(((i + 1) * DIGIT_SEP + 2) as u64);
                let z = x.clone();

                column0.push(x);
                column1.push(y);
                column2.push(z);
                map.insert((x, y), z);
            }
        }

        Self {
            table_entries: [column0, column1, column2],
            table_lookup_map: map,
            table_len,
            name,
        }
    }
}

impl<E: Engine> std::fmt::Debug for ReinforcementConcreterHelperTable1<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ReinforcementConcreterHelperTable1")
            .finish()
    }
}

impl<E: Engine> LookupTableInternal<E> for ReinforcementConcreterHelperTable1<E> {
    fn name(&self) -> &'static str {
        self.name
    }
    fn table_size(&self) -> usize {
        self.table_len
    }
    fn num_keys(&self) -> usize {
        2
    }
    fn num_values(&self) -> usize {
        1
    }
    fn allows_combining(&self) -> bool {
        true
    }
    fn get_table_values_for_polys(&self) -> Vec<Vec<E::Fr>> {
        vec![
            self.table_entries[0].clone(),
            self.table_entries[1].clone(),
            self.table_entries[2].clone(),
        ]
    }
    fn table_id(&self) -> E::Fr {
        table_id_from_string(self.name)
    }
    fn sort(&self, _values: &[E::Fr], _column: usize) -> Result<Vec<E::Fr>, SynthesisError> {
        unimplemented!()
    }
    fn box_clone(&self) -> Box<dyn LookupTableInternal<E>> {
        Box::from(self.clone())
    }
    fn column_is_trivial(&self, _column_num: usize) -> bool {
        false
    }

    fn is_valid_entry(&self, keys: &[E::Fr], values: &[E::Fr]) -> bool {
        assert!(keys.len() == self.num_keys());
        assert!(values.len() == self.num_values());

        if let Some(entry) = self.table_lookup_map.get(&(keys[0], keys[1])) {
            return entry == &(values[0]);
        }
        false
    }

    fn query(&self, keys: &[E::Fr]) -> Result<Vec<E::Fr>, SynthesisError> {
        assert!(keys.len() == self.num_keys());

        if let Some(entry) = self.table_lookup_map.get(&(keys[0], keys[1])) {
            return Ok(vec![*entry]);
        }

        Err(SynthesisError::Unsatisfiable)
    }
}
