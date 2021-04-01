use crate::bellman::plonk::better_better_cs::cs::*;
use crate::bellman::plonk::better_better_cs::lookup_tables::*;
use crate::bellman::plonk::better_better_cs::utils;
use crate::bellman::pairing::ff::*;
use crate::bellman::SynthesisError;
use crate::bellman::Engine;

use itertools::Itertools;

use super::super::utils::*;


// for given bases (b, c), num_of_chunks n, 
// base converter function f: [0, b) -> [0, c) 
// and block counting function g : [0, n) -> u64
// this table does the following transformation:
// x = \sum_{i=0}^n x_i b^i -> y = \sum_{i=0}^m f(x_i) c^i.
// first column - input x; 
// second column - g(k), where k is the number of actual non-zero chunks
// third column - output y;
#[derive(Clone)]
pub struct ExtendedBaseConverterTable<E: Engine> {
    table_entries: [Vec<E::Fr>; 3],
    table_lookup_map: std::collections::HashMap<E::Fr, (E::Fr, E::Fr)>,
    num_chunks: usize,
    base_b: u64,
    base_c: u64,
    name: &'static str,
}

impl<E: Engine> ExtendedBaseConverterTable<E> {
    pub fn new<F, G>(num_chunks: usize, base_b: u64, base_c: u64, transform_f: F, transform_counter: G, name: &'static str) -> Self 
    where F: Fn(u64) -> u64, G: Fn(u64) -> u64
    {
        let table_size = pow(base_b as usize, num_chunks);
        let mut keys_vec = Vec::with_capacity(table_size);
        let mut chunk_count_vec = Vec::with_capacity(table_size);
        let mut values_vec = Vec::with_capacity(table_size);
        let mut map = std::collections::HashMap::with_capacity(table_size);

        let base_b_fr = u64_to_ff::<E::Fr>(base_b);
        let base_c_fr = u64_to_ff::<E::Fr>(base_c);
        let zero_fr = E::Fr::zero();

        for coefs in (0..num_chunks).map(|_| 0..base_b).multi_cartesian_product() {
            let key = coefs.iter().fold(zero_fr.clone(), |acc, x| {
                let mut tmp = acc;
                tmp.mul_assign(&base_b_fr);
                tmp.add_assign(&u64_to_ff(*x));
                tmp
            });

            let value = coefs.iter().fold(zero_fr.clone(), |acc, x| {
                let mut tmp = acc;
                tmp.mul_assign(&base_c_fr);
                tmp.add_assign(&u64_to_ff(transform_f(*x)));
                tmp
            });

            let chunk_count = (num_chunks - coefs.iter().take_while(|x| **x == 0).count()) as u64;
            let chunk_count_fr = u64_to_ff(transform_counter(chunk_count));

            keys_vec.push(key);
            chunk_count_vec.push(chunk_count_fr);
            values_vec.push(value);
            map.insert(key, (chunk_count_fr, value));
        }

        Self {
            table_entries: [keys_vec, chunk_count_vec, values_vec],
            table_lookup_map: map,
            num_chunks,
            base_b,
            base_c,
            name,
        }
    }
}

impl<E: Engine> std::fmt::Debug for ExtendedBaseConverterTable<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ExtendedBaseConverterTable")
            .field("num_chunks", &self.num_chunks)
            .field("base_b", &self.base_b)
            .field("base_c", &self.base_c)
            .finish()
    }
}

impl<E: Engine> LookupTableInternal<E> for ExtendedBaseConverterTable<E> {
    fn name(&self) -> &'static str {
        self.name
    }
    fn table_size(&self) -> usize {
        pow(self.base_b as usize, self.num_chunks)
    }
    fn num_keys(&self) -> usize {
        1
    }
    fn num_values(&self) -> usize {
        2
    }
    fn allows_combining(&self) -> bool {
        true
    }
    fn get_table_values_for_polys(&self) -> Vec<Vec<E::Fr>> {
        vec![self.table_entries[0].clone(), self.table_entries[1].clone(), self.table_entries[2].clone()]
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
    fn column_is_trivial(&self, column_num: usize) -> bool {
        assert!(column_num < 3);
        false
    }

    fn is_valid_entry(&self, keys: &[E::Fr], values: &[E::Fr]) -> bool {
        assert!(keys.len() == self.num_keys());
        assert!(values.len() == self.num_values());

        if let Some(entry) = self.table_lookup_map.get(&keys[0]) {
            return entry == &(values[0], values[1]);
        }
        false
    }

    fn query(&self, keys: &[E::Fr]) -> Result<Vec<E::Fr>, SynthesisError> {
        assert!(keys.len() == self.num_keys());

        if let Some(entry) = self.table_lookup_map.get(&keys[0]) {
            return Ok(vec![entry.0, entry.1])
        }

        Err(SynthesisError::Unsatisfiable)
    }
}


#[derive(Clone)]
pub struct OverflowCognizantConverterTable<E: Engine> {
    table_entries: [Vec<E::Fr>; 3],
    table_lookup_map: std::collections::HashMap<E::Fr, (E::Fr, E::Fr)>,
    base_b: u64,
    base_c: u64,
    high_chunk_offset: u64,
    name: &'static str,
}

impl<E: Engine> OverflowCognizantConverterTable<E> {
    pub fn new<F: Fn(u64) -> u64>(
        base_b: u64, base_c: u64, offset:u64, transform_f: F, name: &'static str
    ) -> Self 
    {
        let table_size = (base_b * (base_b+1)/2) as usize;
        let mut keys_vec = Vec::with_capacity(table_size);
        let zero_vec = vec![E::Fr::zero(); table_size];
        let mut values_vec = Vec::with_capacity(table_size);
        let mut map = std::collections::HashMap::with_capacity(table_size);

        let offset_fr = u64_exp_to_ff::<E::Fr>(base_b, offset);
        let zero_fr = E::Fr::zero();

        for i in 0..base_b {
            for j in 0..(base_b-i) {
                let low = i;
                let high = j;

                let mut key = u64_to_ff::<E::Fr>(low);
                let mut high_fr = u64_to_ff::<E::Fr>(high);
                high_fr.mul_assign(&offset_fr);
                key.add_assign(&high_fr);

                let value = u64_to_ff(transform_f(low + high));

                keys_vec.push(key);
                values_vec.push(value);
                map.insert(key, (zero_fr.clone(), value));
            }
        }

        Self {
            table_entries: [keys_vec, zero_vec, values_vec],
            table_lookup_map: map,
            base_b,
            base_c,
            high_chunk_offset: offset,
            name,
        }
    }
}

impl<E: Engine> std::fmt::Debug for OverflowCognizantConverterTable<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ExtendedBaseConverterTable")
            .field("base_b", &self.base_b)
            .field("base_c", &self.base_c)
            .field("high_chunk_offset", &self.high_chunk_offset)
            .finish()
    }
}

impl<E: Engine> LookupTableInternal<E> for OverflowCognizantConverterTable<E> {
    fn name(&self) -> &'static str {
        self.name
    }
    fn table_size(&self) -> usize {
        let table_size = (self.base_b * (self.base_b+1)/2) as usize;
        table_size
    }
    fn num_keys(&self) -> usize {
        1
    }
    fn num_values(&self) -> usize {
        2
    }
    fn allows_combining(&self) -> bool {
        true
    }
    fn get_table_values_for_polys(&self) -> Vec<Vec<E::Fr>> {
        vec![self.table_entries[0].clone(), self.table_entries[1].clone(), self.table_entries[2].clone()]
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
    fn column_is_trivial(&self, column_num: usize) -> bool {
        assert!(column_num < 3);
        false
    }

    fn is_valid_entry(&self, keys: &[E::Fr], values: &[E::Fr]) -> bool {
        assert!(keys.len() == self.num_keys());
        assert!(values.len() == self.num_values());

        if let Some(entry) = self.table_lookup_map.get(&keys[0]) {
            return entry == &(values[0], values[1]);
        }
        false
    }

    fn query(&self, keys: &[E::Fr]) -> Result<Vec<E::Fr>, SynthesisError> {
        assert!(keys.len() == self.num_keys());

        if let Some(entry) = self.table_lookup_map.get(&keys[0]) {
            return Ok(vec![entry.0, entry.1])
        }

        Err(SynthesisError::Unsatisfiable)
    }
}
