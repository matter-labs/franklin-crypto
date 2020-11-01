use crate::bellman::plonk::better_better_cs::cs::*;
use crate::bellman::plonk::better_better_cs::lookup_tables::*;
use crate::bellman::plonk::better_better_cs::utils;
use crate::bellman::pairing::ff::*;
use crate::bellman::SynthesisError;
use crate::bellman::Engine;

use super::super::utils::*;


// for columns (a, b, c) this table asserts that c = (a ^ b) >>> shift (cyclic shift of 32 bit values)
// if shift is zero, than it is simple xor table: c = a ^ b;
const XOR_ROTATE_REG_BITLEN : u32 = 32;
const XOR_ROTATE_MASK : u64 = (1 << XOR_ROTATE_REG_BITLEN) - 1;

#[derive(Clone)]
pub struct XorRotateTable<E: Engine> {
    table_entries: [Vec<E::Fr>; 3],
    table_lookup_map: std::collections::HashMap<(E::Fr, E::Fr), E::Fr>,
    bits: usize,
    shift: u32,
    name: &'static str,
}


impl<E: Engine> XorRotateTable<E> {
    pub fn new(bits: usize, shift: u32, name: &'static str) -> Self {
        let mut keys1 = Vec::with_capacity(1 << bits);
        let mut keys2 = Vec::with_capacity(1 << bits);
        let mut values = Vec::with_capacity(1 << (2 * bits));
        let mut map = std::collections::HashMap::with_capacity(1 << (2 * bits));

        for x in 0..(1 << bits) {
            for y in 0..(1 << bits) {
                let tmp: u32 = x ^ y;
                let z : u32 = if shift > 0 {
                    tmp.rotate_right(shift)
                }
                else {
                    tmp
                };

                let x = u64_to_ff(x as u64);
                let y = u64_to_ff(y as u64);
                let z = u64_to_ff(z as u64);

                keys1.push(x);
                keys2.push(y);
                values.push(z);

                map.insert((x, y), z);
            }    
        }

        Self {
            table_entries: [keys1, keys2, values],
            table_lookup_map: map,
            bits,
            shift,
            name,
        }
    }
}


impl<E: Engine> std::fmt::Debug for XorRotateTable<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("XorRotateTable")
            .field("bits", &self.bits)
            .field("shift", &self.shift)
            .finish()
    }
}


impl<E: Engine> LookupTableInternal<E> for XorRotateTable<E> {
    fn name(&self) -> &'static str {
        self.name
    }
    fn table_size(&self) -> usize {
        1 << (2 * self.bits)
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

        if let Some(entry) = self.table_lookup_map.get(&(keys[0], keys[1])) {
            return entry == &(values[0]);
        }
        false
    }

    fn query(&self, keys: &[E::Fr]) -> Result<Vec<E::Fr>, SynthesisError> {
        assert!(keys.len() == self.num_keys());

        if let Some(entry) = self.table_lookup_map.get(&(keys[0], keys[1])) {
            return Ok(vec![*entry])
        }

        Err(SynthesisError::Unsatisfiable)
    }
}


// for columns (a, b, c) asserts that b = a >>> rot1, c = a >>> rot2 (cyclic shifts of 32bit numbers) 
#[derive(Clone)]
pub struct CompoundRotTable<E: Engine> {
    table_entries: [Vec<E::Fr>; 3],
    table_lookup_map: std::collections::HashMap<E::Fr, (E::Fr, E::Fr)>,
    bits: usize,
    rot1: usize,
    rot2: usize,
    name: &'static str,
}


impl<E: Engine> CompoundRotTable<E> {

    pub fn new(bits: usize, rot1: usize, rot2: usize, name: &'static str) -> Self {
        assert!(rot1 < bits);
        assert!(rot2 < bits);
        assert!(rot1 != 0);
        assert!(rot2 != 0);

        let mut keys = Vec::with_capacity(1 << bits);
        let mut values1 = Vec::with_capacity(1 << bits);
        let mut values2 = Vec::with_capacity(1 << bits);
        
        let mut map = std::collections::HashMap::with_capacity(1 << bits);
        let mask1 = (1 << (bits - rot1)) - 1;
        let mask2 = (1 << (bits - rot2)) - 1;

        for x in 0..(1 << bits) {
            let y = (x >> rot1) | ((x & mask1) << (bits - rot1));
            let z = (x >> rot2) | ((x & mask2) << (bits - rot2));
            
            let x = u64_to_ff(x as u64);
            let y = u64_to_ff(y as u64);
            let z = u64_to_ff(z as u64);

            keys.push(x);
            values1.push(y);
            values2.push(z);

            map.insert(x, (y, z));    
        }

        Self {
            table_entries: [keys, values1, values2],
            table_lookup_map: map,
            bits,
            rot1,
            rot2,
            name,
        }
    }
}


impl<E: Engine> std::fmt::Debug for CompoundRotTable<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CompoundShiftTable")
            .field("bits", &self.bits)
            .field("rot1", &self.rot1)
            .field("rot2", &self.rot2)
            .finish()
    }
}


impl<E: Engine> LookupTableInternal<E> for CompoundRotTable<E> {
    fn name(&self) -> &'static str {
        self.name
    }
    fn table_size(&self) -> usize {
        1 << (2 * self.bits)
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

