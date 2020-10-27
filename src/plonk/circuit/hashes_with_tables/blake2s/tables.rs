use crate::bellman::plonk::better_better_cs::cs::*;
use crate::bellman::plonk::better_better_cs::lookup_tables::*;
use crate::bellman::plonk::better_better_cs::utils;
use crate::bellman::pairing::ff::*;
use crate::bellman::SynthesisError;
use crate::bellman::Engine;

use super::super::utils::*;


// for columns (a, b, c) this table asserts that c = (a ^ b) >>> shift (cyclic shift of 32 bit values)
// if shift is zero, than it is simple xor table: c = a ^ b;
const XOR_ROTATE_REG_BITLEN : usize = 32;
const XOR_ROTATE_MASK : usize = (1 << XOR_ROTATE_REG_BITLEN) - 1;

#[derive(Clone)]
pub struct XorRotateTable<E: Engine> {
    table_entries: [Vec<E::Fr>; 3],
    table_lookup_map: std::collections::HashMap<(E::Fr, E::Fr), E::Fr>,
    bits: usize,
    shift: usize,
    name: &'static str,
}


impl<E: Engine> XorRotateTable<E> {
    pub fn new(bits: usize, shift: usize, name: &'static str) -> Self {
        let mut keys1 = Vec::with_capacity(1 << bits);
        let mut keys2 = Vec::with_capacity(1 << bits);
        let mut values = Vec::with_capacity(1 << (2 * bits));
        let mut map = std::collections::HashMap::with_capacity(1 << (2 * bits));

        for x in 0..(1 << bits) {
            for y in 0..(1 << bits) {
                let tmp = x ^ y;
                let z : u32 = if shift > 0 {
                    (tmp >> shift) | ((tmp << (XOR_ROTATE_REG_BITLEN - shift)) & XOR_ROTATE_MASK)
                }
                else {
                    tmp
                };

                let x = u64_to_ff(x);
                let y = u64_to_ff(y);
                let z = u64_to_ff(z);

                keys1.push(x);
                keys2.push(y);
                values.push(z);

                map.insert((x, y), z);
            }    
        }

        Self {
            table_entries: [key0, key1, value],
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
        let mut value1 = Vec::with_capacity(1 << bits);
        let mut value1 = Vec::with_capacity(1 << bits);
        
        let mut map = std::collections::HashMap::with_capacity(1 << bits);
        let mask0 = (1 << (bits - rot1)) - 1;
        let mask0 = (1 << (bits - rot1)) - 1;

        for x in 0..(1 << bits) {
            for y in 0..(1 << bits) {
                let z = ( y >> shift) | ((x & mask) << (bits - shift));

                let x = E::Fr::from_str(&x.to_string()).unwrap();
                let y = E::Fr::from_str(&y.to_string()).unwrap();
                let z = E::Fr::from_str(&z.to_string()).unwrap();

                keys1.push(x);
                keys2.push(y);
                values.push(z);

                map.insert((x, y), z);
            }    
        }

        Self {
            table_entries: [key0, key1, value],
            table_lookup_map: map,
            bits,
            shift,
            name,
        }
    }
}


impl<E: Engine> std::fmt::Debug for CompoundShiftTable<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CompoundShiftTable")
            .field("bits", &self.bits)
            .field("shift", &self.shift)
            .finish()
    }
}


impl<E: Engine> LookupTableInternal<E> for CompoundShiftTable<E> {
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

