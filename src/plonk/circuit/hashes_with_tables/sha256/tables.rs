use crate::bellman::plonk::better_better_cs::cs::*;
use crate::bellman::plonk::better_better_cs::lookup_tables::*;
use crate::bellman::plonk::better_better_cs::utils;
use crate::bellman::pairing::ff::*;
use crate::bellman::SynthesisError;
use crate::bellman::Engine;

use super::utils::*;
use super::super::utils::*;


// SHA256 SPECIFIC TABLES (so to say)
// ----------------------------------------------------------------------------------------------------------------------------

// Sha256ShedulerHelperTable is used only in message expansion routines (sheduling).
// the table has the following column structure: (x, base4_shift3(x), base4_rot9(x))
// the width of table is 11
#[derive(Clone)]
pub struct Sha256ShedulerHelperTable<E: Engine> {
    table_entries: [Vec<E::Fr>; 3],
    table_lookup_map: std::collections::HashMap<E::Fr, (E::Fr, E::Fr)>,
    bits: usize,
    name: &'static str,
}

impl<E: Engine> Sha256ShedulerHelperTable<E> {
    pub fn new(name: &'static str) -> Self {
        let bits = 11usize;
        let shift = 3usize;
        let rot = 9usize;
        let base = 4usize;

        let mut keys = Vec::with_capacity(1 << bits);
        let mut values0 = Vec::with_capacity(1 << bits);
        let mut values1 = Vec::with_capacity(1 << bits);
        let mut map = std::collections::HashMap::with_capacity(1 << bits);

        for x in 0..(1 << bits) {
            let y = map_into_sparse_form(shift_right(x, shift), base);
            let z = map_into_sparse_form(rotate_extract(x, rot, 0), base);
            
            let x = E::Fr::from_str(&x.to_string()).unwrap();
            let y = E::Fr::from_str(&y.to_string()).unwrap();
            let z = E::Fr::from_str(&z.to_string()).unwrap();

            keys.push(x);
            values0.push(y);
            values1.push(z);
            map.insert(x, (y, z));
        }

        Self {
            table_entries: [keys, values0, values1],
            table_lookup_map: map,
            bits,
            name,
        }
    }
}

impl<E: Engine> std::fmt::Debug for Sha256ShedulerHelperTable<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Sha256ExtensionHelperTable")
            .finish()
    }
}

impl<E: Engine> LookupTableInternal<E> for Sha256ShedulerHelperTable<E> {
    fn name(&self) -> &'static str {
        self.name
    }
    fn table_size(&self) -> usize {
        1 << self.bits
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
        assert!(column_num <= 2);
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

