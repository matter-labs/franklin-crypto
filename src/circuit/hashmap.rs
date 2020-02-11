use bellman::pairing::{
    Engine,
};

use bellman::{
    SynthesisError,
    ConstraintSystem
};

use super::{
    Assignment
};

use super::num::AllocatedNum;

use super::boolean::{
    AllocatedBit,
    Boolean
};

use super::permutation::{
    PermutationElement,
    SortablePermutationElement,
    enforce_sort
};

use std::cmp::Ordering;

use bellman::pairing::ff::{
    Field,
    PrimeField
};
use std::collections::HashMap;

#[derive(Clone)]
pub struct HashMapMemoryAccessInfo<E: Engine>
{
    pub index_of_access: AllocatedNum<E>,
    pub key: AllocatedNum<E>,
    pub old_value: Vec<AllocatedNum<E>>,
    pub new_value: Vec<AllocatedNum<E>>
}

impl<E: Engine> PermutationElement<E> for HashMapMemoryAccessInfo<E>
{
    fn switch_2x2<CS>(
        mut cs: CS,
        a: &Self,
        b: &Self,
        switched_on: bool
    ) -> Result<(Self, Self), SynthesisError>
        where CS: ConstraintSystem<E>
    {
        assert_eq!(a.old_value.len(), b.old_value.len());

        let switch = Boolean::from(
            AllocatedBit::alloc(
                cs.namespace(|| "switch boolean"),
                Some(switched_on)
            )?
        );

        let mut c = a.clone();
        let mut d = b.clone();

        let (c_index_of_access, d_index_of_access) = AllocatedNum::conditionally_reverse(
            cs.namespace(|| "index_of_access switch"),
            &a.index_of_access,
            &b.index_of_access,
            &switch
        )?;
        c.index_of_access = c_index_of_access;
        d.index_of_access = d_index_of_access;

        let (c_key, d_key) = AllocatedNum::conditionally_reverse(
            cs.namespace(|| "key switch"),
            &a.key,
            &b.key,
            &switch
        )?;
        c.key = c_key;
        d.key = d_key;

        for (i, (a, b)) in a.old_value.iter().zip(&b.old_value).enumerate() {
            let (c_old_value, d_old_value) = AllocatedNum::conditionally_reverse(
                cs.namespace(|| format!("old_value[{}] switch", i)),
                a,
                b,
                &switch
            )?;
            c.old_value[i] = c_old_value;
            d.old_value[i] = d_old_value;
        }

        for (i, (a, b)) in a.new_value.iter().zip(&b.new_value).enumerate() {
            let (c_new_value, d_new_value) = AllocatedNum::conditionally_reverse(
                cs.namespace(|| format!("new_value[{}] switch", i)),
                a,
                b,
                &switch
            )?;
            c.new_value[i] = c_new_value;
            d.new_value[i] = d_new_value;
        }

        Ok((c, d))
    }
}

impl<E: Engine> SortablePermutationElement<E> for HashMapMemoryAccessInfo<E>
{
    fn cmp(
        a: &Self,
        b: &Self,
    ) -> Ordering
    {
        let key_comparison_result = match (a.key.get_value(), b.key.get_value()) {
            (Some(a_key), Some(b_key)) => {
                let a_key_repr = a_key.into_repr();
                let b_key_repr = b_key.into_repr();

                a_key_repr.cmp(&b_key_repr)
            }
            (None, Some(_)) => Ordering::Less,
            (None, None) => Ordering::Equal,
            (Some(_), None) => Ordering::Greater
        };
        if (key_comparison_result != Ordering::Equal) {
            return key_comparison_result;
        }
        let index_of_access_comparison_result = match (a.index_of_access.get_value(), b.index_of_access.get_value()) {
            (Some(a_index_of_access), Some(b_index_of_access)) => {
                let a_index_of_access_repr = a_index_of_access.into_repr();
                let b_index_of_access_repr = b_index_of_access.into_repr();

                a_index_of_access_repr.cmp(&b_index_of_access_repr)
            }
            (None, Some(_)) => Ordering::Less,
            (None, None) => Ordering::Equal,
            (Some(_), None) => Ordering::Greater
        };
        index_of_access_comparison_result
    }

    fn enforce_leq<CS>(
        mut cs: CS,
        a: &Self,
        b: &Self
    ) -> Result<(), SynthesisError>
        where CS: ConstraintSystem<E>
    {
        let key_comparison = AllocatedNum::less_than(
            cs.namespace(|| "key_comparison"),
            &a.key,
            &b.key
        )?;
        let key_equals = Boolean::from(AllocatedNum::equals(
            cs.namespace(|| "key_equals"),
            &a.key,
            &b.key
        )?);

        let index_of_access_comparison = AllocatedNum::less_than(
            cs.namespace(|| "index_of_access_comparison"),
            &a.index_of_access,
            &b.index_of_access
        )?;
        let index_of_access_equals = Boolean::from(AllocatedNum::equals(
            cs.namespace(|| "index_of_access_equals"),
            &a.index_of_access,
            &b.index_of_access
        )?);
        let index_of_access_leq = Boolean::or(
            cs.namespace(|| "index_of_access_leq"),
            &index_of_access_comparison,
            &index_of_access_equals
        )?;

        let key_equals_and_index_of_access_leq = Boolean::and(
            cs.namespace(|| "key_equals_and_index_of_access_leq"),
            &key_equals,
            &index_of_access_leq
        )?;

        let leq = Boolean::or(
            cs.namespace(|| "leq"),
            &key_comparison,
            &key_equals_and_index_of_access_leq
        )?;
        Boolean::enforce_equal(
            cs.namespace(|| "leq must be true"),
            &leq,
            &Boolean::Constant(true)
        )?;

        Ok(())
    }
}

pub struct HashMapGadget<E: Engine>
{
    default_value: Vec<AllocatedNum<E>>,
    index_of_last_memory_access: AllocatedNum<E>,
    values: HashMap<AllocatedNum<E>, Vec<AllocatedNum<E>>>,
    remembered_memory_accesses: Vec<HashMapMemoryAccessInfo<E>>,
    is_finalized: bool
}

impl<E: Engine> Drop for HashMapGadget<E> {
    fn drop(&mut self) {
        assert!(self.is_finalized, "dropping of not finalized hashmap");
    }
}

impl<E: Engine> HashMapGadget<E>
{
    /// Caller be responsible for validity
    /// of key_bitlength value and real keys bitlength
    pub fn new<CS>(
        mut cs: CS,
        fields_in_value: usize,
        default_value: Option<Vec<AllocatedNum<E>>>,
        key_bitlength: Option<usize>
    ) -> Result<Self, SynthesisError>
        where CS: ConstraintSystem<E>
    {
        assert!(fields_in_value > 0, "count of fields in value must be grater than zero");

        let default_value = match default_value {
            Some(default_value) => default_value,
            None => {
                let zero = AllocatedNum::alloc(
                    cs.namespace(|| "zero value"),
                    || Ok(E::Fr::zero())
                )?;
                cs.enforce(
                    || "zero equal to 0",
                    |lc| lc,
                    |lc| lc,
                    |lc| lc + zero.get_variable(),
                );
                vec![zero; fields_in_value]
            }
        };
        assert_eq!(default_value.len(), fields_in_value);

        let index_of_last_memory_access = AllocatedNum::alloc(
            cs.namespace(|| "index_of_last_memory_access"),
            || Ok(E::Fr::zero())
        )?;
        cs.enforce(
            || "index_of_last_memory_access starts from 0",
            |lc| lc,
            |lc| lc,
            |lc| lc + index_of_last_memory_access.get_variable(),
        );

        Ok(HashMapGadget {
            default_value: default_value,
            index_of_last_memory_access: index_of_last_memory_access,
            values: HashMap::new(),
            remembered_memory_accesses: vec![],
            is_finalized: false
        })
    }

    fn memory_access<CS>(
        &mut self,
        mut cs: CS,
        key: &AllocatedNum<E>,
        new_value: Option<&Vec<AllocatedNum<E>>>
    ) -> Result<Vec<AllocatedNum<E>>, SynthesisError>
        where CS: ConstraintSystem<E>
    {
        if (self.is_finalized){
            // can't access to memory of finalized hashmap
            return Err(SynthesisError::Unsatisfiable);
        }

        let new_index_of_memory_access_value = match self.index_of_last_memory_access.get_value() {
            None => None,
            Some(v) => {
                let mut v = v;
                v.add_assign(&E::Fr::one());
                Some(v)
            }
        };
        let new_index_of_memory_access = AllocatedNum::alloc(
            cs.namespace(|| "new_index_of_memory_access"),
            || new_index_of_memory_access_value.grab()
        )?;
        cs.enforce(
            || "new_index_of_memory_access equal to (index_of_last_memory_access + 1)",
            |lc| lc + self.index_of_last_memory_access.get_variable() + CS::one(),
            |lc| lc + CS::one(),
            |lc| lc + new_index_of_memory_access.get_variable()
        );

        if (!self.values.contains_key(key)){
            self.values.insert(key.clone(), self.default_value.clone());
        }
        let old_value = self.values.get(key).expect("HashMap must contain key at this moment").clone();

        if let Some(new_value) = new_value {
            if (new_value.len() != self.default_value.len()){
                return Err(SynthesisError::Unsatisfiable);
            }
            self.values.insert(key.clone(), new_value.clone());

            self.remembered_memory_accesses.push(
                HashMapMemoryAccessInfo{
                    index_of_access: new_index_of_memory_access.clone(),
                    key: key.clone(),
                    old_value: old_value.clone(),
                    new_value: new_value.clone()
                }
            );
        }
        else{
            self.remembered_memory_accesses.push(
                HashMapMemoryAccessInfo{
                    index_of_access: new_index_of_memory_access.clone(),
                    key: key.clone(),
                    old_value: old_value.clone(),
                    new_value: old_value.clone()
                }
            );
        }

        self.index_of_last_memory_access = new_index_of_memory_access.clone();

        Ok(old_value)
    }

    pub fn read<CS>(
        &mut self,
        mut cs: CS,
        key: &AllocatedNum<E>
    ) -> Result<Vec<AllocatedNum<E>>, SynthesisError>
        where CS: ConstraintSystem<E>
    {
        self.memory_access(
            cs,
            key,
            None
        )
    }

    pub fn write<CS>(
        &mut self,
        mut cs: CS,
        key: &AllocatedNum<E>,
        new_value: &Vec<AllocatedNum<E>>
    ) -> Result<Vec<AllocatedNum<E>>, SynthesisError>
        where CS: ConstraintSystem<E>
    {
        self.memory_access(
            cs,
            key,
            Some(new_value)
        )
    }

    pub fn finalize<CS>(
        &mut self,
        mut cs: CS
    ) -> Result<(), SynthesisError>
        where CS: ConstraintSystem<E>
    {
        if (self.is_finalized){
            // trying to finalize of finalized hashmap
            return Err(SynthesisError::Unsatisfiable);
        }

        let sorted_memory_accesses = enforce_sort(
            cs.namespace(|| "enforce sort remembered_memory_accesses"),
            self.remembered_memory_accesses.as_slice()
        )?;

        for i in 0..sorted_memory_accesses.len() {
            let mut cs = cs.namespace(|| format!("enforce validity of sorted_memory_accesses[{}]", i));

            if (i == 0) {
                // enforce that sorted_memory_accesses[i].old_value equal to default_value
                for (idx, (a, b)) in sorted_memory_accesses[i].old_value.iter().zip(&self.default_value).enumerate() {
                    cs.enforce(
                        || format!("enforce sorted_memory_accesses.old_value[{}] equal to default_value[{}]", idx, idx),
                        |lc| lc + a.get_variable(),
                        |lc| lc + CS::one(),
                        |lc| lc + b.get_variable()
                    );
                }
            }
            else{
                // enforce that
                // sorted_memory_accesses[i].old_value equal to sorted_memory_accesses[i - 1].new_value
                // or
                // sorted_memory_accesses[i].key not equal to sorted_memory_accesses[i - 1].key and sorted_memory_accesses[i].old_value equal to default_value


                // sorted_memory_accesses[i].old_value equal to sorted_memory_accesses[i - 1].new_value
                let mut ok_read_previous_value = None;
                for (idx, (previous_write, current_read)) in sorted_memory_accesses[i - 1].new_value.iter().zip(&sorted_memory_accesses[i].old_value).enumerate() {
                    let cur_equal = Boolean::from(AllocatedNum::equals(
                        cs.namespace(|| format!("previous_write[{}] equals to current_read[{}]", idx, idx)),
                        &previous_write,
                        &current_read
                    )?);

                    ok_read_previous_value = match ok_read_previous_value {
                        None => Some(cur_equal),
                        Some(ok_read_previous_value) => Some(Boolean::and(
                            cs.namespace(|| format!("ok_read_previous_value at step {}", idx)),
                            &ok_read_previous_value,
                            &cur_equal
                        )?)
                    }
                }
                let ok_read_previous_value = ok_read_previous_value.expect("count of fields in value must be grater than zero");


                // sorted_memory_accesses[i].key not equal to sorted_memory_accesses[i - 1].key and sorted_memory_accesses[i].old_value equal to default_value
                let diff_with_previous_key = Boolean::from(AllocatedNum::equals(
                    cs.namespace(|| "diff_with_previous_key"),
                    &sorted_memory_accesses[i - 1].key,
                    &sorted_memory_accesses[i].key
                )?).not();

                let mut old_value_equal_to_default = None;
                for (idx, (default_value, current_read)) in self.default_value.iter().zip(&sorted_memory_accesses[i].old_value).enumerate() {
                    let cur_equal = Boolean::from(AllocatedNum::equals(
                        cs.namespace(|| format!("default_value[{}] equals to current_read[{}]", idx, idx)),
                        &default_value,
                        &current_read
                    )?);

                    old_value_equal_to_default = match old_value_equal_to_default {
                        None => Some(cur_equal),
                        Some(old_value_equal_to_default) => Some(Boolean::and(
                            cs.namespace(|| format!("old_value_equal_to_default at step {}", idx)),
                            &old_value_equal_to_default,
                            &cur_equal
                        )?)
                    }
                }
                let old_value_equal_to_default = old_value_equal_to_default.expect("count of fields in value must be grater than zero");

                let diff_with_previous_key_and_old_value_equal_to_default = Boolean::and(
                    cs.namespace(|| "diff_with_previous_key_and_old_value_equal_to_default"),
                    &diff_with_previous_key,
                    &old_value_equal_to_default
                )?;


                let valid_memory_access = Boolean::or(
                    cs.namespace(|| format!("{} memory access is valid", i)),
                    &ok_read_previous_value,
                    &diff_with_previous_key_and_old_value_equal_to_default
                )?;

                Boolean::enforce_equal(
                    cs.namespace(|| format!("enforce that {} memory access is valid", i)),
                    &valid_memory_access,
                    &Boolean::Constant(true)
                )?;
            }
        }

        self.is_finalized = true;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use rand::{XorShiftRng, SeedableRng, Rand, Rng};
    use bellman::pairing::bn256::{Bn256, Fr};
    use circuit::test::*;

    #[test]
    fn test_hashmap_gadget() {
        let mut rng = &mut XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        const NUMBER_OF_KEYS_PER_ITERATION: usize = 100;
        const NUMBER_OF_MEMORY_ACCESSES_PER_ITERATION: usize = 3000;
        for iteration in 0..1 {
            for fields in 1..=2 {
                let mut cs = TestConstraintSystem::<Bn256>::new();

                let keys = (0..NUMBER_OF_KEYS_PER_ITERATION).map(|i| Fr::rand(&mut rng)).collect::<Vec<_>>();
                let mut hashmap: HashMap<AllocatedNum<Bn256>, Vec<AllocatedNum<Bn256>>> = HashMap::new();

                let default_value = (0..fields).map(|i| AllocatedNum::alloc(
                    cs.namespace(|| format!("{} element of default_value", i)),
                    || Ok(rng.gen())
                ).unwrap()).collect::<Vec<_>>();

                let mut hashmap_gadget = HashMapGadget::new(
                    cs.namespace(|| "HashMapGadget constructor"),
                    fields,
                    Some(default_value.clone()),
                    None
                ).unwrap();

                for access in 0..NUMBER_OF_MEMORY_ACCESSES_PER_ITERATION {
                    if (access % 2 == 0) { // read
                        let key = AllocatedNum::alloc(
                            cs.namespace(|| format!("key at {} access", access)),
                            || Ok(keys[(rng.next_u32() as usize) % keys.len()])
                        ).unwrap();

                        let gadget_result = hashmap_gadget.read(
                            cs.namespace(|| format!("gadget_result at {} access", access)),
                            &key
                        ).unwrap();

                        let expected = match hashmap.get(&key) {
                            None => default_value.clone(),
                            Some(expected) => expected.clone()
                        };

                        let expected_values = expected.iter().map(|i| i.get_value().unwrap()).collect::<Vec<_>>();
                        let gadget_result_values = gadget_result.iter().map(|i| i.get_value().unwrap()).collect::<Vec<_>>();

                        assert_eq!(expected_values, gadget_result_values);
                    }
                    else { // write
                        let key = AllocatedNum::alloc(
                            cs.namespace(|| format!("key at {} access", access)),
                            || Ok(keys[(rng.next_u32() as usize) % keys.len()])
                        ).unwrap();
                        let new_value = (0..fields).map(|i| AllocatedNum::alloc(
                            cs.namespace(|| format!("new_value in access({}), field({})", access, i)),
                            || Ok(rng.gen())
                        ).unwrap()).collect::<Vec<_>>();

                        let gadget_result = hashmap_gadget.write(
                            cs.namespace(|| format!("gadget_result at {} access", access)),
                            &key,
                            &new_value
                        ).unwrap();

                        let expected = match hashmap.get(&key) {
                            None => default_value.clone(),
                            Some(expected) => expected.clone()
                        };

                        let expected_values = expected.iter().map(|i| i.get_value().unwrap()).collect::<Vec<_>>();
                        let gadget_result_values = gadget_result.iter().map(|i| i.get_value().unwrap()).collect::<Vec<_>>();

                        assert_eq!(expected_values, gadget_result_values);

                        hashmap.insert(key, new_value);
                    }
                }

                hashmap_gadget.finalize(cs.namespace(|| "finalize"));

                assert!(cs.is_satisfied());
            }
        }
    }
}
