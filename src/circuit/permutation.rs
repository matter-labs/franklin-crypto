extern crate bit_vec;

use self::bit_vec::BitVec;

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

use std::cmp::Ordering;

pub trait PermutationElement<E: Engine>: Sized + Clone {
    fn switch_2x2<CS>(
        cs: CS,
        a: &Self,
        b: &Self,
        switched_on: bool
    ) -> Result<(Self, Self), SynthesisError>
        where CS: ConstraintSystem<E>;
}

pub trait SortablePermutationElement<E: Engine>: PermutationElement<E> {
    fn cmp(
        a: &Self,
        b: &Self,
    ) -> Ordering;

    fn enforce_leq<CS>(
        cs: CS,
        a: &Self,
        b: &Self
    ) -> Result<(), SynthesisError>
        where CS: ConstraintSystem<E>;
}

pub fn is_valid_permutation(
    permutation: &[usize]
) -> bool
{
    let mut set: std::collections::HashSet<usize> = std::collections::HashSet::with_capacity(permutation.len());
    for element in permutation.iter() {
        if *element >= permutation.len() {
            return false;
        }
        if set.contains(element) {
            return false;
        }
        set.insert(*element);
    }
    return true;
}

fn enforce_permutation_recursive<E: Engine, CS, PE>(
    mut cs: CS,
    original: &[PE],
    permutation: &[usize]
) -> Result<Vec<PE>, SynthesisError>
    where CS: ConstraintSystem<E>,
          PE: PermutationElement<E>
{
    assert_eq!(original.len(), permutation.len());

    match original.len() {
        1 => Ok(vec![original[0].clone()]),
        2 => {
            let (c, d) = PE::switch_2x2(
                cs.namespace(|| "switch_2x2"),
                &original[0],
                &original[1],
                permutation[0] != 0
            )?;
            Ok(vec![c, d])
        }
        _ => {
            let n = original.len();
            // position in permutation of each element from 0 to n - 1
            let mut pos_in_permutation = vec![0; n];
            for i in 0..n {
                pos_in_permutation[permutation[i]] = i;
            }

            let mut front_layer_switches_on = BitVec::from_elem(n / 2, false);
            let mut back_layer_switches_on = BitVec::from_elem(n / 2, false);

            // permutations of recursive tasks
            let mut perm_left: Vec<usize> = vec![0; n / 2];
            let mut perm_right: Vec<usize> = vec![0; (n + 1) / 2];

            // considered positions in permutation
            let mut used_positions = BitVec::from_elem(n, false);

            for i in (0..n).rev() {
                if (used_positions.get(i).expect("used_positions must contain n elements")) {
                    continue;
                }

                if (n % 2 == 1 && i == n - 1) {
                    used_positions.set(i, true);
                    perm_right[i / 2] = permutation[i] / 2;

                    // start with neighbour by value
                    let mut current_value = permutation[i] ^ 1;
                    while (current_value != n) {
                        // drop element with (permutation[index] == current_value) to the left subtask
                        assert_eq!(used_positions.get(pos_in_permutation[current_value]), Some(false));
                        used_positions.set(pos_in_permutation[current_value], true);
                        perm_left[pos_in_permutation[current_value] / 2] = current_value / 2;

                        // mark switch with index equal to (pos_in_permutation[current_value] / 2)
                        front_layer_switches_on.set(pos_in_permutation[current_value] / 2, pos_in_permutation[current_value] % 2 == 1);
                        // change current_value's focus to the neighbour in permutation
                        current_value = permutation[pos_in_permutation[current_value] ^ 1];

                        // drop element with (permutation[index] == current_value) to the right subtask
                        assert_eq!(used_positions.get(pos_in_permutation[current_value]), Some(false));
                        used_positions.set(pos_in_permutation[current_value], true);
                        perm_right[pos_in_permutation[current_value] / 2] = current_value / 2;

                        // change current_value's focus to the neighbour by value
                        current_value = current_value ^ 1;
                    }
                }
                else {
                    used_positions.set(i, true);
                    perm_right[i / 2] = permutation[i] / 2;

                    // start with neighbour in permutation
                    let mut current_value = permutation[i ^ 1];
                    loop {
                        // drop element with (permutation[index] == current_value) to the left subtask
                        assert_eq!(used_positions.get(pos_in_permutation[current_value]), Some(false));
                        used_positions.set(pos_in_permutation[current_value], true);
                        perm_left[pos_in_permutation[current_value] / 2] = current_value / 2;

                        // mark switch with index equal to (pos_in_permutation[current_value] / 2)
                        front_layer_switches_on.set(pos_in_permutation[current_value] / 2, pos_in_permutation[current_value] % 2 == 1);
                        // change current_value's focus to the neighbour by value
                        current_value = current_value ^ 1;

                        if (current_value == permutation[i]) {
                            break;
                        }

                        // drop element with (permutation[index] == current_value) to the right subtask
                        assert_eq!(used_positions.get(pos_in_permutation[current_value]), Some(false));
                        used_positions.set(pos_in_permutation[current_value], true);
                        perm_right[pos_in_permutation[current_value] / 2] = current_value / 2;

                        // change current_value's focus to the neighbour in permutation
                        current_value = permutation[pos_in_permutation[current_value] ^ 1];
                    }
                }
            }

            let mut left: Vec<PE> = vec![];
            let mut right: Vec<PE> = vec![];
            for i in (0..n).step_by(2) {
                if (i + 1 < n) {
                    let (l, r) = PE::switch_2x2(
                        cs.namespace(|| format!("switch of front layer with index {}", i / 2)),
                        &original[i],
                        &original[i + 1],
                        front_layer_switches_on.get(i / 2).expect("front_layer_switches_on must contain n / 2 elements")
                    )?;
                    left.push(l);
                    right.push(r);
                }
                else {
                    right.push(original[i].clone());
                }
            }

            // result of recursive tasks
            let left = enforce_permutation_recursive(
                cs.namespace(|| "left recursive task"),
                left.as_slice(),
                perm_left.as_slice(),
            )?;
            assert_eq!(left.len(), n / 2);
            let right = enforce_permutation_recursive(
                cs.namespace(|| "right recursive task"),
                right.as_slice(),
                perm_right.as_slice(),
            )?;
            assert_eq!(right.len(), (n + 1) / 2);

            for i in 0..n {
                if !(n % 2 == 1 && i == n - 1) && !(n % 2 == 1 && pos_in_permutation[i] == n - 1) {
                    back_layer_switches_on.set(
                        i / 2,
                        front_layer_switches_on.get(pos_in_permutation[i] / 2).expect("front_layer_switches_on must contain n / 2 elements")
                            ^ (pos_in_permutation[i] % 2 == 0) ^ (i % 2 == 0)
                    );
                }
            }

            let mut result_of_permutation: Vec<PE> = vec![];
            for i in (0..n).step_by(2) {
                if (i + 1 < n) {
                    let (l, r) = PE::switch_2x2(
                        cs.namespace(|| format!("switch of back layer with index {}", i / 2)),
                        &left[i / 2],
                        &right[i / 2],
                        back_layer_switches_on.get(i / 2).expect("back_layer_switches_on must contain n / 2 elements")
                    )?;
                    result_of_permutation.push(l);
                    result_of_permutation.push(r);
                }
                else {
                    result_of_permutation.push(right.last().expect("subtask result can't be empty").clone());
                }
            }

            Ok(result_of_permutation)
        }
    }
}

/// AS-Waksman permutation network
pub fn enforce_permutation<E: Engine, CS, PE>(
    mut cs: CS,
    original: &[PE],
    permutation: &[usize]
) -> Result<Vec<PE>, SynthesisError>
    where CS: ConstraintSystem<E>,
          PE: PermutationElement<E>
{
    assert!(is_valid_permutation(permutation), "permutation is not valid");

    Ok(enforce_permutation_recursive(
        cs,
        original,
        permutation
    )?)
}

pub fn enforce_sort<E: Engine, CS, SPE>(
    mut cs: CS,
    original: &[SPE]
) -> Result<Vec<SPE>, SynthesisError>
    where CS: ConstraintSystem<E>,
          SPE: SortablePermutationElement<E>
{
    let mut original_sorted: Vec<_> = original.iter().enumerate().collect();
    original_sorted.sort_by(|lhs: &(usize, &SPE), rhs: &(usize, &SPE)| {
        SPE::cmp(lhs.1, rhs.1)
    });
    let mut permutation: Vec<usize> = vec![0; original.len()];
    for (position_in_sorted_version, (index_in_original, value)) in original_sorted.iter().enumerate() {
        permutation[*index_in_original] = position_in_sorted_version;
    }
    let result = enforce_permutation(
        cs.namespace(|| "AS-Waksman permutation network"),
        original,
        permutation.as_slice()
    )?;
    for i in 1..result.len() {
        SPE::enforce_leq(
            cs.namespace(|| format!("enforce comparing elements {} and {}", i - 1, i)),
            &result[i - 1],
            &result[i]
        )?;
    }
    Ok(result)
}

#[cfg(test)]
mod test {
    use super::*;
    use rand::{XorShiftRng, SeedableRng, Rand, Rng};
    use bellman::pairing::bn256::{Bn256, Fr};
    use circuit::test::*;
    use bellman::pairing::ff::PrimeField;

    #[derive(Clone)]
    struct TestSPE<E: Engine>
    {
        pub field: Vec<AllocatedNum<E>>
    }

    impl<E: Engine> PermutationElement<E> for TestSPE<E>
    {
        fn switch_2x2<CS>(
            mut cs: CS,
            a: &Self,
            b: &Self,
            switched_on: bool
        ) -> Result<(Self, Self), SynthesisError>
            where CS: ConstraintSystem<E>
        {
            assert_eq!(a.field.len(), b.field.len());

            let mut c = TestSPE { field: vec![] };
            let mut d = TestSPE { field: vec![] };

            if (a.field.len() == 1) {
                let c_value = match (a.field[0].get_value(), b.field[0].get_value(), switched_on) {
                    (Some(a), Some(b), false) => Some(a),
                    (Some(a), Some(b), true) => Some(b),
                    (_, _, _) => None
                };
                c.field.push(AllocatedNum::alloc(
                    cs.namespace(|| "c"),
                    || c_value.grab()
                )?);

                let d_value = match (a.field[0].get_value(), b.field[0].get_value(), switched_on) {
                    (Some(a), Some(b), false) => Some(b),
                    (Some(a), Some(b), true) => Some(a),
                    (_, _, _) => None
                };
                d.field.push(AllocatedNum::alloc(
                    cs.namespace(|| "d"),
                    || d_value.grab()
                )?);

                cs.enforce(
                    || "(a == c) or (a == d)",
                    |lc| lc + a.field[0].get_variable() - c.field[0].get_variable(),
                    |lc| lc + a.field[0].get_variable() - d.field[0].get_variable(),
                    |lc| lc
                );
                cs.enforce(
                    || "a + b == c + d",
                    |lc| lc + a.field[0].get_variable() + b.field[0].get_variable(),
                    |lc| lc + CS::one(),
                    |lc| lc + c.field[0].get_variable() + d.field[0].get_variable(),
                );
            }
            else {
                let switch = Boolean::from(AllocatedBit::alloc(
                    cs.namespace(|| "switch variable"),
                    Some(switched_on)
                )?);

                for (i, (a, b)) in a.field.iter().zip(&b.field).enumerate() {
                    c.field.push(AllocatedNum::conditionally_select(
                        cs.namespace(|| format!("c[{}]", i)), a, b, &switch.not()
                    )?);

                    d.field.push(AllocatedNum::conditionally_select(
                        cs.namespace(|| format!("d[{}]", i)), a, b, &switch
                    )?);
                }
            }

            Ok((c, d))
        }
    }

    impl<E: Engine> SortablePermutationElement<E> for TestSPE<E>
    {
        fn cmp(
            a: &Self,
            b: &Self,
        ) -> Ordering
        {
            for (a, b) in a.field.iter().zip(&b.field) {
                let comparison_result = match (a.get_value(), b.get_value()) {
                    (Some(a_value), Some(b_value)) => {
                        let a_repr = a_value.into_repr();
                        let b_repr = b_value.into_repr();

                        a_repr.cmp(&b_repr)
                    }
                    (None, Some(_)) => Ordering::Less,
                    (None, None) => Ordering::Equal,
                    (Some(_), None) => Ordering::Greater
                };
                if (comparison_result != Ordering::Equal) {
                    return comparison_result;
                }
            }
            return Ordering::Equal;
        }

        fn enforce_leq<CS>(
            mut cs: CS,
            a: &Self,
            b: &Self
        ) -> Result<(), SynthesisError>
            where CS: ConstraintSystem<E>
        {
            let mut is_prefixes_equal = Boolean::from(
                AllocatedBit::alloc(
                    cs.namespace(|| "is_prefixes_equal"),
                    Some(true)
                )?
            );
            Boolean::enforce_equal(
                cs.namespace(|| "is_prefixes_equal start value"),
                &is_prefixes_equal,
                &Boolean::Constant(true)
            )?;

            let mut lt = Boolean::from(
                AllocatedBit::alloc(
                    cs.namespace(|| "lt"),
                    Some(false)
                )?
            );
            Boolean::enforce_equal(
                cs.namespace(|| "lt start value"),
                &lt,
                &Boolean::Constant(false)
            )?;

            for (i, (a, b)) in a.field.iter().zip(&b.field).enumerate() {
                let comparison_result = AllocatedNum::less_than(
                    cs.namespace(|| format!("comparison_result of a[{}] and b[{}]", i, i)),
                    a,
                    b
                )?;

                let a_lt_b_here_and_prefixes_are_equal = Boolean::and(
                    cs.namespace(|| format!("a[{}] less than b[{}] and suffixes are equal at element with index {}", i, i, i)),
                    &comparison_result,
                    &is_prefixes_equal
                )?;

                lt = Boolean::or(
                    cs.namespace(|| format!("lt after {} element consideration", i + 1)),
                    &lt,
                    &a_lt_b_here_and_prefixes_are_equal
                )?;

                let a_equals_b = &Boolean::from(AllocatedNum::equals(
                    cs.namespace(|| format!("a[{}] equal to b[{}]", i, i)),
                    a,
                    b
                )?);

                is_prefixes_equal = Boolean::and(
                    cs.namespace(|| format!("is_prefixes_equal after {} element consideration", i + 1)),
                    &is_prefixes_equal,
                    &a_equals_b
                )?;
            }

            let leq = Boolean::or(
                cs.namespace(|| "leq"),
                &lt,
                &is_prefixes_equal
            )?;
            Boolean::enforce_equal(
                cs.namespace(|| "leq is true"),
                &leq,
                &Boolean::Constant(true)
            )?;

            Ok(())
        }
    }

    #[test]
    fn test_switch_2x2() {
        let rng = &mut XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        for size in 1..=15 {
            for switched_on in 0..2 {
                let mut cs = TestConstraintSystem::<Bn256>::new();

                let a = TestSPE {
                    field: (0..size).map(
                        |i| AllocatedNum::alloc(
                            cs.namespace(|| format!("a[{}]", i)),
                            || Ok(rng.gen())
                        ).unwrap()
                    ).collect::<Vec<_>>()
                };
                let b = TestSPE {
                    field: (0..size).map(
                        |i| AllocatedNum::alloc(
                            cs.namespace(|| format!("b[{}]", i)),
                            || Ok(rng.gen())
                        ).unwrap()
                    ).collect::<Vec<_>>()
                };

                let (c, d) = <TestSPE<Bn256> as PermutationElement<Bn256>>::switch_2x2(
                    cs.namespace(|| "switch_2x2"),
                    &a,
                    &b,
                    switched_on != 0
                ).unwrap();

                let a = a.field.iter().map(|i| i.get_value().unwrap()).collect::<Vec<_>>();
                let b = b.field.iter().map(|i| i.get_value().unwrap()).collect::<Vec<_>>();
                let c = c.field.iter().map(|i| i.get_value().unwrap()).collect::<Vec<_>>();
                let d = d.field.iter().map(|i| i.get_value().unwrap()).collect::<Vec<_>>();

                if (switched_on == 0) {
                    assert_eq!(a, c);
                    assert_eq!(b, d);
                }
                else {
                    assert_eq!(a, d);
                    assert_eq!(b, c);
                }

                assert!(cs.is_satisfied());
            }
        }
    }

    #[test]
    fn test_enforce_sort() {
        let rng = &mut XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        for iteration in 0..5 {
            for size in 2..=50 {
                for fields in 1..=2 {
                    let mut cs = TestConstraintSystem::<Bn256>::new();

                    let original_vector = (0..size).map(|i|
                        TestSPE{
                            field: (0..fields).map(|j|
                                AllocatedNum::alloc(
                                    cs.namespace(|| format!("input {} {} (size({}), fields({}))", i, j, size, fields)),
                                    || Ok(rng.gen())
                                ).unwrap()
                            ).collect::<Vec<_>>()
                        }
                    ).collect::<Vec<_>>();

                    let mut expected_sorted = original_vector.clone();
                    expected_sorted.sort_by(|lhs: &TestSPE<Bn256>, rhs: &TestSPE<Bn256>| {
                        <TestSPE<Bn256> as SortablePermutationElement<Bn256>>::cmp(lhs, rhs)
                    });

                    let sorted = enforce_sort(
                        cs.namespace(|| "enforce_sort"),
                        original_vector.as_slice()
                    ).unwrap();

                    assert_eq!(expected_sorted.len(), sorted.len());

                    for (expected_i, result_i) in expected_sorted.iter().zip(&sorted) {
                        assert_eq!(expected_i.field.len(), result_i.field.len());
                        for (expected, result) in expected_i.field.iter().zip(&result_i.field) {
                            assert_eq!(expected.get_value().unwrap(), result.get_value().unwrap());
                        }
                    }

                    assert!(cs.is_satisfied());
                }
            }
        }
    }
}
