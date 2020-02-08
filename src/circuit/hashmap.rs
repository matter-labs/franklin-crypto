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
    SortablePermutationElement
};

use std::cmp::Ordering;

use bellman::pairing::ff::PrimeField;

impl<E: Engine> PermutationElement<E> for Vec<AllocatedNum<E>>
{
    fn switch_2x2<CS>(
        mut cs: CS,
        a: &Self,
        b: &Self,
        switched_on: bool
    ) -> Result<(Self, Self), SynthesisError>
        where CS: ConstraintSystem<E>
    {
        assert_eq!(a.len(), b.len());

        let mut c = vec![];
        let mut d = vec![];

        if (a.len() == 1) {
            let c_value = match (a[0].get_value(), b[0].get_value(), switched_on) {
                (Some(a), Some(b), false) => Some(a),
                (Some(a), Some(b), true) => Some(b),
                (_, _, _) => None
            };
            c.push(AllocatedNum::alloc(
                cs.namespace(|| "c"),
                || c_value.grab()
            )?);

            let d_value = match (a[0].get_value(), b[0].get_value(), switched_on) {
                (Some(a), Some(b), false) => Some(b),
                (Some(a), Some(b), true) => Some(a),
                (_, _, _) => None
            };
            d.push(AllocatedNum::alloc(
                cs.namespace(|| "d"),
                || d_value.grab()
            )?);

            cs.enforce(
                || "(a == c) or (a == d)",
                |lc| lc + a[0].get_variable() - c[0].get_variable(),
                |lc| lc + a[0].get_variable() - d[0].get_variable(),
                |lc| lc
            );
            cs.enforce(
                || "a + b == c + d",
                |lc| lc + a[0].get_variable() + b[0].get_variable(),
                |lc| lc + CS::one(),
                |lc| lc + c[0].get_variable() + d[0].get_variable(),
            );
        }
        else {
            let switch = Boolean::from(AllocatedBit::alloc(
                cs.namespace(|| "switch variable"),
                Some(switched_on)
            )?);

            for (i, (a, b)) in a.iter().zip(b).enumerate() {
                c.push(AllocatedNum::conditionally_select(
                    cs.namespace(|| format!("c[{}]", i)), a, b, &switch.not())?
                );

                d.push(AllocatedNum::conditionally_select(
                    cs.namespace(|| format!("d[{}]", i)), a, b, &switch)?
                );
            }
        }

        Ok((c, d))
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use rand::{XorShiftRng, SeedableRng, Rand, Rng};
    use bellman::pairing::bn256::{Bn256, Fr};
    use circuit::test::*;

    #[test]
    fn test_Vec_AllocatedNum_switch_2x2() {
        let rng = &mut XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        for size in 1..=15 {
            for switched_on in 0..2 {
                let mut cs = TestConstraintSystem::<Bn256>::new();

                let a = (0..size).map(
                    |i| AllocatedNum::alloc(
                        cs.namespace(|| format!("a[{}]", i)),
                        || Ok(rng.gen())
                    ).unwrap()
                ).collect::<Vec<_>>();
                let b = (0..size).map(
                    |i| AllocatedNum::alloc(
                        cs.namespace(|| format!("b[{}]", i)),
                        || Ok(rng.gen())
                    ).unwrap()
                ).collect::<Vec<_>>();

                let (c, d) = <Vec<AllocatedNum<Bn256>> as PermutationElement<Bn256>>::switch_2x2(
                    cs.namespace(|| "switch_2x2"),
                    &a,
                    &b,
                    switched_on != 0
                ).unwrap();

                let a = a.iter().map(|i| i.get_value().unwrap()).collect::<Vec<_>>();
                let b = b.iter().map(|i| i.get_value().unwrap()).collect::<Vec<_>>();
                let c = c.iter().map(|i| i.get_value().unwrap()).collect::<Vec<_>>();
                let d = d.iter().map(|i| i.get_value().unwrap()).collect::<Vec<_>>();

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
}
