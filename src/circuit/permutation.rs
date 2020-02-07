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

pub trait PermutationField<E: Engine>: Sized + Clone {
    fn switch_2x2<CS>(
        cs: CS,
        a: &Self,
        b: &Self,
        switched_on: bool
    ) -> Result<(Self, Self), SynthesisError>
        where CS: ConstraintSystem<E>;
}

/// AS-Waksman permutation network
/// Caller be responsible for validity of permutation
pub fn enforce_permutation<E, CS, PF>(
    mut cs: CS,
    original: &[PF],
    permutation: &[usize]
) -> Result<(Vec<PF>), SynthesisError>
    where CS: ConstraintSystem<E>,
          E: Engine,
          PF: PermutationField<E>
{
    assert_eq!(original.len(), permutation.len());

    match permutation.len(){
        1 => Ok(vec![original[0].clone()]),
        2 => {
            let (c, d) = PF::switch_2x2(
                cs.namespace(|| "switch_2x2"),
                &original[0],
                &original[1],
                permutation[0] != 0
            )?;
            Ok(vec![c, d])
        }
        _ => {
            Ok(vec![])
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use rand::{XorShiftRng, SeedableRng, Rand, Rng};
    use bellman::pairing::bn256::{Bn256, Fr};
    use circuit::test::*;

    #[test]
    fn test_switch_2x2() {
        let rng = &mut XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        for size in 1..10{
            for switched_on in 0..2{
                let mut cs = TestConstraintSystem::<Bn256>::new();

                let a = (0..size).map(
                    |i| AllocatedNum::alloc(
                        cs.namespace(|| format!("a[{}]", i)),
                        || Ok(Fr::rand(rng))
                    ).unwrap()
                ).collect::<Vec<_>>();
                let b = (0..size).map(
                    |i| AllocatedNum::alloc(
                        cs.namespace(|| format!("b[{}]", i)),
                        || Ok(Fr::rand(rng))
                    ).unwrap()
                ).collect::<Vec<_>>();

                let (c, d) = <Vec<AllocatedNum<Bn256>> as PermutationField<Bn256>>::switch_2x2(
                    cs.namespace(|| "switch_2x2"),
                    &a,
                    &b,
                    switched_on != 0
                ).unwrap();

                let a = a.iter().map(|i| i.get_value().unwrap()).collect::<Vec<_>>();
                let b = b.iter().map(|i| i.get_value().unwrap()).collect::<Vec<_>>();
                let c = c.iter().map(|i| i.get_value().unwrap()).collect::<Vec<_>>();
                let d = d.iter().map(|i| i.get_value().unwrap()).collect::<Vec<_>>();

                if (switched_on == 0){
                    assert_eq!(a, c);
                    assert_eq!(b, d);
                }
                else{
                    assert_eq!(a, d);
                    assert_eq!(b, c);
                }

                assert!(cs.is_satisfied());
            }
        }
    }
}
