use super::*;
use super::ecc::{
    MontgomeryPoint,
    EdwardsPoint
};
use super::boolean::{Boolean,AllocatedBit};
use ::jubjub::*;
use bellman::{
    ConstraintSystem,
    Variable,
    Index
};
use super::lookup::*;
pub use pedersen_hash::Personalization;

impl Personalization {
    fn get_constant_bools(&self) -> Vec<Boolean> {
        self.get_bits()
        .into_iter()
        .map(|e| Boolean::constant(e))
        .collect()
    }
}

extern crate tokio;

use self::tokio::runtime::Runtime;

extern crate futures;

use self::futures::sync::oneshot;

use self::futures::*;
use std::sync::mpsc::channel;
use self::futures::Future;
use self::futures::future::lazy;
use self::tokio::prelude::*;
use std::thread;
use self::futures::future::ok;
use std::error::Error;

pub fn pedersen_hash<E: JubjubEngine, CS>(
    mut cs: CS,
    personalization: Personalization,
    bits: &[Boolean],
    params: &E::Params
) -> Result<EdwardsPoint<E>, SynthesisError>
    where CS: ConstraintSystem<E>
{
    let personalization = personalization.get_constant_bools();
    assert_eq!(personalization.len(), 6);

    let mut edwards_result = None;
    let mut bits = personalization.iter().chain(bits.iter());
    let mut segment_generators = params.pedersen_circuit_generators().iter();
    let boolean_false = Boolean::constant(false);

    let mut segment_i = 0;
    loop {
        let mut segment_result = None;
        let mut segment_windows = &segment_generators.next()
                                                     .expect("enough segments")[..];

        let mut window_i = 0;
        while let Some(a) = bits.next() {
            let b = bits.next().unwrap_or(&boolean_false);
            let c = bits.next().unwrap_or(&boolean_false);

            let tmp = lookup3_xy_with_conditional_negation(
                cs.namespace(|| format!("segment {}, window {}", segment_i, window_i)),
                &[a.clone(), b.clone(), c.clone()],
                &segment_windows[0]
            )?;

            let tmp = MontgomeryPoint::interpret_unchecked(tmp.0, tmp.1);

            match segment_result {
                None => {
                    segment_result = Some(tmp);
                },
                Some(ref mut segment_result) => {
                    *segment_result = tmp.add(
                        cs.namespace(|| format!("addition of segment {}, window {}", segment_i, window_i)),
                        segment_result,
                        params
                    )?;
                }
            }

            segment_windows = &segment_windows[1..];

            if segment_windows.len() == 0 {
                break;
            }

            window_i += 1;
        }

        match segment_result {
            Some(segment_result) => {
                // Convert this segment into twisted Edwards form.
                let segment_result = segment_result.into_edwards(
                    cs.namespace(|| format!("conversion of segment {} into edwards", segment_i)),
                    params
                )?;

                match edwards_result {
                    Some(ref mut edwards_result) => {
                        *edwards_result = segment_result.add(
                            cs.namespace(|| format!("addition of segment {} to accumulator", segment_i)),
                            edwards_result,
                            params
                        )?;
                    },
                    None => {
                        edwards_result = Some(segment_result);
                    }
                }
            },
            None => {
                // We didn't process any new bits.
                break;
            }
        }

        segment_i += 1;
    }

    Ok(edwards_result.unwrap())
}

pub fn my_pedersen_hash<E: JubjubEngine, CS>(
    mut cs: CS,
    personalization: Personalization,
    bits: &[Boolean],
    params: &E::Params
) -> Result<EdwardsPoint<E>, SynthesisError>
    where CS: ConstraintSystem<E>
{
    let input: Vec<bool> = bits.into_iter().map(|bit| bit.get_value().unwrap()).collect();
    let expected = ::pedersen_hash::pedersen_hash::<E, _>(
        personalization,
        input.clone().into_iter(),
        params
    ).into_xy();

    use super::num::AllocatedNum;

    let res_x = AllocatedNum::alloc(cs.namespace(|| "res_x of pedershen hash"), || Ok(expected.0)).unwrap();
    let res_y = AllocatedNum::alloc(cs.namespace(|| "res_x of pedershen hash"), || Ok(expected.1)).unwrap();

    let mut threadCS = cs.add_new_ThreadCS(|| "pedershen_hash thread",
                                         match res_y.get_variable().get_unchecked() {
                                             Index::Input(i) => {
                                                 i
                                             },
                                             Index::Aux(i) => {
                                                 i
                                             }
                                         });

    let mut new_bits: Vec<Boolean> = vec![];

    for (index,i) in bits.iter().enumerate(){
        if (i.is_constant()){
            new_bits.push(i.clone());
        }
        else {
            // TODO unwrap in Option<bool> - when None ???
            let local_var = threadCS.alloc(|| format!("alloc {}-th bit",index), || Ok(i.get_value_field::<E>().unwrap())).unwrap();
            let local_copy = Boolean::Is(AllocatedBit::interpret_unchecked(local_var,i.get_value())?);
            threadCS.add_outside_variable(local_var,i.get_variable().unwrap().get_variable()); // checked - not a constant
            new_bits.push(local_copy);
        }
    }

    let bits = &new_bits;

//    tokio::spawn(future::poll_fn(move || {
        let personalization = personalization.get_constant_bools();
        assert_eq!(personalization.len(), 6);

        let mut edwards_result = None;
        let mut bits = personalization.iter().chain(bits.iter());
        let mut segment_generators = params.pedersen_circuit_generators().iter();
        let boolean_false = Boolean::constant(false);

        let mut segment_i = 0;
        loop {
            let mut segment_result = None;
            let mut segment_windows = &segment_generators.next()
                .expect("enough segments")[..];

            let mut window_i = 0;
            while let Some(a) = bits.next() {
                let b = bits.next().unwrap_or(&boolean_false);
                let c = bits.next().unwrap_or(&boolean_false);

                let tmp = lookup3_xy_with_conditional_negation(
                    threadCS.namespace(|| format!("segment {}, window {}", segment_i, window_i)),
                    &[a.clone(), b.clone(), c.clone()],
                    &segment_windows[0]
                ).unwrap();

                let tmp = MontgomeryPoint::interpret_unchecked(tmp.0, tmp.1);

                match segment_result {
                    None => {
                        segment_result = Some(tmp);
                    },
                    Some(ref mut segment_result) => {
                        *segment_result = tmp.add(
                            threadCS.namespace(|| format!("addition of segment {}, window {}", segment_i, window_i)),
                            segment_result,
                            params
                        ).unwrap();
                    }
                }

                segment_windows = &segment_windows[1..];

                if segment_windows.len() == 0 {
                    break;
                }

                window_i += 1;
            }

            match segment_result {
                Some(segment_result) => {
                    // Convert this segment into twisted Edwards form.
                    let segment_result = segment_result.into_edwards(
                        threadCS.namespace(|| format!("conversion of segment {} into edwards", segment_i)),
                        params
                    ).unwrap();

                    match edwards_result {
                        Some(ref mut edwards_result) => {
                            *edwards_result = segment_result.add(
                                threadCS.namespace(|| format!("addition of segment {} to accumulator", segment_i)),
                                edwards_result,
                                params
                            ).unwrap();
                        },
                        None => {
                            edwards_result = Some(segment_result);
                        }
                    }
                },
                None => {
                    // We didn't process any new bits.
                    break;
                }
            }

            segment_i += 1;
        }

        let edwards_result = edwards_result.unwrap();

        threadCS.add_outside_variable(edwards_result.get_x().get_variable(),res_x.get_variable());
        threadCS.add_outside_variable(edwards_result.get_y().get_variable(),res_y.get_variable());
//        Ok(Async::Ready(()))
//    }));

    Ok(EdwardsPoint::interpret_unchecked(&res_x, &res_y))
}

#[cfg(test)]
mod test {
    use rand::{SeedableRng, Rng, XorShiftRng};
    use super::*;
    use ::circuit::test::*;
    use ::circuit::boolean::{Boolean, AllocatedBit};
    use ::circuit::num::AllocatedNum;
    use bellman::pairing::bls12_381::{Bls12, Fr};
    use bellman::pairing::ff::PrimeField;

    #[test]
    fn my_test_pedersen_hash() {
        let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        let params = &JubjubBls12::new();
        let mut cs = TestConstraintSystem::<Bls12>::new();

        let input: Vec<bool> = (0..(Fr::NUM_BITS * 2)).map(|_| rng.gen()).collect();

        let input_bools: Vec<Boolean> = input.iter().enumerate().map(|(i, b)| {
            Boolean::from(
                AllocatedBit::alloc(cs.namespace(|| format!("input {}", i)), Some(*b)).unwrap()
            )
        }).collect();

        let result = pedersen_hash(
            cs.namespace(|| "pedersen hash"),
            Personalization::NoteCommitment,
            &input_bools,
            params
        ).unwrap();

        let res_x=AllocatedNum::alloc(cs.namespace(|| "res_x"), || Ok(result.get_x().get_value().unwrap())).unwrap();
        let res_y=AllocatedNum::alloc(cs.namespace(|| "res_y"), || Ok(result.get_y().get_value().unwrap())).unwrap();

        cs.enforce(
            || "res_x enforce",
            |lc| lc + res_x.get_variable(),
            |lc| lc + TestConstraintSystem::<Bls12>::one(),
            |lc| lc + result.get_x().get_variable()
        );

        cs.enforce(
            || "res_y enforce",
            |lc| lc + res_y.get_variable(),
            |lc| lc + TestConstraintSystem::<Bls12>::one(),
            |lc| lc + result.get_y().get_variable()
        );

        dbg!(cs.find_unconstrained());
        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_pedersen_hash_constraints() {
        let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        let params = &JubjubBls12::new();
        let mut cs = TestConstraintSystem::<Bls12>::new();

        let input: Vec<bool> = (0..(Fr::NUM_BITS * 2)).map(|_| rng.gen()).collect();

        let input_bools: Vec<Boolean> = input.iter().enumerate().map(|(i, b)| {
            Boolean::from(
                AllocatedBit::alloc(cs.namespace(|| format!("input {}", i)), Some(*b)).unwrap()
            )
        }).collect();

        pedersen_hash(
            cs.namespace(|| "pedersen hash"),
            Personalization::NoteCommitment,
            &input_bools,
            params
        ).unwrap();

        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 1377);
    }

    #[test]
    fn test_pedersen_hash() {
        let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        let params = &JubjubBls12::new();

        for length in 0..751 {
            for _ in 0..5 {
                let mut input: Vec<bool> = (0..length).map(|_| rng.gen()).collect();

                let mut cs = TestConstraintSystem::<Bls12>::new();

                let input_bools: Vec<Boolean> = input.iter().enumerate().map(|(i, b)| {
                    Boolean::from(
                        AllocatedBit::alloc(cs.namespace(|| format!("input {}", i)), Some(*b)).unwrap()
                    )
                }).collect();

                let res = pedersen_hash(
                    cs.namespace(|| "pedersen hash"),
                    Personalization::MerkleTree(1),
                    &input_bools,
                    params
                ).unwrap();

                assert!(cs.is_satisfied());

                let expected = ::pedersen_hash::pedersen_hash::<Bls12, _>(
                    Personalization::MerkleTree(1),
                    input.clone().into_iter(),
                    params
                ).into_xy();

                assert_eq!(res.get_x().get_value().unwrap(), expected.0);
                assert_eq!(res.get_y().get_value().unwrap(), expected.1);

                // Test against the output of a different personalization
                let unexpected = ::pedersen_hash::pedersen_hash::<Bls12, _>(
                    Personalization::MerkleTree(0),
                    input.into_iter(),
                    params
                ).into_xy();

                assert!(res.get_x().get_value().unwrap() != unexpected.0);
                assert!(res.get_y().get_value().unwrap() != unexpected.1);
            }
        }
    }
}

#[cfg(test)]
mod baby_test {
    use rand::{SeedableRng, Rng, XorShiftRng};
    use super::*;
    use ::circuit::test::*;
    use ::circuit::boolean::{Boolean, AllocatedBit};
    use bellman::pairing::bn256::{Bn256, Fr};
    use bellman::pairing::ff::PrimeField;
    use ::alt_babyjubjub::{AltJubjubBn256};

    #[test]
    fn test_baby_pedersen_hash_constraints() {
        let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        let params = &AltJubjubBn256::new();
        let mut cs = TestConstraintSystem::<Bn256>::new();

        let input: Vec<bool> = (0..(Fr::NUM_BITS * 2)).map(|_| rng.gen()).collect();

        let input_bools: Vec<Boolean> = input.iter().enumerate().map(|(i, b)| {
            Boolean::from(
                AllocatedBit::alloc(cs.namespace(|| format!("input {}", i)), Some(*b)).unwrap()
            )
        }).collect();

        pedersen_hash(
            cs.namespace(|| "pedersen hash"),
            Personalization::NoteCommitment,
            &input_bools,
            params
        ).unwrap();

        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 1374);
    }

    #[test]
    fn test_baby_pedersen_hash() {
        let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        let params = &AltJubjubBn256::new();

        for length in 0..739 {
            for _ in 0..5 {
                let mut input: Vec<bool> = (0..length).map(|_| rng.gen()).collect();

                let mut cs = TestConstraintSystem::<Bn256>::new();

                let input_bools: Vec<Boolean> = input.iter().enumerate().map(|(i, b)| {
                    Boolean::from(
                        AllocatedBit::alloc(cs.namespace(|| format!("input {}", i)), Some(*b)).unwrap()
                    )
                }).collect();

                let res = pedersen_hash(
                    cs.namespace(|| "pedersen hash"),
                    Personalization::MerkleTree(0),
                    &input_bools,
                    params
                ).unwrap();

                assert!(cs.is_satisfied());

                let expected = ::pedersen_hash::pedersen_hash::<Bn256, _>(
                    Personalization::MerkleTree(0),
                    input.clone().into_iter(),
                    params
                ).into_xy();

                assert_eq!(res.get_x().get_value().unwrap(), expected.0);
                assert_eq!(res.get_y().get_value().unwrap(), expected.1);

                // Test against the output of a different personalization
                let unexpected = ::pedersen_hash::pedersen_hash::<Bn256, _>(
                    Personalization::MerkleTree(1),
                    input.into_iter(),
                    params
                ).into_xy();

                assert!(res.get_x().get_value().unwrap() != unexpected.0);
                assert!(res.get_y().get_value().unwrap() != unexpected.1);
            }
        }
    }
}
