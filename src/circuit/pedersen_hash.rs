use super::*;
use super::ecc::{
    MontgomeryPoint,
    EdwardsPoint
};
use super::boolean::{Boolean,AllocatedBit};
use ::jubjub::*;
use bellman::{
    ConstraintSystem,
    LinearCombination,
    ThreadConstraintSystem,
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

use ::alt_babyjubjub::AltJubjubBn256;

lazy_static!{
    static ref jubjub_params: AltJubjubBn256 = AltJubjubBn256::new();
}

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

use bellman::pairing::ff::Field;
use super::num::AllocatedNum;

pub fn my_pedersen_hash<E: JubjubEngine, CS>(
    mut cs: CS,
    personalization: Personalization,
    bits: &[Boolean],
    params: &'static E::Params
) -> Result<EdwardsPoint<E>, SynthesisError>
    where CS: ConstraintSystem<E>
{
    let input: Vec<bool> = bits.into_iter().map(|bit| bit.get_value().unwrap()).collect();
    let expected = ::pedersen_hash::pedersen_hash::<E, _>(
        personalization,
        input.clone().into_iter(),
        params
    ).into_xy();

    let res_x = AllocatedNum::alloc_thread_output(cs.namespace(|| "res_x of pedershen hash"), || Ok(expected.0)).unwrap();
    let res_y = AllocatedNum::alloc_thread_output(cs.namespace(|| "res_y of pedershen hash"), || Ok(expected.1)).unwrap();

    let res_x_variable = res_x.get_variable();
    let res_y_variable = res_y.get_variable();

    let mut bits: Vec<Boolean> = bits.iter().map(|a| a.clone()).collect();

    use std::sync::{Arc};
    let params_arc= Arc::new(params);

    let sender = cs.reserve_memory_for_thread_info();

    tokio::spawn(future::poll_fn(move || {
        println!("start of spawn");
        let mut threadCS = ThreadConstraintSystem::<E, CS>::new();

        let mut new_bits = vec![];

        for (index,i) in bits.iter().enumerate(){
            if (i.is_constant()){
                new_bits.push(i.clone());
            }
            else {
                // TODO unwrap in Option<bool> - when None ???
                let local_var = threadCS.alloc(|| format!("alloc {}-th bit", index), || Ok(i.get_value_field::<E>().unwrap())).unwrap();
                let local_copy = Boolean::Is(AllocatedBit::interpret_unchecked(local_var,i.get_value()));
                threadCS.add_outside_variable(local_var,i.get_variable().unwrap().get_variable()); // checked - not a constant
                new_bits.push(local_copy);
            }
        }

        bits = new_bits;

        let params= &Arc::clone(&params_arc);

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

        threadCS.add_thread_output(edwards_result.get_x().get_variable(),res_x_variable);
        threadCS.add_thread_output(edwards_result.get_y().get_variable(),res_y_variable);
        sender.send(threadCS.get_rem_info());
        println!("finished spawn");
        Ok(Async::Ready(()))
    }));

    Ok(EdwardsPoint::interpret_unchecked(&res_x, &res_y))
}

use bellman::pairing::bn256::{Bn256};

lazy_static!{
    static ref hash_params: AltJubjubBn256 = AltJubjubBn256::new();
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
    use bellman::groth16::*;
    use bellman::pairing::ff::Field;

    #[test]
    fn test_barik1() {
        use std::time::{Duration, Instant};
        let start=Instant::now();

        tokio::run(future::poll_fn(move || {
            let SSS = 1500;

            let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

            let mut inputs: Vec<Vec<bool>> = vec![];
            for _ in 0..10{
                inputs.push((0..500).map(|_| rng.gen()).collect());
            }

            let point1 = Instant::now();

            let mut cs = ThreadProvingAssignment::<Bn256>::new();

            cs.alloc_input(|| "", || Ok(bellman::pairing::bn256::Fr::one())).unwrap();

            let mut input_bools: Vec<Boolean> = inputs[0].iter().enumerate().map(|(i, b)| {
                Boolean::from(
                    AllocatedBit::alloc(cs.namespace(|| format!("input {}", i)), Some(*b)).unwrap()
                )
            }).collect();

            for iteration in 0..SSS{
                if (iteration>0&&iteration<10){
                    input_bools = inputs[iteration].iter().enumerate().map(|(i, b)| {
                        Boolean::from(
                            AllocatedBit::alloc(cs.namespace(|| format!("input {}", i)), Some(*b)).unwrap()
                        )
                    }).collect();
                }
                my_pedersen_hash(
                    cs.namespace(|| "pedersen hash"),
                    Personalization::NoteCommitment,
                    &input_bools,
                    &hash_params
                ).unwrap();
                let mut array = vec![];
                for j in 0..iteration{
                    array.push(cs.alloc(|| "this guy", || Ok(
                        if (j%2==0){
                            bellman::pairing::bn256::Fr::one()
                        }
                        else{
                            bellman::pairing::bn256::Fr::zero()
                        }
                    )).unwrap());
                    if (j%4==3){
                        // 1 0 1 0
                        cs.enforce(
                            || "one more enforce",
                            |lc| lc + array[j-3] + array[j-2],
                            |lc| lc + ThreadProvingAssignment::<Bn256>::one(),
                            |lc| lc + array[j-1],
                        );
                        cs.enforce(
                            || "one more enforce",
                            |lc| lc + array[j-3],
                            |lc| lc + array[j-2],
                            |lc| lc + array[j],
                        );
                    }
                }
            }

            let point2 = Instant::now();

            let res1=cs.make_proving_assignment().unwrap();

            let point3 = Instant::now();

            println!("start standart hash calculating");
            println!("start standart hash calculating");
            println!("start standart hash calculating");
            println!("start standart hash calculating");
            println!("start standart hash calculating");
            println!("start standart hash calculating");
            println!("start standart hash calculating");
            println!("start standart hash calculating");

            let mut cs = ProvingAssignment::<Bn256>::new();

            cs.alloc_input(|| "", || Ok(bellman::pairing::bn256::Fr::one())).unwrap();

            let mut input_bools: Vec<Boolean> = inputs[0].iter().enumerate().map(|(i, b)| {
                Boolean::from(
                    AllocatedBit::alloc(cs.namespace(|| format!("input {}", i)), Some(*b)).unwrap()
                )
            }).collect();

            for iteration in 0..SSS{
                if (iteration>0&&iteration<10){
                    input_bools = inputs[iteration].iter().enumerate().map(|(i, b)| {
                        Boolean::from(
                            AllocatedBit::alloc(cs.namespace(|| format!("input {}", i)), Some(*b)).unwrap()
                        )
                    }).collect();
                }
                pedersen_hash(
                    cs.namespace(|| "pedersen hash"),
                    Personalization::NoteCommitment,
                    &input_bools,
                    &hash_params
                ).unwrap();
                let mut array = vec![];
                for j in 0..iteration{
                    array.push(cs.alloc(|| "this guy", || Ok(
                        if (j%2==0){
                            bellman::pairing::bn256::Fr::one()
                        }
                        else{
                            bellman::pairing::bn256::Fr::zero()
                        }
                    )).unwrap());
                    if (j%4==3){
                        // 1 0 1 0
                        cs.enforce(
                            || "one more enforce",
                            |lc| lc + array[j-3] + array[j-2],
                            |lc| lc + ProvingAssignment::<Bn256>::one(),
                            |lc| lc + array[j-1],
                        );
                        cs.enforce(
                            || "one more enforce",
                            |lc| lc + array[j-3],
                            |lc| lc + array[j-2],
                            |lc| lc + array[j],
                        );
                    }
                }
            }

            let res2=cs;

            assert!(res1==res2);
            assert!(res1.eq(&res2));

            let point4 = Instant::now();

            println!("time for paralel calculating :: {:?}",point3.duration_since(point1));
            println!("time for merge paralel calculating :: {:?}",point3.duration_since(point2));
            println!("time for linear calculating :: {:?}",point4.duration_since(point3));

            Ok(Async::Ready(()))
        }));

        println!("time for all :: {:?}",Instant::now().duration_since(start));
    }

    #[test]
    fn test_my_pedersen_hash() {
        use std::time::{Duration, Instant};
        let start=Instant::now();

        tokio::run(future::poll_fn(move || {

            for _ in 0..30000 {
                println!("at start of iteration");
                let mut cs = ThreadProvingAssignment::<Bn256>::new();

                cs.alloc_input(|| "", || Ok(bellman::pairing::bn256::Fr::one())).unwrap();

                let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
//                let params=&AltJubjubBn256::new();

                let input: Vec<bool> = (0..500).map(|_| rng.gen()).collect();

                let input_bools: Vec<Boolean> = input.iter().enumerate().map(|(i, b)| {
                    Boolean::from(
                        AllocatedBit::alloc(cs.namespace(|| format!("input {}", i)), Some(*b)).unwrap()
                    )
                }).collect();

                my_pedersen_hash(
                    cs.namespace(|| "pedersen hash"),
                    Personalization::NoteCommitment,
                    &input_bools,
                    &hash_params
                ).unwrap();
            }
            Ok(Async::Ready(()))
        }));
        println!("time for all :: {:?}",Instant::now().duration_since(start));
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
