use super::*;

use super::witness::{
    IntegerPermutation,
    AsWaksmanTopology,
    AsWaksmanRoute
};

pub fn order_into_switches_set<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    permutation: &IntegerPermutation
) -> Result<Vec<Vec<Boolean>>, SynthesisError> {
    let mut layers = vec![];

    let size = permutation.size();

    let topology = AsWaksmanTopology::new(size);

    // now calculate the witness for gate assignments

    let router = AsWaksmanRoute::new(permutation);

    // now route elements through the network. Deterministically do the bookkeeping of the variables in a plain array

    let num_columns = AsWaksmanTopology::num_columns(topology.size);
    let mut routed_packages = std::collections::HashSet::new();

    for column_idx in 0..num_columns {
        // this is just a bookkeeping variable and is deterministic
        let mut switches = vec![];
        for packet_idx in 0..size {
            if topology.topology[column_idx][packet_idx].0 == topology.topology[column_idx][packet_idx].1 {
                // straight switch, there is no need to allocate witness
                let routed_into_idx = topology.topology[column_idx][packet_idx].0;
                routed_packages.insert(routed_into_idx);
            } else {
                // validity check
                let a = router.switches[column_idx].get(&packet_idx);
                let b = if packet_idx > 0 {
                    router.switches[column_idx].get(&(packet_idx - 1))
                } else {
                    None
                };

                // get value to make a witness
                let switch_value = if a.is_some() {
                    a.cloned()
                } else if b.is_some() {
                    b.cloned()
                } else {
                    None
                };

                // in normal workflow we would select an index to which it's routed.
                // here we select a value instead, and always route as a cross, but value can be chosen
                // tricky part is that we have to route both variables at once to properly make a cross

                let routed_into_straght = topology.topology[column_idx][packet_idx].0; // this is a straight index
                let routed_into_cross = topology.topology[column_idx][packet_idx].1; // this is a cross index

                // may be we have already routed a pair, so quickly check
                if routed_packages.contains(&routed_into_straght) || routed_packages.contains(&routed_into_cross) {
                    continue;
                }

                // now find a pair of the variable at this index. It should be a variable for which
                // straight == this_cross and vice versa

                let mut another_idx = None;
                for idx in (packet_idx + 1)..topology.size {
                    let another_straght = topology.topology[column_idx][idx].0; // this is a straight index
                    let another_cross = topology.topology[column_idx][idx].1; // this is a cross index
                    if routed_into_straght == another_cross && routed_into_cross == another_straght {
                        another_idx = Some(idx);
                        break;
                    }
                }        
                assert!(another_idx.is_some());

                let boolean_switch = Boolean::from(AllocatedBit::alloc(
                    cs,
                    switch_value
                )?); 

                routed_packages.insert(routed_into_straght);
                routed_packages.insert(routed_into_cross);

                switches.push(boolean_switch);
            }
        }
        layers.push(switches);
        // check that all are routed
        let mut sorted_copy: Vec<_> = routed_packages.drain().collect();
        sorted_copy.sort();
        let min = sorted_copy.drain(0..1).next().expect("must contain an element");
        let mut prev = min;
        for el in sorted_copy.into_iter() {
            assert!(el != prev);
            prev = el;
        }

        let max = prev;

        assert_eq!(min, 0, "permutation should start with 0");
        assert_eq!(max, size-1, "permutation should not contain spaces");
    }

    Ok(layers)
}


/// prove permutation by routing elements through the permutation network
/// Topology is calculated exclusively based on the size on the network, 
/// and permuted elements can be anything. Caller be responsible for validity
/// if elements are unique or not
pub fn prove_permutation_using_switches_witness<E, CS>(
    cs: &mut CS,
    original: &[AllocatedNum<E>],
    permuted: &[AllocatedNum<E>],
    switches_layes: &Vec<Vec<Boolean>>,
) -> Result<(), SynthesisError>
    where CS: ConstraintSystem<E>,
          E: Engine
{
    assert_eq!(original.len(), permuted.len());
    // First make a topology

    let topology = AsWaksmanTopology::new(original.len());

    // now route elements through the network. Deterministically do the bookkeeping of the variables in a plain array

    let num_columns = AsWaksmanTopology::num_columns(topology.size);
    assert_eq!(num_columns, switches_layes.len());

    let mut permutation: Vec<Option<AllocatedNum<E>>> = original.iter().map(|e| Some(e.clone())).collect();

    // let mut permutation: Vec<Option<AllocatedNum<E>>> = permuted.iter().map(|e| Some(e.clone())).collect();

    let mut switch_count = 0;

    for column_idx in 0..num_columns {
        // this is just a bookkeeping variable and is deterministic
        let mut result_of_this_column: Vec<Option<AllocatedNum<E>>> = vec![None; topology.size];
        let mut switches_it = (&switches_layes[column_idx]).iter();
        for packet_idx in 0..topology.size {
            if topology.topology[column_idx][packet_idx].0 == topology.topology[column_idx][packet_idx].1 {
                // straight switch, there is no need to allocate witness
                let routed_into_idx = topology.topology[column_idx][packet_idx].0;
                let previous_level_variable = permutation.get(packet_idx).expect("must be a variable for this packet idx");
                // let previous_level_variable = previous_level_variable.ok_or(SynthesisError::Unsatisfiable)?.as_ref();
                let previous_level_variable = previous_level_variable.ok_or(SynthesisError::Unsatisfiable)?;
                // let new_variable_for_this_level = AllocatedNum::alloc(
                //     cs,
                //     || {
                //         let value = *previous_level_variable.get_value().get()?;

                //         Ok(value)
                //     }
                // )?;

                let new_variable_for_this_level = previous_level_variable;

                result_of_this_column[routed_into_idx] = Some(new_variable_for_this_level);
            } else {
                // in normal workflow we would select an index to which it's routed.
                // here we select a value instead, and always route as a cross, but value can be chosen
                // tricky part is that we have to route both variables at once to properly make a cross

                let routed_into_straght = topology.topology[column_idx][packet_idx].0; // this is a straight index
                let routed_into_cross = topology.topology[column_idx][packet_idx].1; // this is a cross index

                // may be we have already routed a pair, so quickly check
                if result_of_this_column[routed_into_straght].is_some() || result_of_this_column[routed_into_cross].is_some()
                {
                    assert!(result_of_this_column[routed_into_straght].is_some() && result_of_this_column[routed_into_cross].is_some());
                    continue;
                }

                // now find a pair of the variable at this index. It should be a variable for which
                // straight == this_cross and vice versa

                let mut another_idx = None;
                for idx in (packet_idx + 1)..topology.size {
                    let another_straght = topology.topology[column_idx][idx].0; // this is a straight index
                    let another_cross = topology.topology[column_idx][idx].1; // this is a cross index
                    if routed_into_straght == another_cross && routed_into_cross == another_straght {
                        another_idx = Some(idx);
                        break;
                    }
                }        
                assert!(another_idx.is_some());
                let another_idx = another_idx.unwrap();

                let previous_level_variable = permutation.get(packet_idx).ok_or(SynthesisError::Unsatisfiable)?.as_ref().ok_or(SynthesisError::Unsatisfiable)?;
                let previous_level_pair = permutation.get(another_idx).ok_or(SynthesisError::Unsatisfiable)?.as_ref().ok_or(SynthesisError::Unsatisfiable)?;

                let boolean_switch = switches_it.next().expect("must contain a switch value");

                // perform an actual switching 
                let (next_level_straight, next_level_cross) = AllocatedNum::conditionally_reverse(
                    cs,
                    &previous_level_variable,
                    &previous_level_pair,
                    &boolean_switch
                )?;
                switch_count += 1;

                result_of_this_column[routed_into_straght] = Some(next_level_straight);
                result_of_this_column[routed_into_cross] = Some(next_level_cross);
            }
        }
        // permutation that we keep a track on is now replaced by result of permutation by this column
        permutation = result_of_this_column;
        assert!(switches_it.next().is_none());
    }

    // we have routed the "original" into some "permutation", so we check that
    // "permutation" is equal to the claimed "permuted" value 
    for (claimed, routed) in permuted.iter().zip(permutation.into_iter()) {
        let routed = routed.expect("must be some");
        routed.enforce_equal(cs, &claimed)?;
    }

    println!("switch count: {}", switch_count);


    Ok(())
}



/// prove permutation by routing elements through the permutation network
/// Topology is calculated exclusively based on the size on the network, 
/// and permuted elements can be anything. Caller be responsible for validity
/// if elements are unique or not
pub fn prove_permutation_of_nums_using_switches_witness<E, CS>(
    cs: &mut CS,
    original: &[Num<E>],
    permuted: &[Num<E>],
    switches_layes: &Vec<Vec<Boolean>>,
) -> Result<(), SynthesisError>
    where CS: ConstraintSystem<E>,
          E: Engine
{
    // it's a code dumplication until we introduce traits and reworks
    assert_eq!(original.len(), permuted.len());
    // First make a topology

    let topology = AsWaksmanTopology::new(original.len());

    // now route elements through the network. Deterministically do the bookkeeping of the variables in a plain array

    let num_columns = AsWaksmanTopology::num_columns(topology.size);
    assert_eq!(num_columns, switches_layes.len());

    let mut permutation: Vec<Option<Num<E>>> = original.iter().map(|e| Some(e.clone())).collect();

    for column_idx in 0..num_columns {
        // this is just a bookkeeping variable and is deterministic
        let mut result_of_this_column: Vec<Option<Num<E>>> = vec![None; topology.size];
        let mut switches_it = (&switches_layes[column_idx]).iter();
        for packet_idx in 0..topology.size {
            if topology.topology[column_idx][packet_idx].0 == topology.topology[column_idx][packet_idx].1 {
                // straight switch, there is no need to allocate witness
                let routed_into_idx = topology.topology[column_idx][packet_idx].0;
                let previous_level_variable = permutation.get(packet_idx).expect("must be a variable for this packet idx");
                let previous_level_variable = previous_level_variable.ok_or(SynthesisError::Unsatisfiable)?;

                let new_variable_for_this_level = previous_level_variable;

                result_of_this_column[routed_into_idx] = Some(new_variable_for_this_level);
            } else {
                // in normal workflow we would select an index to which it's routed.
                // here we select a value instead, and always route as a cross, but value can be chosen
                // tricky part is that we have to route both variables at once to properly make a cross

                let routed_into_straght = topology.topology[column_idx][packet_idx].0; // this is a straight index
                let routed_into_cross = topology.topology[column_idx][packet_idx].1; // this is a cross index

                // may be we have already routed a pair, so quickly check
                if result_of_this_column[routed_into_straght].is_some() || result_of_this_column[routed_into_cross].is_some()
                {
                    assert!(result_of_this_column[routed_into_straght].is_some() && result_of_this_column[routed_into_cross].is_some());
                    continue;
                }

                // now find a pair of the variable at this index. It should be a variable for which
                // straight == this_cross and vice versa

                let mut another_idx = None;
                for idx in (packet_idx + 1)..topology.size {
                    let another_straght = topology.topology[column_idx][idx].0; // this is a straight index
                    let another_cross = topology.topology[column_idx][idx].1; // this is a cross index
                    if routed_into_straght == another_cross && routed_into_cross == another_straght {
                        another_idx = Some(idx);
                        break;
                    }
                }        
                assert!(another_idx.is_some());
                let another_idx = another_idx.unwrap();

                let previous_level_variable = permutation.get(packet_idx).ok_or(SynthesisError::Unsatisfiable)?.as_ref().ok_or(SynthesisError::Unsatisfiable)?;
                let previous_level_pair = permutation.get(another_idx).ok_or(SynthesisError::Unsatisfiable)?.as_ref().ok_or(SynthesisError::Unsatisfiable)?;

                let boolean_switch = switches_it.next().expect("must contain a switch value");

                // perform an actual switching 
                let (next_level_straight, next_level_cross) = Num::conditionally_reverse(
                    cs,
                    &previous_level_variable,
                    &previous_level_pair,
                    &boolean_switch
                )?;

                result_of_this_column[routed_into_straght] = Some(next_level_straight);
                result_of_this_column[routed_into_cross] = Some(next_level_cross);
            }
        }
        // permutation that we keep a track on is now replaced by result of permutation by this column
        permutation = result_of_this_column;
        assert!(switches_it.next().is_none());
    }

    // we have routed the "original" into some "permutation", so we check that
    // "permutation" is equal to the claimed "permuted" value 
    for (claimed, routed) in permuted.iter().zip(permutation.into_iter()) {
        let routed = routed.expect("must be some");
        routed.enforce_equal(cs, &claimed)?;
    }


    Ok(())
}

/// prove permutation by routing elements through the permutation network
/// Topology is calculated exclusively based on the size on the network, 
/// and permuted elements can be anything. Caller be responsible for validity
/// if elements are unique or not
pub fn prove_shuffle<E, CS>(
    cs: &mut CS,
    original: &[AllocatedNum<E>],
    permuted: &[AllocatedNum<E>],
    permuted_order: &IntegerPermutation,
) -> Result<(), SynthesisError>
    where CS: ConstraintSystem<E>,
          E: Engine
{
    assert_eq!(original.len(), permuted.len());
    assert_eq!(original.len(), permuted_order.size());

    let switches = order_into_switches_set(cs, permuted_order)?;
    prove_permutation_using_switches_witness(cs, original, permuted, &switches)

    // // First make a topology

    // let topology = AsWaksmanTopology::new(original.len());

    // // now calculate the witness for gate assignments

    // let router = AsWaksmanRoute::new(permuted_order);

    // // now route elements through the network. Deterministically do the bookkeeping of the variables in a plain array

    // let num_columns = AsWaksmanTopology::num_colunms(topology.size);

    // let mut permutation: Vec<Option<AllocatedNum<E>>> = original.iter().map(|e| Some(e.clone())).collect();

    // // let mut permutation: Vec<Option<AllocatedNum<E>>> = permuted.iter().map(|e| Some(e.clone())).collect();

    // for column_idx in 0..num_columns {
    //     // this is just a bookkeeping variable and is deterministic
    //     let mut result_of_this_column: Vec<Option<AllocatedNum<E>>> = vec![None; topology.size];
    //     for packet_idx in 0..topology.size {
    //         if topology.topology[column_idx][packet_idx].0 == topology.topology[column_idx][packet_idx].1 {
    //             // straight switch, there is no need to allocate witness
    //             let routed_into_idx = topology.topology[column_idx][packet_idx].0;
    //             let previous_level_variable = permutation.get(packet_idx).expect("must be a variable for this packet idx");
    //             // let previous_level_variable = previous_level_variable.ok_or(SynthesisError::Unsatisfiable)?.as_ref();
    //             let previous_level_variable = previous_level_variable.ok_or(SynthesisError::Unsatisfiable)?;
    //             // let new_variable_for_this_level = AllocatedNum::alloc(
    //             //     cs,
    //             //     || {
    //             //         let value = *previous_level_variable.get_value().get()?;

    //             //         Ok(value)
    //             //     }
    //             // )?;

    //             let new_variable_for_this_level = previous_level_variable;

    //             result_of_this_column[routed_into_idx] = Some(new_variable_for_this_level);
    //         } else {
    //             // validity check
    //             let a = router.switches[column_idx].get(&packet_idx);
    //             let b = if packet_idx > 0 {
    //                 router.switches[column_idx].get(&(packet_idx - 1))
    //             } else {
    //                 None
    //             };
    //             assert!(a.is_some() ^ b.is_some());

    //             // get value to make a witness
    //             let switch_value = if a.is_some() {
    //                 a.cloned()
    //             } else {
    //                 b.cloned()
    //             };

    //             // in normal workflow we would select an index to which it's routed.
    //             // here we select a value instead, and always route as a cross, but value can be chosen
    //             // tricky part is that we have to route both variables at once to properly make a cross

    //             let routed_into_straght = topology.topology[column_idx][packet_idx].0; // this is a straight index
    //             let routed_into_cross = topology.topology[column_idx][packet_idx].1; // this is a cross index

    //             // may be we have already routed a pair, so quickly check
    //             if result_of_this_column[routed_into_straght].is_some() || result_of_this_column[routed_into_cross].is_some()
    //             {
    //                 assert!(result_of_this_column[routed_into_straght].is_some() && result_of_this_column[routed_into_cross].is_some());
    //                 continue;
    //             }

    //             // now find a pair of the variable at this index. It should be a variable for which
    //             // straight == this_cross and vice versa

    //             let mut another_idx = None;
    //             for idx in (packet_idx + 1)..topology.size {
    //                 let another_straght = topology.topology[column_idx][idx].0; // this is a straight index
    //                 let another_cross = topology.topology[column_idx][idx].1; // this is a cross index
    //                 if routed_into_straght == another_cross && routed_into_cross == another_straght {
    //                     another_idx = Some(idx);
    //                     break;
    //                 }
    //             }        
    //             assert!(another_idx.is_some());
    //             let another_idx = another_idx.unwrap();

    //             let previous_level_variable = permutation.get(packet_idx).ok_or(SynthesisError::Unsatisfiable)?.as_ref().ok_or(SynthesisError::Unsatisfiable)?;
    //             let previous_level_pair = permutation.get(another_idx).ok_or(SynthesisError::Unsatisfiable)?.as_ref().ok_or(SynthesisError::Unsatisfiable)?;

    //             let boolean_switch = Boolean::from(AllocatedBit::alloc(
    //                 cs,
    //                 switch_value
    //             )?); 

    //             let cross_value = AllocatedNum::alloc(
    //                 cs,
    //             || {
    //                 let value = *previous_level_pair.get_value().get()?;

    //                 Ok(value)
    //             })?;

    //             let straight_value = AllocatedNum::alloc(
    //                 cs,
    //             || {
    //                 let value = *previous_level_variable.get_value().get()?;

    //                 Ok(value)
    //             })?;

    //             // perform an actual switching 
    //             let (next_level_straight, next_level_cross) = AllocatedNum::conditionally_reverse(
    //                 cs,
    //                 &straight_value,
    //                 &cross_value,
    //                 &boolean_switch
    //             )?;

    //             result_of_this_column[routed_into_straght] = Some(next_level_straight);
    //             result_of_this_column[routed_into_cross] = Some(next_level_cross);
    //         }
    //     }
    //     // permutation that we keep a track on is now replaced by result of permutation by this column
    //     permutation = result_of_this_column;
    // }

    // // enforce an actual permutation
    // for (i, variable) in permutation.into_iter().enumerate() {
    //     let variable = variable.ok_or(SynthesisError::Unsatisfiable)?;
    //     let permuted = &permuted[i];

    //     variable.enforce_equal(cs, &permuted)?;
    // }


    // Ok(())
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::bellman::plonk::better_better_cs::cs::*;
    use rand::{XorShiftRng, SeedableRng, Rand, Rng};
    use bellman::pairing::bn256::{Bn256, Fr};
    use bellman::pairing::ff::{BitIterator, Field, PrimeField};

    use super::{AsWaksmanRoute, AsWaksmanTopology, IntegerPermutation, prove_shuffle};

    #[test]
    fn test_permutation_positive() {
        let rng = &mut XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        for size in 3..10 {
            println!("Size = {}", size);
            for _ in 0..1 {
                let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

                let mut permutation = IntegerPermutation::new(size);
                permutation.make_permutation(rng);

                let original_vector = (0..size).map(|_| Fr::rand(rng)).collect::<Vec<_>>();
                let mut permuted_vector = original_vector.clone();
                for i in permutation.elements.iter() {
                    // element number `i` will go into the place `k`
                    let k = permutation.elements[*i];
                    permuted_vector[k] = original_vector[*i];
                }

                let mut original = vec![];
                let mut permuted = vec![];

                for(_i, (o, p)) in original_vector.into_iter().zip(permuted_vector.into_iter()).enumerate() {
                    let o = AllocatedNum::alloc(&mut cs, 
                        || Ok(o)
                    ).unwrap();
                    let p = AllocatedNum::alloc(&mut cs, 
                        || Ok(p)
                    ).unwrap();

                    original.push(o);
                    permuted.push(p);
                }

                prove_shuffle(&mut cs, 
                    &original, 
                    &permuted, 
                    &permutation
                ).unwrap();

                assert!(cs.is_satisfied());
            }
        }
    }

    #[test]
    #[should_panic]
    fn test_as_waksman_gadget_negative() {
        let rng = &mut XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        for size in 3..128 {
            println!("Size = {}", size);
            for _ in 0..10 {
                let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();
                
                let mut permutation = IntegerPermutation::new(size);
                permutation.make_permutation(rng);

                let original_vector = (0..size).map(|_| Fr::rand(rng)).collect::<Vec<_>>();
                let mut permuted_vector = original_vector.clone();
                for i in permutation.elements.iter() {
                    let k = permutation.elements[*i];
                    permuted_vector[k] = original_vector[*i];
                }

                let mut another_permutation = IntegerPermutation::new(size);
                another_permutation.make_permutation(rng);

                if permutation.elements == another_permutation.elements {
                    continue;
                }

                let mut original = vec![];
                let mut permuted = vec![];

                for(_i, (o, p)) in original_vector.into_iter().zip(permuted_vector.into_iter()).enumerate() {
                    let o = AllocatedNum::alloc(&mut cs, 
                        || Ok(o)
                    ).unwrap();
                    let p = AllocatedNum::alloc(&mut cs, 
                        || Ok(p)
                    ).unwrap();

                    original.push(o);
                    permuted.push(p);
                }

                prove_shuffle(&mut cs, 
                    &original, 
                    &permuted, 
                    &another_permutation
                ).unwrap();

                assert!(!cs.is_satisfied());
            }
        }
    }
}