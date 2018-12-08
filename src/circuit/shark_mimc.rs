// This is an attempt to write an implementation of Dmitry Khovratovich

use pairing::{Engine};
use bellman::{ConstraintSystem, SynthesisError};
use rand::Rng;
use ff::{Field, PrimeField, PrimeFieldRepr, BitIterator};

use super::*;

const block_size: usize = 256;
const gate_size: usize = 32;
const branch_size: usize = 32;
const num_branches: usize = 4;
const middle_rounds: usize = 38;
const total_rounds: usize = 3 + middle_rounds + 3;
const num_round_keys: usize = (middle_rounds + 7) * num_branches;
const num_round_constants: usize = (middle_rounds + 6) * num_branches;

pub struct SharkMimc<E: Engine> {
    round_constants : [E::Fr; num_round_constants],
    round_keys:  [E::Fr; num_round_keys],
    matrix_1: [[E::Fr; num_branches]; num_branches],
    matrix_2: [[E::Fr; num_branches]; num_branches],
    // linear_vals : Vec<num::AllocatedNum<E>>,
    // round_squares : Vec<num::AllocatedNum<E>>,
    // sbox_outs: Vec<num::AllocatedNum<E>>,
}

impl<E:Engine> SharkMimc<E> {
    fn new<R, CS>(
        mut cs: CS,
        rng: &mut R
    ) -> Self
        where CS: ConstraintSystem<E>, R: Rng
    {
        // generate round keys
        let mut round_keys = [E::Fr::zero(); num_round_keys];
        for i in 0..num_round_keys {
            let random_element: E::Fr = rng.gen();
            round_keys[i] = random_element;
        }

        // prepare round constants
        let mut round_constants = [E::Fr::zero(); num_round_constants];
        for i in 0..num_round_constants {
            let random_element: E::Fr = rng.gen();
            round_keys[i] = random_element;
        }

        let mut matrix_1 = [[E::Fr::one(); num_branches]; num_branches];

        {
            let x = [E::Fr::from_str(&"1").unwrap(),
                    E::Fr::from_str(&"2").unwrap(),
                    E::Fr::from_str(&"3").unwrap(),
                    E::Fr::from_str(&"4").unwrap()
                ];

            let y = [E::Fr::from_str(&"5").unwrap(),
                    E::Fr::from_str(&"6").unwrap(),
                    E::Fr::from_str(&"7").unwrap(),
                    E::Fr::from_str(&"8").unwrap()
                ];



            let one = E::Fr::one();

            // Char - 2
            let mut power = E::Fr::zero();
            power.sub_assign(&one);
            power.sub_assign(&one);
            
            let mut element = E::Fr::zero();
            let mut base_temp = E::Fr::zero();
            let mut exp_temp = E::Fr::zero;
            for i in 0..num_branches {
                for j in 0..num_branches {
                    let mut element = x[i];
                    element.add_assign(&y[j]);
                    element.pow(power.into_repr());

                    // let mut bit_iterator: Vec<bool> = BitIterator::new(element.into_repr()).collect();
                    // bit_iterator.reverse();
                    // let mut res = E::Fr::one();
                    // for bit in bit_iterator.into_iter() {
                    //     if bit {
                    //         res.mul_assign(&element);
                    //     }
                    //     res.square();
                    // }

                    matrix_1[i][j] = element
                }
            }
        }

        let mut matrix_2 = [[E::Fr::one(); num_branches]; num_branches];

        {
            let x = [E::Fr::from_str(&"9").unwrap(),
                    E::Fr::from_str(&"10").unwrap(),
                    E::Fr::from_str(&"11").unwrap(),
                    E::Fr::from_str(&"12").unwrap()
                ];

            let y = [E::Fr::from_str(&"13").unwrap(),
                    E::Fr::from_str(&"14").unwrap(),
                    E::Fr::from_str(&"15").unwrap(),
                    E::Fr::from_str(&"16").unwrap()
                ];

            let one = E::Fr::one();

            // Char - 2
            let mut power = E::Fr::zero();
            power.sub_assign(&one);
            power.sub_assign(&one);
            
            let mut element = E::Fr::zero();
            let mut base_temp = E::Fr::zero();
            let mut exp_temp = E::Fr::zero;
            for i in 0..num_branches {
                for j in 0..num_branches {
                    let mut element = x[i];
                    element.add_assign(&y[j]);
                    element.pow(power.into_repr());

                    // let mut bit_iterator: Vec<bool> = BitIterator::new(element.into_repr()).collect();
                    // bit_iterator.reverse();
                    // let mut res = E::Fr::one();
                    // for bit in bit_iterator.into_iter() {
                    //     if bit {
                    //         res.mul_assign(&element);
                    //     }
                    //     res.square();
                    // }

                    matrix_2[i][j] = element
                }
            }
        }

        Self {
            round_constants : round_constants,
            round_keys:  round_keys,
            matrix_1: matrix_1,
            matrix_2: matrix_2,
            // linear_vals : Vec<num::AllocatedNum<E>>,
            // round_squares : Vec<num::AllocatedNum<E>>,
            // sbox_outs: Vec<num::AllocatedNum<E>>,
        }
    }

    fn hash<CS>(
        &self,
        mut cs: CS,
        inputs: &[num::AllocatedNum<E>]
    ) -> Result<num::AllocatedNum<E>, SynthesisError> 
        where CS: ConstraintSystem<E>
    {
        assert_eq!(inputs.len(), num_branches);
        let cs = cs.namespace(|| "Sharkmimc inverse gadget");
        let linear_vals = inputs.clone();
        let mut round_squares_constraint_idx = 0;
        let mut round_keys_offset = 0;

        let mut s_box_outs = vec![];

        for round_number in 1..4 {
            let offset = round_number * num_branches;
            let prev_offset = offset - num_branches;

            for i in 0..num_branches {
                let lookup_index = prev_offset+i;
                let input = inputs[lookup_index];
                let s_box_out = num::AllocatedNum::alloc(
                    cs.namespace(|| format!("Allocate sbox output for round number {}, branch {}", round_number, i)), 
                    || {
                        let mut t = input.get_value().get()?;
                        t.add_assign(&self.round_keys[round_keys_offset]);

                        match t.inverse() {
                                Some(t) => {
                                

                                    Ok(t)
                                },
                            None => {
                                Err(SynthesisError::DivisionByZero)
                            }
                        }
                    }   
                )?;

                cs.enforce(
                    || format!("s box for round {} computation, branch {}", round_number, i),
                    |lc| lc + input.get_variable() + (self.round_keys[round_keys_offset], CS::one()),
                    |lc| lc + s_box_out.get_variable(),
                    |lc| lc + CS::one()
                );

                s_box_outs.push(s_box_out);

                round_keys_offset += 1;
            }
        }

        for round_number in 4..(4+middle_rounds) {
            let offset = round_number * num_branches;

            let lookup_index = offset - num_branches;
            let input = inputs[lookup_index];
            let s_box_out = num::AllocatedNum::alloc(
                cs.namespace(|| format!("Allocate sbox output for round number {}", round_number)), 
                || {
                    let mut t = input.get_value().get()?;
                    t.add_assign(&self.round_keys[round_keys_offset]);

                    match t.inverse() {
                            Some(t) => {
                            

                                Ok(t)
                            },
                        None => {
                            Err(SynthesisError::DivisionByZero)
                        }
                    }
                }   
            )?;

            cs.enforce(
                || format!("s box for round {} computation", round_number),
                |lc| lc + input.get_variable() + (self.round_keys[round_keys_offset], CS::one()),
                |lc| lc + s_box_out.get_variable(),
                |lc| lc + CS::one()
            );
            s_box_outs.push(s_box_out);
            round_keys_offset += num_branches;
        }

        for round_number in (4+middle_rounds)..(4+2+middle_rounds) {
            let offset = round_number * num_branches;
            let prev_offset = offset - num_branches;

            for i in 0..num_branches {
                let lookup_index = prev_offset+i;
                let input = inputs[lookup_index];
                let s_box_out = num::AllocatedNum::alloc(
                    cs.namespace(|| format!("Allocate sbox output for round number {}, branch {}", round_number, i)), 
                    || {
                        let mut t = input.get_value().get()?;
                        t.add_assign(&self.round_keys[round_keys_offset]);

                        match t.inverse() {
                                Some(t) => {
                                

                                    Ok(t)
                                },
                            None => {
                                Err(SynthesisError::DivisionByZero)
                            }
                        }
                    }   
                )?;

                cs.enforce(
                    || format!("s box for round {} computation, branch {}", round_number, i),
                    |lc| lc + input.get_variable() + (self.round_keys[round_keys_offset], CS::one()),
                    |lc| lc + s_box_out.get_variable(),
                    |lc| lc + CS::one()
                );
                s_box_outs.push(s_box_out);
                round_keys_offset += 1;
            }
        }

        let offset = (4+2+middle_rounds) * num_branches;
        let prev_offset = offset - num_branches;

        for i in 0..num_branches {
                let lookup_index = prev_offset+i;
                let input = inputs[lookup_index];
                let s_box_out = num::AllocatedNum::alloc(
                    cs.namespace(|| format!("Allocate sbox output for round number {}, branch {}", (4+2+middle_rounds), i)), 
                    || {
                        let mut t = input.get_value().get()?;
                        t.add_assign(&self.round_keys[round_keys_offset]);

                        match t.inverse() {
                                Some(t) => {
                                

                                    Ok(t)
                                },
                            None => {
                                Err(SynthesisError::DivisionByZero)
                            }
                        }
                    }   
                )?;

                cs.enforce(
                    || format!("s box for round {} computation, branch {}", round_number, i),
                    |lc| lc + input.get_variable() + (self.round_keys[round_keys_offset], CS::one()),
                    |lc| lc + s_box_out.get_variable(),
                    |lc| lc + CS::one()
                );
                s_box_outs.push(s_box_out);
                round_keys_offset += 2;
            }

        round_keys_offset += num_branches;



        for(; round_no <= 3+middle_rounds; round_no++) {

            uint32_t offset = round_no * this->num_branches;

            this->generate_sbox_constraint(offset-this->num_branches, round_keys_offset, sbox_outs_idx);

            round_keys_offset += this->num_branches;
            sbox_outs_idx++;
        }

        for(; round_no <= 3+middle_rounds+2; round_no++) {

            uint32_t offset = round_no * this->num_branches;
            uint32_t prev_offset = offset - this->num_branches;

            // 4 S-boxes, 8 constraints
            for(uint32_t i = 0; i < this->num_branches; i++) {

                this->generate_sbox_constraint(prev_offset+i, round_keys_offset, sbox_outs_idx);
                round_keys_offset++;
                sbox_outs_idx++;
            }
        }

        uint32_t offset = round_no * this->num_branches;
        uint32_t prev_offset = offset - this->num_branches;

        for(uint32_t i = 0; i < this->num_branches; i++) {

            this->generate_sbox_constraint(prev_offset+i, round_keys_offset, sbox_outs_idx);

            sbox_outs_idx++;
            round_keys_offset += 2;
        }
    }
}