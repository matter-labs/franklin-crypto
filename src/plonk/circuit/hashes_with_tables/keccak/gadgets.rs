use crate::bellman::plonk::better_better_cs::cs::*;
use crate::bellman::plonk::better_better_cs::lookup_tables::*;
use crate::bellman::plonk::better_better_cs::utils;
use crate::bellman::pairing::ff::*;
use crate::bellman::pairing::ff::{PrimeField, PrimeFieldRepr};
use crate::bellman::SynthesisError;
use crate::bellman::Engine;

use crate::plonk::circuit::allocated_num::{
    AllocatedNum,
    Num,
};
use crate::plonk::circuit::byte::{
    Byte,
};
use crate::plonk::circuit::assignment::{
    Assignment
};

use super::tables::*;
use super::utils::*;
use super::super::utils::*;
use super::super::tables::*;

use std::sync::Arc;
use std::collections::HashMap;
use std::ops::{Index, IndexMut};

use crate::num_bigint::BigUint;
use crate::num_traits::cast::ToPrimitive;
use crate::num_traits::{Zero, One};
use itertools::Itertools;

type Result<T> = std::result::Result<T, SynthesisError>;


// keccak full_width = 1600 bits = 200 bytes
// rate = 136 byte = 1088 bits = 17 (64-bit) words
pub const KECCAK_RATE_WORDS_SIZE : usize = 17;
pub const DEFAULT_KECCAK_DIGEST_WORDS_SIZE : usize = 4;
pub const DEFAULT_BINARY_NUM_OF_CHUNKS : usize = 16; // 2^16 is fine
pub const DEFAULT_FIRST_BASE_NUM_OF_CHUNKS : usize = 4; 
pub const DEFAULT_OF_FIRST_BASE_NUM_OF_CHUNKS : usize = 2;
pub const DEFAULT_SECOND_BASE_NUM_OF_CHUNKS : usize = 5;
pub const BINARY_BASE: u64 = 2;
// keccak state has 5 x 5 x 64 - bits, 
// each row of 64 bits is a lane.
pub const KECCAK_STATE_WIDTH : usize = 5;
pub const KECCAK_LANE_WIDTH : usize = 64;
pub const KECCAK_NUM_ROUNDS : usize = 24;
#[derive(Clone)]
pub struct KeccakState<E: Engine>([[Num<E>; KECCAK_STATE_WIDTH]; KECCAK_STATE_WIDTH]);

impl<E: Engine> Default for KeccakState<E> {
    fn default() -> Self {
        KeccakState(<[[Num<E>; KECCAK_STATE_WIDTH]; KECCAK_STATE_WIDTH]>::default())
    }
}

impl<E: Engine> Index<(usize, usize)> for KeccakState<E> {
    type Output = Num<E>;

    fn index(&self, index: (usize, usize)) -> &Self::Output {
        assert!(index.0 < KECCAK_STATE_WIDTH);
        assert!(index.1 < KECCAK_STATE_WIDTH);

        &self.0[index.0][index.1]
    }
}

impl<E: Engine> IndexMut<(usize, usize)> for KeccakState<E> {
    fn index_mut(&mut self, index: (usize, usize)) -> &mut Self::Output {
        assert!(index.0 < KECCAK_STATE_WIDTH);
        assert!(index.1 < KECCAK_STATE_WIDTH);

        &mut self.0[index.0][index.1]
    }
}


#[derive(Copy, Clone)]
enum KeccakBase {
    Binary,
    KeccakFirstSparseBase,
    KeccakSecondSparseBase,
}


pub struct KeccakGadget<E: Engine> {
    // table used to convert binary register into first_sparse_base and second sparse base
    from_binary_converter_table: Arc<LookupTableApplication<E>>,
    // tables used to convert elements from first_sparse base into second - standard and overflow cognizant
    first_to_second_base_converter_table: Arc<LookupTableApplication<E>>,
    of_first_to_second_base_converter_table: Arc<LookupTableApplication<E>>,
    // table used to convert elements from second base: either to binary form or back to first sparse base
    from_second_base_converter_table: Arc<LookupTableApplication<E>>,
    
    binary_base_num_of_chunks: usize,
    first_base_num_of_chunks: usize,
    range_table_lower_bound: usize,
    range_table_upper_bound : usize,
    second_base_num_of_chunks: usize,

    offsets : [[usize; KECCAK_STATE_WIDTH]; KECCAK_STATE_WIDTH],
    round_cnsts_in_first_base : [E::Fr; KECCAK_NUM_ROUNDS],
    round_cnsts_in_second_base : [E::Fr; KECCAK_NUM_ROUNDS],
    digest_size: usize,
}

impl<E: Engine> KeccakGadget<E> {
    pub fn new<CS: ConstraintSystem<E>>(
        cs: &mut CS, 
        binary_base_num_of_chunks: Option<usize>,
        first_base_num_of_chunks: Option<usize>,
        second_base_num_of_chunks: Option<usize>,
        digest_size : Option<usize>,
    ) -> Result<Self> 
    {
        let binary_base_num_of_chunks = binary_base_num_of_chunks.unwrap_or(DEFAULT_BINARY_NUM_OF_CHUNKS);
        let first_base_num_of_chunks = first_base_num_of_chunks.unwrap_or(DEFAULT_FIRST_BASE_NUM_OF_CHUNKS);
        let of_first_base_num_of_chunks = DEFAULT_OF_FIRST_BASE_NUM_OF_CHUNKS;
        let second_base_num_of_chunks = second_base_num_of_chunks.unwrap_or(DEFAULT_SECOND_BASE_NUM_OF_CHUNKS);
        let digest_size = digest_size.unwrap_or(DEFAULT_KECCAK_DIGEST_WORDS_SIZE);
        
        let columns3 = vec![
            PolyIdentifier::VariablesPolynomial(0), 
            PolyIdentifier::VariablesPolynomial(1), 
            PolyIdentifier::VariablesPolynomial(2)
        ];

        let name1: &'static str = "from_binary_converter_table";
        let from_binary_converter_table = LookupTableApplication::new(
            name1,
            MultiBaseNormalizationTable::new(
                binary_base_num_of_chunks, BINARY_BASE, KECCAK_FIRST_SPARSE_BASE, KECCAK_SECOND_SPARSE_BASE, |x| {x}, |x| {x}, name1,
            ),
            columns3.clone(),
            true
        );

        let name2 : &'static str = "first_to_second_base_converter_table";
        let f = |x| { keccak_u64_first_conveter(x)};
        let first_to_second_base_converter_table = LookupTableApplication::new(
            name2,
            ExtendedBaseConverterTable::new(first_base_num_of_chunks, KECCAK_FIRST_SPARSE_BASE, KECCAK_SECOND_SPARSE_BASE, f, name2),
            columns3.clone(),
            true
        );

        println!("third table");

        let name3 : &'static str = "of_first_to_second_base_converter_table";
        let f = |x| { keccak_u64_first_conveter(x)};
        let of_first_to_second_base_converter_table = LookupTableApplication::new(
            name3,
            OverflowFriendlyBaseConverterTable::new(
                first_base_num_of_chunks, KECCAK_FIRST_SPARSE_BASE, KECCAK_SECOND_SPARSE_BASE, KECCAK_LANE_WIDTH as u64, f, name3
            ),
            columns3.clone(),
            true
        );

        println!("fourth table");

        let name4 : &'static str = "ternary_range_table";
        let f = |x| { keccak_u64_second_converter(x)};
        let ternary_range_table = LookupTableApplication::new(
            name4,
            TinyRangeTable::new(range_table_lower_bound, range_table_upper_bound, name4),
            columns3.clone(),
            true
        );
        
        let name5 : &'static str = "from_second_base_converter_table";
        let from_second_base_converter_table = LookupTableApplication::new(
            name5,
            MultiBaseConverterTable::new(
                second_base_num_of_chunks, KECCAK_SECOND_SPARSE_BASE, KECCAK_FIRST_SPARSE_BASE, BINARY_BASE, f, name5
            ),
            columns3.clone(),
            true
        );

        let from_binary_converter_table = cs.add_table(from_binary_converter_table)?;
        let first_to_second_base_converter_table = cs.add_table(first_to_second_base_converter_table)?;
        let of_first_to_second_base_converter_table = cs.add_table(of_first_to_second_base_converter_table)?;
        let ternary_range_table = cs.add_table(ternary_range_table)?;
        let from_second_base_converter_table = cs.add_table(from_second_base_converter_table)?;

        let offsets = [
            [64, 28, 61, 46, 23], 
            [63, 20, 54, 19, 62], 
            [2, 58, 21, 49, 3], 
            [36, 9, 39, 43, 8], 
            [37, 44, 25, 56, 50]
        ];

        let f = |mut input: u64, step: u64| -> E::Fr {
            let mut acc = BigUint::default(); 
            let mut base = BigUint::one();
 
            while input > 0 {
                let bit = input & 1;
                input >>= 1;
                acc += bit * base.clone();
                base *= step;
            }

            let res = E::Fr::from_str(&acc.to_str_radix(10)).expect("should parse");
            res
        };

        let t = KECCAK_FIRST_SPARSE_BASE;
        let round_cnsts_in_first_base = [
            f(0x0000000000000001, t), f(0x0000000000008082, t), f(0x800000000000808A, t), f(0x8000000080008000, t),
            f(0x000000000000808B, t), f(0x0000000080000001, t), f(0x8000000080008081, t), f(0x8000000000008009, t),
            f(0x000000000000008A, t), f(0x0000000000000088, t), f(0x0000000080008009, t), f(0x000000008000000A, t),
            f(0x000000008000808B, t), f(0x800000000000008B, t), f(0x8000000000008089, t), f(0x8000000000008003, t),
            f(0x8000000000008002, t), f(0x8000000000000080, t), f(0x000000000000800A, t), f(0x800000008000000A, t),
            f(0x8000000080008081, t), f(0x8000000000008080, t), f(0x0000000080000001, t), f(0x8000000080008008, t),
        ];

        let r = KECCAK_SECOND_SPARSE_BASE;
        let round_cnsts_in_second_base = [
            f(0x0000000000000001, r), f(0x0000000000008082, r), f(0x800000000000808A, r), f(0x8000000080008000, r),
            f(0x000000000000808B, r), f(0x0000000080000001, r), f(0x8000000080008081, r), f(0x8000000000008009, r),
            f(0x000000000000008A, r), f(0x0000000000000088, r), f(0x0000000080008009, r), f(0x000000008000000A, r),
            f(0x000000008000808B, r), f(0x800000000000008B, r), f(0x8000000000008089, r), f(0x8000000000008003, r),
            f(0x8000000000008002, r), f(0x8000000000000080, r), f(0x000000000000800A, r), f(0x800000008000000A, r),
            f(0x8000000080008081, r), f(0x8000000000008080, r), f(0x0000000080000001, r), f(0x8000000080008008, r),
        ];

        let allocated_one = AllocatedNum::alloc_cnst(cs, E::Fr::one())?;

        println!("here");

        Ok(KeccakGadget {
            from_binary_converter_table,
            first_to_second_base_converter_table,
            of_first_to_second_base_converter_table,
            ternary_range_table,
            from_second_base_converter_table,
    
            binary_base_num_of_chunks,
            first_base_num_of_chunks,
            of_first_base_num_of_chunks,
            range_table_lower_bound,
            range_table_upper_bound,
            second_base_num_of_chunks,

            offsets,
            round_cnsts_in_first_base,
            round_cnsts_in_second_base,
            digest_size,

            allocated_one,
        })
    }

    // for row of the form [x, f(x), g(x), acc] do:
    // table query x => f(x), g(x)
    // running sum for input: acc_next = acc - coef * x
    // if is_final is set, simply check: acc = coef * x
    // returns (f(x), g(x), acc_next)
    fn query_table_accumulate<CS: ConstraintSystem<E>>(
        &self, 
        cs: &mut CS, 
        table: &Arc<LookupTableApplication<E>>, 
        key: &AllocatedNum<E>,
        prev_acc: &AllocatedNum<E>,
        coef: &E::Fr,
        is_final: bool,
    ) -> Result<(AllocatedNum<E>, AllocatedNum<E>, AllocatedNum<E>)> 
    {
        let (f_key, g_key) = match key.get_value() {
            None => {
                (
                    AllocatedNum::alloc(cs, || Err(SynthesisError::AssignmentMissing))?, 
                    AllocatedNum::alloc(cs, || Err(SynthesisError::AssignmentMissing))?,
                )
            },
            Some(val) => {
                let vals = table.query(&[val])?;
                (AllocatedNum::alloc(cs, || Ok(vals[0]))?, AllocatedNum::alloc(cs, || Ok(vals[1]))?)
            },     
        };

        let new_acc = if !is_final {
            AllocatedNum::alloc(cs, || {
                let mut res = prev_acc.get_value().grab()?;
                let mut tmp = key.get_value().grab()?;
                tmp.mul_assign(coef);
                res.sub_assign(&(f_key.get_value().grab())?);
                Ok(tmp)
            })?
        }
        else {
            AllocatedNum::zero(cs)
        };

        let mut minus_one = E::Fr::one();
        minus_one.negate();
        let dummy = AllocatedNum::zero(cs).get_variable();

        let range_of_linear_terms = CS::MainGate::range_of_linear_terms();
        let range_of_next_step_linear_terms = CS::MainGate::range_of_next_step_linear_terms();
        let idx_of_last_linear_term = range_of_next_step_linear_terms.last().expect("must have an index");

        // new_acc = prev_acc - base * key
        // or: base * key + new_acc - prev_acc = 0;
        let vars = [key.get_variable(), f_key.get_variable(), g_key.get_variable(), new_acc.get_variable()];
        let coeffs = [coef.clone(), E::Fr::zero(), E::Fr::zero(), minus_one];

        cs.begin_gates_batch_for_step()?;

        cs.apply_single_lookup_gate(&vars[..table.width()], table.clone())?;
    
        let mut gate_term = MainGateTerm::new();
        let (_, mut gate_coefs) = CS::MainGate::format_term(gate_term, dummy)?;

        for (idx, coef) in range_of_linear_terms.zip(coeffs.into_iter()) {
            gate_coefs[idx] = *coef;
        }

        if !is_final {
            gate_coefs[idx_of_last_linear_term] = E::Fr::one();
        }

        let mg = CS::MainGate::default();
        cs.new_gate_in_batch(
            &mg,
            &gate_coefs,
            &vars,
            &[]
        )?;

        cs.end_gates_batch_for_step()?;

        Ok((f_key, g_key, new_acc))
    }

    fn rotate_and_convert(&self, fr: &E::Fr, rot: usize) -> E::Fr
    {
        let mut input = BigUint::default();
        let fr_repr = fr.into_repr();
        for n in fr_repr.as_ref().iter().rev() {
            input <<= 64;
            input += *n;
        }

        let mut acc = BigUint::default(); 
        let init_base = biguint_pow(KECCAK_FIRST_SPARSE_BASE as usize, KECCAK_LANE_WIDTH - rot);
        let mut base = init_base.clone();
        let mut iter_n = 0;
        let mut special_chunk = 0;

        for (is_first, is_last, i) in (0..(KECCAK_LANE_WIDTH + 1)).identify_first_last() {
            let remainder = (input.clone() % BigUint::from(KECCAK_FIRST_SPARSE_BASE)).to_u64().unwrap();
            if is_first || is_last {
                special_chunk += remainder;
            }
            else {
                let output_chunk = keccak_u64_second_converter(remainder);
                acc += base.clone() * output_chunk;
            }
            
            input /= KECCAK_FIRST_SPARSE_BASE;
            base *= KECCAK_SECOND_SPARSE_BASE;
            iter_n += 1;

            if iter_n == rot {
                base = BigUint::one();
            } 
        }

        acc += keccak_u64_second_converter(special_chunk) * init_base;
        let res = E::Fr::from_str(&acc.to_str_radix(10)).expect("should parse");
        res
    }

    fn theta<CS: ConstraintSystem<E>>(&self, cs: &mut CS, state: KeccakState<E>) -> Result<KeccakState<E>> {
        let mut C = Vec::with_capacity(KECCAK_LANE_WIDTH);
        // calculate C[x] for each column:
        for i in 0..KECCAK_LANE_WIDTH {
            C.push(Num::sum(cs, &state.0[i])?);
        }

        // recalculate state
        let coeffs = [E::Fr::one(), E::Fr::one(), u64_to_ff(KECCAK_FIRST_SPARSE_BASE)];
        let mut new_state = KeccakState::default();
        for (i, j) in (0..KECCAK_LANE_WIDTH).cartesian_product(0..KECCAK_LANE_WIDTH) {
            let inputs = [state[(i, j)].clone(), C[(i-1) % KECCAK_LANE_WIDTH].clone(), C[(i+1) % KECCAK_LANE_WIDTH].clone()];
            new_state[(i, j)] = Num::lc(cs, &coeffs, &inputs[..])?;
        }
        Ok(new_state)   
    }

    fn pi<CS: ConstraintSystem<E>>(&self, _cs: &mut CS, state: KeccakState<E>) -> Result<KeccakState<E>> {
        let mut new_state = KeccakState::default();
        for (i, j) in (0..KECCAK_LANE_WIDTH).cartesian_product(0..KECCAK_LANE_WIDTH) {
            new_state[(i, j)] = state[((i + 3*j) % KECCAK_LANE_WIDTH, i)].clone();
        }
        Ok(new_state)
    }

    fn xi_i<CS: ConstraintSystem<E>>(
        &self, cs: &mut CS, state: KeccakState<E>, round: usize, 
        elems_to_squeeze: usize, elems_to_mix: Option<&[Num<E>]>, is_final: bool,
    ) -> Result<(KeccakState<E>, Vec<Num<E>>)> 
    {
        // we cant's squeeze and mix simultantously:
        if elems_to_squeeze > 0 && elems_to_mix.is_some() {
            unreachable!();
        }
        // check, that elems to mix contains the righit number of elements
        if let Some(input_to_mix) = elems_to_mix {
            assert_eq!(input_to_mix.len(), KECCAK_RATE_WORDS_SIZE);
        }
        
        let mut new_state = KeccakState::default();
        let mut iter_count = 0;
        let coeffs = [u64_to_ff(2), E::Fr::one(), u64_to_ff(3), E::Fr::one()];
        let mut squeezed = Vec::with_capacity(elems_to_squeeze);
        
        let num_of_chunks = self.second_base_num_of_chunks;
        let num_slices = round_up(KECCAK_LANE_WIDTH, num_of_chunks);
                    
        let input_slice_modulus = pow(KECCAK_SECOND_SPARSE_BASE as usize, num_of_chunks);
        let output1_slice_modulus = pow(KECCAK_FIRST_SPARSE_BASE as usize, num_of_chunks);
        let output2_slice_modulus = pow(BINARY_BASE as usize, num_of_chunks);

        let input_slice_modulus_fr = u64_exp_to_ff(KECCAK_SECOND_SPARSE_BASE, num_of_chunks as u64);
        let output1_slice_modulus_fr = u64_exp_to_ff(KECCAK_FIRST_SPARSE_BASE, num_of_chunks as u64);
        let output2_slice_modulus_fr = u64_exp_to_ff(KECCAK_SECOND_SPARSE_BASE, num_of_chunks as u64);

        let dummy = AllocatedNum::zero(cs);
        let next_row_coef_idx = CS::MainGate::range_of_next_step_linear_terms().last().unwrap();
        let mut minus_one = E::Fr::one();
        minus_one.negate();

        for (j, i) in (0..KECCAK_LANE_WIDTH).cartesian_product(0..KECCAK_LANE_WIDTH) {
            // A′[x, y,z] = A[x, y,z] ⊕ ((A[(x+1) mod 5, y, z] ⊕ 1) ⋅ A[(x+2) mod 5, y, z]).
            // the corresponding algebraic transform is y = 2a + b + 3c +2d
            // if we are squeezing:
            // d is always constant and nonzero only for lane[0][0]
            // if we are mixing:
            // d is the next mixed input for the first KECCAK_RATE_WORDS_SIZE lanes (and zero for the rest)
            // there are 4-summands so always push result in d-next if not constant
            let d = match elems_to_mix {
                None => if i == 0  && j == 0 {Num::Constant(self.round_cnsts_in_second_base[round].clone())} else { Num::default() },
                Some(input_to_mix) => {
                    let idx = j * KECCAK_LANE_WIDTH + i; 
                    if idx < KECCAK_RATE_WORDS_SIZE { input_to_mix[idx].clone() } else { Num::default() }
                },
            }; 
            let b = state[((i+1 % KECCAK_STATE_WIDTH), j)].clone();
            let c = state[((i+2 % KECCAK_STATE_WIDTH), j)].clone();
            let inputs = [state[(i, j)].clone(), b, c, d];

            let lc = if inputs.iter().all(| x | x.is_constant()) {
                let value = inputs.iter().zip(coeffs.iter()).fold(E::Fr::zero(), |acc, (x, coef)| {
                    let mut temp = x.get_value().unwrap();
                    temp.mul_assign(&coef);
                    temp.add_assign(&acc);
                    temp
                });
                
                Num::Constant(value)
            }
            else {
                let lc = AllocatedNum::alloc(cs, || {
                    let mut acc = inputs[0].get_value().grab()?;
                    acc.mul_assign(&coeffs[0]);

                    let mut tmp = inputs[1].get_value().grab()?;
                    tmp.mul_assign(&coeffs[1]);
                    acc.add_assign(&tmp);

                    tmp = inputs[2].get_value().grab()?;
                    tmp.mul_assign(&coeffs[2]);
                    acc.add_assign(&tmp);

                    tmp = inputs[3].get_value().grab()?;
                    tmp.mul_assign(&coeffs[3]);
                    acc.add_assign(&tmp);

                    Ok(acc)
                })?;

                let mut gate = MainGateTerm::new();
                let mut cnst = E::Fr::zero();
     
                for (x, coef) in inputs.iter().zip(coeffs.iter()) {
                    match x {
                        Num::Constant(x) => {
                            let mut temp = x.clone();
                            temp.mul_assign(&coef);
                            cnst.add_assign(&temp);
                        },
                        Num::Variable(x) => {
                            let mut term = ArithmeticTerm::from_variable(x.get_variable());
                            term.scale(coef);
                            gate.add_assign(term);
                        }
                    }
                };

                let const_term = ArithmeticTerm::constant(cnst);
                gate.add_assign(const_term);

                let (mut gate_vars, mut gate_coefs) = CS::MainGate::format_term(gate, dummy.get_variable())?;
                gate_coefs[next_row_coef_idx] = minus_one.clone();
        
                let mg = CS::MainGate::default();
                cs.new_single_gate_for_trace_step(
                    &mg,
                    &gate_coefs,
                    &gate_vars,
                    &[]
                )?;

                Num::Variable(lc)
            };
                      
            match lc {
                Num::Constant(fr) => {
                    new_state[(i, j)] = Num::Constant(keccak_ff_second_converter(fr, KECCAK_FIRST_SPARSE_BASE));
                    if iter_count < elems_to_squeeze {
                        squeezed.push(Num::Constant(keccak_ff_second_converter(fr, BINARY_BASE)));
                    }
                }
                Num::Variable(var) => {
                    let mut input_slices : Vec<AllocatedNum<E>> = Vec::with_capacity(num_slices);
                    let mut output1_slices : Vec<AllocatedNum<E>> = Vec::with_capacity(num_slices);
                    let mut output2_slices : Vec<AllocatedNum<E>> = Vec::with_capacity(num_slices);

                    match var.get_value() {
                        None => {
                            for _ in 0..num_slices {
                                let tmp = AllocatedNum::alloc(cs, || Err(SynthesisError::AssignmentMissing))?;
                                input_slices.push(tmp);
                            }
                        },
                        Some(f) => {
                            // here we have to operate on row biguint number
                            let mut big_f = BigUint::default();
                            let f_repr = f.into_repr();
                            for n in f_repr.as_ref().iter().rev() {
                                big_f <<= 64;
                                big_f += *n;
                            } 

                            for _ in 0..num_slices {
                                let remainder = (big_f.clone() % BigUint::from(input_slice_modulus)).to_u64().unwrap();
                                let new_val = u64_to_ff(remainder);
                                big_f /= input_slice_modulus;
                                let tmp = AllocatedNum::alloc(cs, || Ok(new_val))?;
                                input_slices.push(tmp);
                            }

                            assert!(big_f.is_zero());
                        }
                    }

                    let mut coef = E::Fr::one();
                    let mut acc = var.clone();
                    for (_is_first, is_last, input_chunk) in input_slices.iter().identify_first_last() {
                        let (output1, output2, new_acc) = self.query_table_accumulate(
                            cs, &self.from_second_base_converter_table, input_chunk, &acc, &coef, is_last
                        )?; 

                        coef.mul_assign(&input_slice_modulus_fr);
                        acc = new_acc;

                        output1_slices.push(output1);
                        output1_slices.push(output2);
                    }

                    if !is_final {
                        let mut output1_total = AllocatedNum::alloc(cs, || {
                            let fr = var.get_value().grab()?;
                            Ok(keccak_ff_second_converter(fr, KECCAK_FIRST_SPARSE_BASE))
                        })?;

                        AllocatedNum::long_weighted_sum_eq(cs, &output1_slices[..], &output1_slice_modulus_fr, &output1_total, false)?;
                        new_state[(i, j)] = Num::Variable(output1_total);
                    }

                    if iter_count < elems_to_squeeze {
                        let mut output2_total = AllocatedNum::alloc(cs, || {
                            let fr = var.get_value().grab()?;
                            Ok(keccak_ff_second_converter(fr, BINARY_BASE))
                        })?;

                        AllocatedNum::long_weighted_sum_eq(cs, &output2_slices[..], &output2_slice_modulus_fr, &output2_total, false)?;
                        squeezed.push(Num::Variable(output2_total));
                    }
                }
            }
        }

        Ok((new_state, squeezed))
    }

    // helper functions for rho subroutine
    // returns expected num_of_chunks (if less than maximum possible value contained in a table)
    // and boolean flag indicating if chunk is last
    fn check_offset_helper(&self, cur_offset: usize, max_offset: usize, is_first_iter: bool) -> (Option<usize>, bool) {
        let is_last = cur_offset + self.first_base_num_of_chunks >= KECCAK_LANE_WIDTH;

        if is_first_iter && (cur_offset < max_offset) && (cur_offset + self.of_first_base_num_of_chunks > max_offset) {
            return (Some(max_offset - cur_offset), true);
        }
        if !is_first_iter && (cur_offset < max_offset) && (cur_offset + self.first_base_num_of_chunks > max_offset) {
            return (Some(max_offset - cur_offset), true);
        }
        if (cur_offset < KECCAK_LANE_WIDTH) && (cur_offset + self.first_base_num_of_chunks > KECCAK_LANE_WIDTH) {
            return (Some(max_offset - cur_offset), true);
        }
        return (None, is_last);
    }

    fn get_divider_helper(&self, chunk_count_bound: &Option<usize>, is_first_iter: bool) -> u64 {
        let exp = match chunk_count_bound {
            None => if is_first_iter { self.of_first_base_num_of_chunks - 1} else { self.first_base_num_of_chunks },
            Some(n) => *n,
        };

        pow(KECCAK_FIRST_SPARSE_BASE as usize, exp) as u64
    }

    fn handle_one_bit_of_arr<CS>(&self, cs: &mut CS, input: &[AllocatedNum<E>]) -> Result<Option<AllocatedNum<E>>> 
    where CS: ConstraintSystem<E>
    {
        let mut cnst : E::Fr = u64_to_ff(input.len() as u64);
        cnst.negate();
        let mut gate_vars = Vec::with_capacity(4);
        let mut res = None;

        let one = E::Fr::one();
        let mut minus_one = one.clone();
        minus_one.negate();
        let dummy = AllocatedNum::zero(cs);

        for (_is_first, is_last, elem) in input.iter().identify_first_last()  {
            if gate_vars.len() < 4 {
                gate_vars.push(elem.clone());
            }
            else {
                // we have filled in the whole vector!
                if !is_last {
                    let gate_coefs = [one.clone(), one.clone(), one.clone(), one.clone(), minus_one.clone()];
                    let temp = AllocatedNum::quartic_lc_with_cnst(cs, &gate_coefs[..], &gate_vars[..], &cnst)?;
                    gate_vars = vec![temp, elem.clone()];
                }
                else {
                    let gate_coefs = [one.clone(), one.clone(), one.clone(), one.clone(), one.clone()];
                    AllocatedNum::quartic_lc_with_cnst(cs, &gate_coefs[..], &gate_vars[..], &cnst)?;
                    res = Some(elem.clone());
                    gate_vars = vec![];
                }
                cnst = E::Fr::zero();
            }
        }

        if !gate_vars.is_empty() {
            // pad with dummy variables
            for _i in gate_vars.len()..4 {
                gate_vars.push(dummy.clone());
            }
            
            let gate_coefs = [one.clone(), one.clone(), one.clone(), one.clone(), E::Fr::zero()];
            AllocatedNum::quartic_lc_with_cnst(cs, &gate_coefs[..], &gate_vars[..], &cnst)?;
        }

        Ok(res)
    }

    fn handle_max_of_arr<CS>(&self, cs: &mut CS, input: &[AllocatedNum<E>], d_var: &Option<AllocatedNum<E>>) -> Result<()>
    where CS: ConstraintSystem<E>
    {
        let dummy = &self.allocated_one;
        let d = d_var.clone().unwrap_or(dummy.clone());
        let table = &self.ternary_range_table;

        let mut iter = input.chunks_exact(3);
        let remainder = iter.remainder(); 
        for block in iter {
            let vars = [block[0].get_variable(), block[1].get_variable(), block[2].get_variable(), d.get_variable()];
            
            cs.begin_gates_batch_for_step()?; 
            cs.allocate_variables_without_gate(
                &vars[..],
                &[]
            )?;
            cs.apply_single_lookup_gate(&vars[..table.width()], table.clone())?;
            cs.end_gates_batch_for_step()?;
        }

        if !remainder.is_empty() {
            let mut vars = [dummy.get_variable(), dummy.get_variable(), dummy.get_variable(), d.get_variable()];
            for (in_arr, out_arr) in remainder.iter().zip(vars.iter_mut()) {
                *out_arr = in_arr.get_variable(); 
            }

            cs.begin_gates_batch_for_step()?; 
            cs.allocate_variables_without_gate(
                &vars,
                &[]
            )?;
            cs.apply_single_lookup_gate(&vars[..table.width()], table.clone())?;
            cs.end_gates_batch_for_step()?;
        }

        Ok(())
    }

    fn handle_general_of<CS: ConstraintSystem<E>>(
        &self, cs: &mut CS, 
        elem: &AllocatedNum<E>, offset: u64, max_of_arr: &mut Vec<AllocatedNum<E>>, d_var: &Option<AllocatedNum<E>>,
    ) -> Result<()>
    {
        let dummy_one = &self.allocated_one;
        let dummy_zero = AllocatedNum::alloc_zero(cs)?;

        let zero = E::Fr::zero();
        let one = E::Fr::one();
        let mut minus_one = E::Fr::one();
        minus_one.negate();

        let a = AllocatedNum::alloc(cs, || {
            let mut tmp = elem.get_value().grab()?;
            let cnst : E::Fr = u64_to_ff(offset);
            tmp.add_assign(&cnst);

            Ok(tmp)
        })?;
        let b = max_of_arr.pop().unwrap_or(dummy_one.clone());

        let (c, d) = match d_var {
            None => {
                // [elem + offset, max_of_or_dummy, max_of_or_dummy, elem]
                // constraint: a = d + offset;
                (max_of_arr.pop().unwrap_or(dummy_one.clone()), elem.clone())
            },
            Some(var) => {
                // [elem + offset, max_of_dummy, elem, d]
                // constraint: a = c + offset;
                (elem.clone(), var.clone())
            },
        };
        
        let vars = [a.get_variable(), b.get_variable(), c.get_variable(), d.get_variable()];
        let range_of_linear_terms = CS::MainGate::range_of_linear_terms();
        let range_of_linear_terms_start = range_of_linear_terms.start;
        let table = &self.ternary_range_table;
        
        cs.begin_gates_batch_for_step()?;

        cs.apply_single_lookup_gate(&vars[..table.width()], table.clone())?;
    
        let mut gate_term = MainGateTerm::new();
        let (_, mut gate_coefs) = CS::MainGate::format_term(gate_term, dummy_zero.get_variable())?;

        gate_coefs[range_of_linear_terms_start] = minus_one;
        gate_coefs[range_of_linear_terms_start + 1] = zero.clone();  
        match d_var {
            None => {
                // [elem + offset, max_of_or_dummy, max_of_or_dummy, elem]
                // constraint: a = d + offset;
                gate_coefs[range_of_linear_terms_start + 2] = zero;
                gate_coefs[range_of_linear_terms_start + 3] = one;  
            },
            Some(var) => {
                // [elem + offset, max_of_dummy, elem, d]
                // constraint: a = c + offset;
                gate_coefs[range_of_linear_terms_start + 2] = one;
                gate_coefs[range_of_linear_terms_start + 3] = zero;  
            },
        };

        let cnst_index = CS::MainGate::index_for_constant_term();
        gate_coefs[cnst_index] = u64_to_ff(offset);

        let mg = CS::MainGate::default();
        cs.new_gate_in_batch(
            &mg,
            &gate_coefs,
            &vars,
            &[]
        )?;

        cs.end_gates_batch_for_step()?;

        Ok(())
    }

    // we unite /rho (rotate) and conversion (FIRST_SPARSE_BASE -> SECOND_SPARSE_BASE) in one function
    fn rho<CS: ConstraintSystem<E>>(&self, cs: &mut CS, state: KeccakState<E>) -> Result<KeccakState<E>> {
        let mut new_state = KeccakState::default();
        let mut of_map : std::collections::HashMap<usize, Vec<AllocatedNum<E>>> = HashMap::new();
        let num_slices = Self::round_up(KECCAK_LANE_WIDTH - self.of_first_base_num_of_chunks -1, self.first_base_num_of_chunks) + 3;  
        
        let input_chunks_step = u64_exp_to_ff(KECCAK_FIRST_SPARSE_BASE, self.first_base_num_of_chunks as u64);
        let output_chunks_step = u64_exp_to_ff(KECCAK_SECOND_SPARSE_BASE, self.second_base_num_of_chunks as u64);
        
        let input_chunks_of_step = u64_exp_to_ff(KECCAK_FIRST_SPARSE_BASE, (self.of_first_base_num_of_chunks - 1) as u64);
        let output_chunks_of_step = u64_exp_to_ff(KECCAK_SECOND_SPARSE_BASE, (self.of_first_base_num_of_chunks - 1) as u64);

        for (i, j) in (0..KECCAK_LANE_WIDTH).cartesian_product(0..KECCAK_LANE_WIDTH) {
            let offset = self.offsets[i][j];

            let transformed = match &state[(i, j)] {
                Num::Constant(fr) => {
                    Num::Constant(self.rotate_and_convert(fr, offset))
                },
                Num::Allocated(var) => {
                    let mut output_slices : Vec<AllocatedNum<E>> = Vec::with_capacity(num_slices);
                    let mut output_coefs : Vec<E::Fr> = Vec::with_capacity(num_slices);
                    let mut big_f = BigUint::default();
                    let mut var_has_value = false; 
                    let mut cur_offset = 0;

                    let mut cur_input_coef = E::Fr::one();
                    let mut cur_output_coef : E::Fr = u64_exp_to_ff(KECCAK_SECOND_SPARSE_BASE, (KECCAK_LANE_WIDTH - offset) as u64);
                    let mut acc = var;
                    let mut is_first_iter = true;

                    let output_total = match var.get_value() {
                        None => AllocatedNum::alloc(cs, || Err(SynthesisError::AssignmentMissing))?,
                        Some(fr) => {
                            let fr_repr = fr.into_repr();
                            for n in fr_repr.as_ref().iter().rev() {
                                big_f <<= 64;
                                big_f += *n;
                            }
                            var_has_value = true; 
                            AllocatedNum::alloc(cs, || Ok(self.rotate_and_convert(&fr, offset)))?
                        },
                    };

                    while cur_offset < KECCAK_LANE_WIDTH {
                        let (chunk_count_bound, is_last) = self.check_offset_helper(cur_offset, offset, is_first_iter);
                        let input_slice = if var_has_value {
                            let divider = self.get_divider_helper(&chunk_count_bound, is_first_iter);
                            let remainder = (big_f.clone() % BigUint::from(divider)).to_u64().unwrap();
                            let new_val = u64_to_ff(remainder);
                            big_f /= divider;
                            AllocatedNum::alloc(cs, || Ok(new_val))?
                        }
                        else {
                            AllocatedNum::alloc(cs, || Err(SynthesisError::AssignmentMissing))?
                        };

                        let table = if is_first_iter {
                            &self.of_first_to_second_base_converter_table
                        }
                        else {
                            &self.first_to_second_base_converter_table
                        };
                        let (chunk_count, output_slice, new_acc) = self.query_table_accumulate(
                            cs, table, &input_slice, &acc, &cur_input_coef, is_last
                        )?; 

                        output_coefs.push(cur_output_coef.clone());
                        output_slices.push(output_slice);

                        match chunk_count_bound {
                            None => {
                                if is_first_iter {
                                    cur_input_coef.mul_assign(&input_chunks_of_step);
                                    cur_output_coef.mul_assign(&output_chunks_of_step);
                                    cur_offset += self.of_first_base_num_of_chunks - 1;
                                }
                                else {
                                    cur_input_coef.mul_assign(&input_chunks_step);
                                    cur_output_coef.mul_assign(&output_chunks_step);
                                    cur_offset += self.first_base_num_of_chunks;
                                }
                            }
                            Some(n) => {
                                cur_input_coef.mul_assign(&u64_exp_to_ff(KECCAK_FIRST_SPARSE_BASE, n as u64));
                                cur_output_coef = E::Fr::one();
                                cur_offset += n;
                                
                                let entry = of_map.entry(n).or_insert(vec![]);
                                entry.push(chunk_count);
                            }
                        };

                        is_first_iter = false; 
                    }

                    //AllocatedNum::lc_eq(cs, &output_slices[..], &output_coefs[..], &output_total)?;
                    Num::Allocated(output_total)
                },
            };
                    
            new_state[(i, j)] = transformed;
        }

        // handle offsets
        // NB: all of this stuff may be optimized further
        let mut next_row_var = match of_map.get(&1usize) {
            None => None,
            Some(arr) => self.handle_one_bit_of_arr(cs, arr)?,
        };
        
        let mut max_of_arr = of_map.get(&(self.first_base_num_of_chunks - 1)).cloned().unwrap_or(vec![]);
        for of in 2..(self.first_base_num_of_chunks - 1) {
            let cur_of_arr = of_map.get(&of).cloned().unwrap_or(vec![]);
            for elem in cur_of_arr {
                self.handle_general_of(cs, &elem, (self.first_base_num_of_chunks - 1 - of) as u64, &mut max_of_arr, &next_row_var)?;
                next_row_var = None;
            }
        }
        
        if !max_of_arr.is_empty() {
            self.handle_max_of_arr(cs, &max_of_arr, &next_row_var)?;
            next_row_var = None;
        }

        assert!(next_row_var.is_none());

        Ok(new_state) 
    }

    fn keccak_f<CS: ConstraintSystem<E>>(
        &self, cs: &mut CS, input_state: KeccakState<E>, elems_to_squeeze: usize, elems_to_mix: Option<&[Num<E>]>, is_final: bool,
    ) -> Result<(KeccakState<E>, Option<Vec<Num<E>>>)>
    {
        let mut state = input_state;

        for round in 0..(KECCAK_NUM_ROUNDS-1) {
            state = self.theta(cs, state)?;
            state = self.pi(cs, state)?;
            state = self.rho(cs, state)?;
            let (new_state, _) = self.xi_i(cs, state, round, 0, None, false)?;
            state = new_state; 
        }

        state = self.theta(cs, state)?;
        state = self.pi(cs, state)?;
        state = self.rho(cs, state)?;
        let (mut new_state, out) = self.xi_i(cs, state, KECCAK_NUM_ROUNDS-1, elems_to_squeeze, elems_to_mix, is_final)?;
        if elems_to_mix.is_some() {
            new_state[(0, 0)] = new_state[(0, 0)].add(cs, &Num::Constant(self.round_cnsts_in_first_base[KECCAK_NUM_ROUNDS-1]))?;
        }

        let squeezed = if elems_to_squeeze > 0 { Some(out) } else { None };
        Ok((new_state, squeezed))
    }

    fn convert_binary_to_sparse_repr<CS>(&self, cs: &mut CS, input: &Num<E>, sparse_base: KECCAK_BASE) -> Result<Num<E>> 
    where CS: ConstraintSystem<E>
    {
        let output_base = match sparse_base {
            KECCAK_BASE::KECCAK_FIRST_SPARSE_BASE => KECCAK_FIRST_SPARSE_BASE,
            KECCAK_BASE::KECCAK_SECOND_SPARSE_BASE => KECCAK_SECOND_SPARSE_BASE,
            KECCAK_BASE::BINARY => unreachable!(),
        };

        let res = match input {
            Num::Constant(fr) => {
                Num::Constant(general_ff_converter(*fr, BINARY_BASE, output_base, |x| { x }))
            },
            Num::Allocated(var) => {
                let num_of_chunks = self.binary_base_num_of_chunks;
                let num_slices = Self::round_up(KECCAK_LANE_WIDTH, num_of_chunks);

                let mut input_slices : Vec<AllocatedNum<E>> = Vec::with_capacity(num_slices);
                let mut output_slices : Vec<AllocatedNum<E>> = Vec::with_capacity(num_slices);

                let input_slice_modulus = pow(BINARY_BASE as usize, num_of_chunks);
                let output1_slice_modulus = pow(output_base as usize, num_of_chunks);

                let input_slice_modulus_fr = u64_exp_to_ff(BINARY_BASE, num_of_chunks as u64);
                let output_slice_modulus_fr = u64_exp_to_ff(output_base, num_of_chunks as u64);

                match var.get_value() {
                    None => {
                        for _ in 0..num_slices {
                            let tmp = AllocatedNum::alloc(cs, || Err(SynthesisError::AssignmentMissing))?;
                            input_slices.push(tmp);
                        }
                    },
                    Some(f) => {
                        // here we have to operate on row biguint number
                        let mut big_f = BigUint::default();
                        let f_repr = f.into_repr();
                        for n in f_repr.as_ref().iter().rev() {
                            big_f <<= 64;
                            big_f += *n;
                        } 

                        for _ in 0..num_slices {
                            let remainder = (big_f.clone() % BigUint::from(input_slice_modulus)).to_u64().unwrap();
                            let new_val = u64_to_ff(remainder);
                            big_f /= input_slice_modulus;
                            let tmp = AllocatedNum::alloc(cs, || Ok(new_val))?;
                            input_slices.push(tmp);
                        }

                        assert!(big_f.is_zero());
                    }
                }

                let mut coef = E::Fr::one();
                let mut acc = var.clone();
                for (_is_first, is_last, input_chunk) in input_slices.iter().identify_first_last() {
                    let (output1, output2, new_acc) = self.query_table_accumulate(
                        cs, &self.from_binary_converter_table, input_chunk, &acc, &coef, is_last
                    )?; 

                    coef.mul_assign(&input_slice_modulus_fr);
                    acc = new_acc;

                    let output = match sparse_base {
                        KECCAK_BASE::KECCAK_FIRST_SPARSE_BASE => output1,
                        KECCAK_BASE::KECCAK_SECOND_SPARSE_BASE => output2,
                        KECCAK_BASE::BINARY => unreachable!(),
                    }; 
                    output_slices.push(output);
                }
                
                let mut output_total = AllocatedNum::alloc(cs, || {
                    let fr = var.get_value().grab()?;
                    Ok(general_ff_converter(fr, BINARY_BASE, output_base, |x| { x }))
                })?;

                AllocatedNum::long_weighted_sum_eq(cs, &output_slices[..], &output_slice_modulus_fr, &output_total, false)?;
                Num::Allocated(output_total)
            },
        };

        Ok(res)
    }

    // we assume that data is split into 64-bit words
    pub fn digest<CS: ConstraintSystem<E>>(&self, cs: &mut CS, data: &[Num<E>]) -> Result<Vec<Num<E>>> {
        assert!(data.len() % KECCAK_RATE_WORDS_SIZE == 0);
        
        let mut state = KeccakState::default();
        let mut res = Vec::with_capacity(self.digest_size);
        
        for (is_first, _is_last, data_block) in data.chunks(KECCAK_RATE_WORDS_SIZE).identify_first_last() {
            if is_first {
                for (idx, elem) in data_block.iter().enumerate() {
                    let out = self.convert_binary_to_sparse_repr(cs, elem, KECCAK_BASE::KECCAK_FIRST_SPARSE_BASE)?;
                    state[(idx % KECCAK_STATE_WIDTH, idx / KECCAK_STATE_WIDTH)] = out;
                }
            }
            else {
                let (new_state, _) = self.keccak_f(cs, state, 0, Some(data_block), false)?;
                state = new_state;
            }            
        }

        while res.len() < self.digest_size {
            let elems_to_squeeze = std::cmp::min(self.digest_size - res.len(), KECCAK_RATE_WORDS_SIZE);
            let is_final = res.len() + KECCAK_RATE_WORDS_SIZE >= self.digest_size;

            let (new_state, mut squeezed) = self.keccak_f(cs, state, elems_to_squeeze, None, is_final)?;
            state = new_state;
            res.extend(squeezed.unwrap().into_iter());
        }

        Ok(res)
    }
} 