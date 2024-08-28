use super::*;
use std::iter;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};
use crate::plonk::circuit::linear_combination::*;
use crate::plonk::circuit::SomeArithmetizable;
use crate::plonk::circuit::assignment::Assignment;
use crate::plonk::circuit::hashes_with_tables::utils::IdentifyFirstLast;
use crate::bellman::plonk::better_better_cs::lookup_tables::LookupTableApplication;
use num_bigint::BigUint;
use num_traits::Zero;


pub static NUM_RANGE_CHECK_INVOCATIONS: AtomicUsize = AtomicUsize::new(0);
// shorts range checks are range checks that occupy a single gate
pub static NUM_SHORT_RANGE_CHECK_INVOCATIONS: AtomicUsize = AtomicUsize::new(0);
pub static NUM_GATES_SPENT_ON_RANGE_CHECKS: AtomicUsize = AtomicUsize::new(0);

pub fn reset_stats() {
    NUM_RANGE_CHECK_INVOCATIONS.store(0, Ordering::Relaxed);
    NUM_SHORT_RANGE_CHECK_INVOCATIONS.store(0, Ordering::Relaxed);
    NUM_GATES_SPENT_ON_RANGE_CHECKS.store(0, Ordering::Relaxed);
}

fn increment_invocation_count() {
    NUM_RANGE_CHECK_INVOCATIONS.fetch_add(1, Ordering::SeqCst);
}

fn increment_short_checks_count() {
    NUM_SHORT_RANGE_CHECK_INVOCATIONS.fetch_add(1, Ordering::SeqCst);
}

fn increment_total_gates_count(val: usize) {
    NUM_GATES_SPENT_ON_RANGE_CHECKS.fetch_add(val, Ordering::SeqCst);
}

pub fn print_stats() {
    let total_checks = NUM_RANGE_CHECK_INVOCATIONS.load(Ordering::Relaxed);
    let short_checks = NUM_SHORT_RANGE_CHECK_INVOCATIONS.load(Ordering::Relaxed);
    let total_gates = NUM_GATES_SPENT_ON_RANGE_CHECKS.load(Ordering::Relaxed);
    println!(
        "Has made in total of {} range checks, with {} being short (singe gate) and {} gates in total", 
        total_checks, short_checks, total_gates
    );
}


pub enum DecompositionType<E: Engine> {
    BitDecomposition(Vec<AllocatedBit>),
    ChunkDecomposition(Vec<AllocatedNum<E>>),
}

pub struct RangeCheckDecomposition<E: Engine>
{
    chunks_bitlength: usize,
    decomposition: DecompositionType<E>
}

impl<E: Engine> RangeCheckDecomposition<E> {
    pub fn get_chunk_bitlen(&self) -> usize {
        self.chunks_bitlength
    }

    pub fn get_num_chunks(&self) -> usize {
        match &self.decomposition {
            DecompositionType::BitDecomposition(x) => x.len(),
            DecompositionType::ChunkDecomposition(x) => x.len()
        }
    }

    pub fn is_bit_decomposition(&self) -> bool {
        match &self.decomposition {
            DecompositionType::BitDecomposition(_) => true,
            DecompositionType::ChunkDecomposition(_) => false
        }
    }

    pub fn get_total_value(&self) -> Option<BigUint> {
        let (values, chunk_size) : (Vec<Option<E::Fr>>, usize) = match &self.decomposition {
            DecompositionType::BitDecomposition(_) => {
                let elems: Vec<Option<E::Fr>> = self.get_bits().iter().map(|x| {
                     x.get_value_as_field_element::<E>() 
                }).collect();
                (elems, 1)
            },
            DecompositionType::ChunkDecomposition(_) => {
                let elems: Vec<Option<E::Fr>> = self.get_vars().iter().map(|x| { x.get_value() }).collect();
                (elems, self.chunks_bitlength)
            }
        };
        if values.iter().any(|x| x.is_none()) {
            return None;
        };
            
        let mut result = BigUint::zero();
        for elem in values.into_iter().rev() {
            result <<= chunk_size;
            result += fe_to_biguint(&elem.unwrap())
        }
        Some(result)
    }

    pub fn get_bits(&self) -> &Vec<AllocatedBit> {
        if let DecompositionType::BitDecomposition(ref x) = self.decomposition { &x } else { unreachable!(); }
    }

    pub fn get_vars(&self) -> &Vec<AllocatedNum<E>> {
        if let DecompositionType::ChunkDecomposition(ref x) = self.decomposition { &x } else { unreachable!(); }
    }

    pub fn combine(separate_decompositions: &[Self]) -> Self {
        let flag = separate_decompositions.windows(2).all(|w| w[0].chunks_bitlength == w[1].chunks_bitlength);
        assert!(flag);

        let total_decomposition = match &separate_decompositions[0].decomposition {
            &DecompositionType::BitDecomposition(_) => {
                let all_bits = separate_decompositions.iter().map(|x| x.get_bits()).flatten().cloned().collect();
                DecompositionType::BitDecomposition(all_bits)
            },
            &DecompositionType::ChunkDecomposition(_) => {
                let all_vars = separate_decompositions.iter().map(|x| x.get_vars()).flatten().cloned().collect();
                DecompositionType::ChunkDecomposition(all_vars)
            }
        }; 

        RangeCheckDecomposition::<E>
        {
            chunks_bitlength: separate_decompositions[0].chunks_bitlength,
            decomposition: total_decomposition
        }
    }
}


// if coarsely flag is set that we constraint bit length up to range check granularity
pub fn constraint_bit_length_ext_with_strategy<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS, var: &AllocatedNum<E>, num_bits: usize, strategy: RangeConstraintStrategy, coarsely: bool
) -> Result<RangeCheckDecomposition<E>, SynthesisError> {
    match strategy {
        RangeConstraintStrategy::NaiveSingleBit => {
            enforce_range_check_using_naive_approach(cs, var, num_bits)
        },
        RangeConstraintStrategy::CustomTwoBitGate => {
            unreachable!();
            enforce_range_check_using_custom_gate(cs, var, num_bits, coarsely)
        },
        RangeConstraintStrategy::WithBitwiseOpTable(_table_width) => {  
            let table = cs.get_table(BITWISE_LOGICAL_OPS_TABLE_NAME).expect("should found a valid table");         
            enforce_range_check_using_bitop_table(cs, var, num_bits, table, coarsely)
        }    
    }
}

pub fn constraint_bit_length_with_strategy<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS, var: &AllocatedNum<E>, num_bits: usize, range_check_strategy: RangeConstraintStrategy
) -> Result<(), SynthesisError> {
    let _decomposition = constraint_bit_length_ext_with_strategy(cs, var, num_bits, range_check_strategy, false)?;
    Ok(())
}

pub fn coarsely_constraint_bit_length_with_strategy<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS, var: &AllocatedNum<E>, num_bits: usize, range_check_strategy: RangeConstraintStrategy
) -> Result<(), SynthesisError> {
    let _decomposition = constraint_bit_length_ext_with_strategy(cs, var, num_bits, range_check_strategy, true)?;
    Ok(())
}

// enforces that bitlength(var) <= shift and returns the decomposition of var into smaller chunks
// the actual bitsize and type of chunks depends on the chosen strategy
pub fn constraint_bit_length_ext<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS, var: &AllocatedNum<E>, num_bits: usize
) -> Result<RangeCheckDecomposition<E>, SynthesisError> {
    let range_check_strategy = get_optimal_strategy(cs);
    constraint_bit_length_ext_with_strategy(cs, var, num_bits, range_check_strategy, false)
}

pub fn constraint_bit_length<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS, var: &AllocatedNum<E>, num_bits: usize
) -> Result<(), SynthesisError> {
    let _decomposition = constraint_bit_length_ext(cs, var, num_bits)?;
    Ok(())
}


pub fn allocate_gate_with_linear_only_terms<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS, vars: &[Variable], coefs: &[E::Fr], d_next_coef: &E::Fr
) -> Result<(), SynthesisError> {
    let dummy = CS::get_dummy_variable();
    let range_of_linear_terms = CS::MainGate::range_of_linear_terms();
    let next_row_term_idx = CS::MainGate::range_of_next_step_linear_terms().last().unwrap();
    
    let gate_term = MainGateTerm::new();
    let (_, mut local_coeffs) = CS::MainGate::format_term(gate_term, dummy)?;
    for (pos, coef) in range_of_linear_terms.zip(coefs.iter()) {
        local_coeffs[pos] = coef.clone();
    } 
    local_coeffs[next_row_term_idx] = d_next_coef.clone();

    let mg = CS::MainGate::default();
    let local_vars : Vec<Variable> = vars.iter().cloned().collect();
    cs.new_single_gate_for_trace_step(&mg, &local_coeffs, &local_vars, &[])
}


// enforce that bitlength(var * shift) <= num_bits using naive approach which is the following:
// we decompose var * shift into single bits [f0, f1, ..., fn], for each f_i we enforce that f_i is actually a bit
// by f_i * (f_i - 1) == 0
// and then construct the long linear combination: var = \sum 2^i * f_i
pub fn enforce_range_check_using_naive_approach<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS, var: &AllocatedNum<E>, num_bits: usize
) -> Result<RangeCheckDecomposition<E>, SynthesisError> {
    increment_invocation_count();
    // count all constraints of the form f * (f - 1) == 0
    increment_total_gates_count(num_bits);
    // we should additionally count gates used in long linear combination:
    // if num_bits <= 3, then there is a single gate: f0 + 2*f1 + 4*f2 = var
    // if 4 <= num_bits <= 6 there will be two gates: f0 + 2*f1 + 4*f2 + 8*f3 = d_next, d_next + 16*f4 + 32*f5 = var
    // if num_bits > 6, then the first gate will be of the form:
    //      f0 + 2*f1 + 4*f2 + 8*f3 = d_next - and hence contain 4 variables
    // the last gate will be of the form: 
    //      d_last + 2^(n-1)*f_(n-1) +2^n * f_n = var and hence containt 2 variables f_i
    // all intermediate gates will be of the form: 
    //      2^i f_i + 2^(i+1) f_(i+1) + 2^(i+2) f_(i+2) + d_cur = d_next and hence containt 3 variables f_i
    // hence the total number of gates in linear combination will be: 2 + x, where x is the smallest integer,
    // such that 3 * x + 6 >= num_bits => x = ceil(num_bits / 3) - 2
    let lc_gates : usize = match num_bits {
        1..=3 => 1,
        4..=6 => 2,
        _ => (num_bits + 2) / 3 - 2, 
    };
    increment_total_gates_count(lc_gates);

    let has_value = var.get_value().is_some();
    let value = var.get_value().unwrap_or(E::Fr::zero());
    
    let value_bits : Vec<bool> = BitIterator::new(value.into_repr()).collect();
    let allocated_bits : Vec<AllocatedBit> = value_bits.into_iter().rev().take(num_bits).map(|bit| {
        let t = if has_value { Some(bit) } else { None };
        AllocatedBit::alloc(cs, t)
    }).collect::<Result<Vec<_>, SynthesisError>>()?;

    let mut minus_one = E::Fr::one();
    minus_one.negate();

    if num_bits < CS::Params::STATE_WIDTH {
        let mut lc = LinearCombination::zero();
        let mut coef = E::Fr::one();
        for bit in allocated_bits.iter() {
            lc.add_assign_bit_with_coeff(bit, coef.clone());
            coef.double();
        }
        lc.add_assign_variable_with_coeff(var, minus_one);
        lc.enforce_zero(cs)?;
    }
    else {
        let mut coef = E::Fr::one();
        let mut idx = 0;
        let mut is_first = true;
        let mut total_is_added = false;
        let mut acc = AllocatedNum::zero(cs);

        while idx < allocated_bits.len() {
            // For the first gate, we can use all terms to accumulate the bits
            // For the remaining gates, we must reserve the last term to add in the accumulator
            let non_first_slice_len = std::cmp::min(CS::Params::STATE_WIDTH - 1, allocated_bits.len() - idx); 
            let slice_len = if is_first { CS::Params::STATE_WIDTH } else { non_first_slice_len };

            let mut coefs : Vec<E::Fr> = (0..slice_len+1).scan(coef.clone(), |st, _| {
                let res = st.clone(); st.double(); Some(res)
            }).collect();
            coef = coefs.pop().unwrap();

            let (mut vars, mut vals): (Vec<_>, Vec<Option<_>>) = allocated_bits[idx..idx + slice_len].iter().map(|x| {
                (x.get_variable(), x.get_value_as_field_element::<E>())
            }).unzip(); 
            assert_eq!(coefs.len(), vars.len());

            while coefs.len() < CS::Params::STATE_WIDTH - 1 {
                if total_is_added {
                    coefs.push(E::Fr::zero()); 
                    vars.push(CS::get_dummy_variable()); 
                    vals.push(Some(E::Fr::zero()));
                }
                else {
                    total_is_added = true;
                    coefs.push(minus_one.clone());
                    vars.push(var.get_variable());
                    vals.push(var.get_value());
                }
            }
            if !is_first {
                coefs.push(E::Fr::one());
                vars.push(acc.get_variable());
            }

            acc = if total_is_added {
                AllocatedNum::zero(cs)
            }
            else {
                AllocatedNum::alloc(cs, || {
                    let mut res = acc.get_value().grab()?;
                    for (val, coef) in vals.iter().zip(coefs.iter()) {       
                        let mut tmp = val.grab()?;
                        tmp.mul_assign(&coef);
                        res.add_assign(&tmp);
                    }
                    Ok(res)
                })?
            };
            
            let d_next_coef = if total_is_added { E::Fr::zero() } else { minus_one.clone() };
            allocate_gate_with_linear_only_terms(cs, &vars[..], &coefs[..], &d_next_coef)?;

            idx += slice_len;
            is_first = false;
        }

        if !total_is_added {
            let coefs = vec![E::Fr::zero(); CS::Params::STATE_WIDTH];
            let mut vars = vec![CS::get_dummy_variable(); CS::Params::STATE_WIDTH];
            *vars.last_mut().unwrap() = acc.get_variable();
            allocate_gate_with_linear_only_terms(cs, &vars[..], &coefs[..], &E::Fr::zero())?;
        }
    }

    Ok(RangeCheckDecomposition {
        chunks_bitlength: 1,
        decomposition: DecompositionType::BitDecomposition(allocated_bits),
    })
}


fn split_into_bit_constraint_slices<F: PrimeField>(el: &F, slice_width: usize, num_slices: usize) -> Vec<F> {
    // gate accumulates values a bit differently: each time it shift previous slice by X bits
    // and adds a new chunk into lowest bits, and then constraints the difference
    let bases = split_into_slices(el, slice_width, num_slices);
    let mut slices = Vec::with_capacity(num_slices);
    let mut accum = F::zero();
    let mut base = F::one();
    for _ in 0..slice_width {
        base.double();
    }
    for s in bases.into_iter().rev() {
        accum.mul_assign(&base); // shift existing accumulator
        accum.add_assign(&s); // add into lowest bits

        slices.push(accum);
    }

    slices
}


// enforce bitlength(var * shift) <= num_bits via custom gate of the form:
// { d_next - 4a /in [0, 3], a - 4b /in [0, 3], b - 4c /in [0, 3], c - 4d /in [0, 3]
pub fn enforce_range_check_using_custom_gate<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS, var: &AllocatedNum<E>, num_bits: usize, _coarsely: bool
) -> Result<RangeCheckDecomposition<E>, SynthesisError> 
{
    assert!(num_bits > 0);
    // TODO: there should be additional logic for num_bits &1 != 0
    // for now every such allocation is automatically coarse on 2 bit granularity
    assert!(num_bits & 1 == 0);
    assert_eq!(CS::Params::STATE_WIDTH, 4, "this only works for a state of width 4 for now");
    const NUM_BITS_PER_GATE: usize = 8;
    increment_invocation_count();

    if let Some(v) = var.get_value() {
        let t = self::bigint::fe_to_biguint(&v);
        assert!(
            t.bits() as usize <= num_bits, "value is {} that is {} bits, while expected {} bits", 
            t.to_str_radix(16), t.bits(), num_bits
        );
    }
    let num_elements = num_bits / 2;
    let mut slices: Vec<Option<E::Fr>> = if let Some(v) = var.get_value() {
        split_into_bit_constraint_slices(&v, 2, num_elements).into_iter().map(|el| Some(el)).collect()
    } else {
        vec![None; num_elements]
    };

    let last_val = slices.pop().unwrap();
    if let Some(last_val) = last_val {
        if let Some(v) = var.get_value() {
            assert_eq!(last_val, v);
        }
    }
    
    let mut result = vec![];
    for v in slices.into_iter() {
        let a = AllocatedNum::alloc(cs, || {
                Ok(*v.get()?)
            }
        )?;
        result.push(a);
    }
    // last element is actually an element we want to constraint
    result.push(var.clone());

    let num_gates = (num_bits + NUM_BITS_PER_GATE - 1) / NUM_BITS_PER_GATE;
    let mut raw_variables = Vec::with_capacity(result.len() + 1);
    raw_variables.push(cs.get_explicit_zero()?);
    // we start at D(x) with 0
    for el in result.iter() {
        raw_variables.push(el.get_variable());
    }

    let mut four = E::Fr::one();
    four.double();
    four.double();
    let some_four = Some(four);

    let mut previous_value = var.get_value();
    while raw_variables.len() % CS::Params::STATE_WIDTH != 1 {
        let new_value = previous_value.mul(&some_four);
        let padding = cs.alloc(|| Ok(*new_value.get()?))?;
        raw_variables.push(padding);
        previous_value = new_value;
    }
    assert_eq!(raw_variables.len() % CS::Params::STATE_WIDTH, 1, "variables len = {}", raw_variables.len());
    
    let mut rows = raw_variables.chunks_exact(CS::Params::STATE_WIDTH);
    let gate = TwoBitDecompositionRangecheckCustomGate::default();

    for row in &mut rows {
        let mut row = row.to_vec();
        row.reverse();
        cs.new_single_gate_for_trace_step(&gate, &[], &row, &[])?;
    }

    let last = rows.remainder();
    assert!(last.len() == 1);
    let last = last[0];
    let dummy = CS::get_dummy_variable();

    // cause we touch D_Next we place an empty gate to the last row
    let (mut variables, coeffs) = CS::MainGate::format_term(MainGateTerm::new(), dummy)?;
    *variables.last_mut().unwrap() = last;
    cs.new_single_gate_for_trace_step(&CS::MainGate::default(), &coeffs, &variables, &[])?;

    increment_total_gates_count(num_gates+1);
    Ok(RangeCheckDecomposition {
        chunks_bitlength: 2,
        decomposition: DecompositionType::ChunkDecomposition(result),
    })
}


pub fn apply_range_table_gate<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS, a: &AllocatedNum<E>, b: &AllocatedNum<E>, acc: &AllocatedNum<E>, 
    shift_a: &E::Fr, shift_b: &E::Fr, shift_acc: &E::Fr, shift_d_next: &E::Fr,
    table: Arc<LookupTableApplication<E>>, is_final: bool
) -> Result<AllocatedNum<E>, SynthesisError>
{
    let a_xor_b = match (a.get_value(), b.get_value()) {
        (Some(a_val), Some(b_val)) => {
            let res = table.query(&[a_val, b_val])?;
            AllocatedNum::alloc(cs, || Ok(res[0]))?
        },  
        (_, _) => AllocatedNum::alloc(cs, || Err(SynthesisError::AssignmentMissing))?
    };

    let new_acc = if !is_final {
        AllocatedNum::alloc(cs, || {
            let mut res = acc.get_value().grab()?;            
            let mut tmp = a.get_value().grab()?;
            tmp.mul_assign(&shift_a);
            res.sub_assign(&tmp);
            tmp = b.get_value().grab()?;
            tmp.mul_assign(&shift_b);
            res.sub_assign(&tmp);
            let div_inv = shift_d_next.inverse().unwrap();
            res.mul_assign(&div_inv);
            Ok(res)
        })?
    }
    else {
        AllocatedNum::zero(cs)
    };

    let dummy = AllocatedNum::zero(cs);
    let mut minus_one = E::Fr::one();
    minus_one.negate();

    let range_of_linear_terms = CS::MainGate::range_of_linear_terms();
    let range_of_next_step_linear_terms = CS::MainGate::range_of_next_step_linear_terms();
    let idx_of_last_linear_term = range_of_next_step_linear_terms.last().expect("must have an index");

    // new_acc * shift_d_next = prev_acc - a * shift_a - b * shift_b
    // or: a * shift_a + b * shift_b + new_acc * shift_d_next - prev_acc = 0;
    let vars = [a.get_variable(), b.get_variable(), a_xor_b.get_variable(), acc.get_variable()];
    let coeffs = [shift_a.clone(), shift_b.clone(), E::Fr::zero(), shift_acc.clone()];

    cs.begin_gates_batch_for_step()?;
    cs.apply_single_lookup_gate(&vars[..table.width()], table.clone())?;

    let gate_term = MainGateTerm::new();
    let (_, mut gate_coefs) = CS::MainGate::format_term(gate_term, dummy.get_variable())?;

    for (idx, coef) in range_of_linear_terms.clone().zip(coeffs.iter()) {
        gate_coefs[idx] = *coef;
    }
    if !is_final {
        gate_coefs[idx_of_last_linear_term] = shift_d_next.clone();
    }

    let mg = CS::MainGate::default();
    cs.new_gate_in_batch(&mg, &gate_coefs, &vars, &[])?;
    cs.end_gates_batch_for_step()?;

    Ok(new_acc)
}


pub fn enforce_range_check_using_bitop_table<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS, var: &AllocatedNum<E>, num_bits: usize, table: Arc<LookupTableApplication<E>>, coarsely: bool
) -> Result<RangeCheckDecomposition<E>, SynthesisError> 
{
    let chunk_width = (crate::log2_floor(table.size()) / 2) as usize;
    let num_chunks = (num_bits + chunk_width - 1) / chunk_width;
    let should_enforce_for_shifted_chunk = (num_bits % chunk_width) != 0 && !coarsely;

    increment_invocation_count();
    if (num_chunks == 1 && should_enforce_for_shifted_chunk) || (num_chunks <= 2 && !should_enforce_for_shifted_chunk) 
    {
        increment_short_checks_count();
    }
    increment_total_gates_count((num_chunks + 1 + should_enforce_for_shifted_chunk as usize)/2);
    
    let value = var.get_value().map(|x| { fe_to_biguint(&x) });
    let chunks = split_some_into_fixed_number_of_limbs(value, chunk_width, num_chunks).into_iter().map(|x| {
        AllocatedNum::alloc(cs, || some_biguint_to_fe::<E::Fr>(&x).grab())
    }).collect::<Result<Vec<AllocatedNum<E>>, SynthesisError>>()?;

    let dummy = AllocatedNum::zero(cs);
    let shifts = compute_shifts::<E::Fr>();
    let shift_a = E::Fr::one();
    let shift_b = shifts[chunk_width].clone();
    let shift_d_next = shifts[chunk_width * 2].clone();
    let mut minus_one = E::Fr::one();
    minus_one.negate();
    let mut acc = var.clone();

    let is_even_num_of_chunks = chunks.len() % 2 == 0;
    let last_chunk = chunks.last().unwrap().clone();
    let iter = chunks.chunks_exact(2);
    
    for (_is_first, mut is_final, pair) in iter.identify_first_last() {
        // a + b * shift = acc - acc_next * shift^2;
        // a + b * shift - acc + acc_next * shift^2;
        let (a, b) = (&pair[0], &pair[1]);
        is_final &= is_even_num_of_chunks; 
        acc = apply_range_table_gate(cs, a, b, &acc, &shift_a, &shift_b, &minus_one.clone(), &shift_d_next, table.clone(), is_final)?;
    }

    if !is_even_num_of_chunks || should_enforce_for_shifted_chunk {
        // if we should_enforce_for_shifted_chunk than our last gate would be of the form:
        // [a, b, a ^ b, a] with arithmetic condition: b = a * shift
        // else it is just [a, 0, a^0, a]
        let shift = u64_to_fe::<E::Fr>(1 << (chunk_width - (num_bits % chunk_width)));
        let a = last_chunk;
        let b = if should_enforce_for_shifted_chunk {
            AllocatedNum::alloc(cs, || {
                let mut res = last_chunk.get_value().grab()?;
                res.mul_assign(&shift);
                Ok(res)
            })?
        }
        else {
            dummy.clone()
        };
        
        let shift_a = if should_enforce_for_shifted_chunk { shift } else { E::Fr::zero() };
        let shift_b = if should_enforce_for_shifted_chunk { minus_one.clone() } else { E::Fr::zero() };
        apply_range_table_gate(cs, &a, &b, &a, &shift_a, &shift_b, &E::Fr::zero(), &E::Fr::zero(), table.clone(), true)?;
    } 

    Ok(RangeCheckDecomposition {
        chunks_bitlength: chunk_width,
        decomposition: DecompositionType::ChunkDecomposition(chunks),
    })
}


#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn check_two_bit_gate() {
        use crate::bellman::pairing::bn256::{Bn256, Fr};
        use crate::bellman::plonk::better_better_cs::cs::*;
        use crate::plonk::circuit::bigint_new::*;
        use crate::plonk::circuit::linear_combination::*;
        use crate::plonk::circuit::allocated_num::*;

        struct Tester;

        impl Circuit<Bn256> for Tester {
            type MainGate = Width4MainGateWithDNext;

            fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<Bn256>>>, SynthesisError> {
                Ok(
                    vec![
                        Self::MainGate::default().into_internal(),
                        TwoBitDecompositionRangecheckCustomGate::default().into_internal(),
                    ]
                )
            }
            fn synthesize<CS: ConstraintSystem<Bn256>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
                let variables: Vec<_> = (0..5).map(|_| AllocatedNum::alloc(
                    cs, 
                    || {
                        Ok(Fr::one())
                    }
                ).unwrap()).collect();
        
                let mut lc = LinearCombination::<Bn256>::zero();
                lc.add_assign_constant(Fr::one());
                let mut current = Fr::one();
                for v in variables.iter() {
                    lc.add_assign_variable_with_coeff(v, current);
                    current.double();
                }
        
                let _result = lc.into_allocated_num(cs).unwrap();
            
                let num = AllocatedNum::alloc(
                    cs,
                    || {
                        Ok(Fr::from_str("40000").unwrap())
                    }
                ).unwrap();
        
                let _ = enforce_range_check_using_custom_gate(cs, &num, 18, false)?;

                Ok(())
            }
        }

        let mut assembly = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

        let circuit = Tester;
        circuit.synthesize(&mut assembly).unwrap();
        assert!(assembly.is_satisfied());

        let gate = assembly.sorted_gates[1].box_clone();
        dbg!(assembly.aux_gate_density.0.get(&gate));

        assembly.finalize();

        use crate::bellman::worker::Worker;

        let worker = Worker::new();

        let setup = assembly.create_setup::<Tester>(&worker).unwrap();

        use crate::bellman::kate_commitment::*;
        use crate::bellman::plonk::commitments::transcript::{*, keccak_transcript::RollingKeccakTranscript};

        let crs_mons =
            Crs::<Bn256, CrsForMonomialForm>::crs_42(setup.gate_selectors_monomials[0].size(), &worker);

        let _proof = assembly.create_proof::<_, RollingKeccakTranscript<Fr>>(
            &worker, 
            &setup, 
            &crs_mons,
            None
        ).unwrap();
    }

    #[cfg(test)]
mod test {
    use super::*;
    use crate::bellman::pairing::bn256::{Fq, Bn256, Fr};
    use plonk::circuit::Width4WithCustomGates;
    
    #[test]
    fn test_unalligned_range_check_via_table() {
        let mut cs = TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();
        inscribe_default_bitop_range_table(&mut cs).unwrap();
        let var = AllocatedNum::alloc(&mut cs, || Ok(u64_to_fe::<Fr>(0b1111111))).unwrap();
        constraint_bit_length(&mut cs, &var, 8).unwrap();

        assert!(cs.is_satisfied()); 
    }

    #[test]
    fn check_naive() {
        use crate::bellman::pairing::bn256::{Bn256, Fr};
        use crate::bellman::plonk::better_better_cs::cs::*;
        use crate::plonk::circuit::bigint_new::*;
        use crate::plonk::circuit::linear_combination::*;
        use crate::plonk::circuit::allocated_num::*;

        struct Tester;

        impl Circuit<Bn256> for Tester {
            type MainGate = Width4MainGateWithDNext;

            fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<Bn256>>>, SynthesisError> {
                Ok(
                    vec![
                        Self::MainGate::default().into_internal(),
                    ]
                )
            }
            fn synthesize<CS: ConstraintSystem<Bn256>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
                let num = AllocatedNum::alloc(
                    cs,
                    || {
                        Ok(Fr::from_str("1").unwrap())
                    }
                ).unwrap();
                let _ = enforce_range_check_using_naive_approach(cs, &num, 2)?;

                let num = AllocatedNum::alloc(
                    cs,
                    || {
                        Ok(Fr::from_str("255").unwrap())
                    }
                ).unwrap();
                let _ = enforce_range_check_using_naive_approach(cs, &num, 8)?;

                let num = AllocatedNum::alloc(
                    cs,
                    || {
                        Ok(Fr::from_str("511").unwrap())
                    }
                ).unwrap();
                let _ = enforce_range_check_using_naive_approach(cs, &num, 9)?;

                Ok(())
            }
        }

        let mut assembly = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

        let circuit = Tester;
        circuit.synthesize(&mut assembly).unwrap();
        assert!(assembly.is_satisfied());

        assembly.finalize();
    }

    #[test]
    #[should_panic]
    fn check_naive_error() {
        use crate::bellman::pairing::bn256::{Bn256, Fr};
        use crate::bellman::plonk::better_better_cs::cs::*;
        use crate::plonk::circuit::bigint_new::*;
        use crate::plonk::circuit::linear_combination::*;
        use crate::plonk::circuit::allocated_num::*;

        struct Tester;

        impl Circuit<Bn256> for Tester {
            type MainGate = Width4MainGateWithDNext;

            fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<Bn256>>>, SynthesisError> {
                Ok(
                    vec![
                        Self::MainGate::default().into_internal(),
                    ]
                )
            }
            fn synthesize<CS: ConstraintSystem<Bn256>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
                let num = AllocatedNum::alloc(
                    cs,
                    || {
                        Ok(Fr::from_str("256").unwrap())
                    }
                ).unwrap();
                let _ = enforce_range_check_using_naive_approach(cs, &num, 8)?;

                Ok(())
            }
        }

        let mut assembly = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

        let circuit = Tester;
        circuit.synthesize(&mut assembly).unwrap();
        assert!(assembly.is_satisfied());

        assembly.finalize();
    }


}
}
