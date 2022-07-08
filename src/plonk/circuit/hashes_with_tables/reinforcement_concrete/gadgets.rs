use crate::bellman::pairing::ff::*;
use crate::bellman::pairing::ff::{PrimeField, PrimeFieldRepr};
use crate::bellman::plonk::better_better_cs::cs::*;
use crate::bellman::plonk::better_better_cs::lookup_tables::*;
use crate::bellman::plonk::better_better_cs::utils;
use crate::bellman::Engine;
use crate::bellman::SynthesisError;
use crate::plonk::circuit::allocated_num::{AllocatedNum, Num};
use crate::plonk::circuit::assignment::Assignment;
use crate::plonk::circuit::bigint::biguint_to_fe;
use crate::plonk::circuit::bigint::repr_to_biguint;
use crate::plonk::circuit::boolean::{AllocatedBit, Boolean};
use crate::plonk::circuit::byte::Byte;
use crate::plonk::circuit::custom_5th_degree_gate_optimized::Nonlinearity5CustomGate;
use crate::plonk::circuit::custom_rescue_gate::Rescue5CustomGate;
use crate::plonk::circuit::linear_combination::*;

use super::super::tables::*;
use super::super::utils::*;
use super::super::{AllocatedNumExtension, NumExtension};
use super::tables::*;
use num_traits::signum;
use sha3::{digest::ExtendableOutput, digest::Update, digest::XofReader, Sha3XofReader, Shake128};

use crate::num_bigint::BigUint;
use crate::num_traits::cast::ToPrimitive;
use crate::num_traits::{One, Zero};
use std::cmp::Ordering;
use std::convert::TryInto;
use std::ops::{Index, IndexMut};
use std::sync::Arc;

type Result<T> = std::result::Result<T, SynthesisError>;

pub const RC_STATE_WIDTH: usize = 3;
pub const RC_RATE: usize = 2;
pub const RC_PRE_ROUNDS_COUNT: usize = 3;
pub const RC_POST_ROUNDS_COUNT: usize = 3;
pub const RC_TOTAL_ROUNDS_COUNT: usize = RC_PRE_ROUNDS_COUNT + RC_POST_ROUNDS_COUNT + 1;
pub const RC_ROUND_CONSTS_COUNT: usize = (RC_TOTAL_ROUNDS_COUNT + 1) * RC_STATE_WIDTH;
pub const RC_INIT_SHAKE: &'static str = "ReinforcedConcrete";

#[derive(Clone)]
pub struct RCState<E: Engine>([Num<E>; RC_STATE_WIDTH]);

impl<E: Engine> Default for RCState<E> {
    fn default() -> Self {
        RCState(<[Num<E>; RC_STATE_WIDTH]>::default())
    }
}

impl<E: Engine> RCState<E> {
    fn from_raw(raw_state: &[Num<E>]) -> Self {
        assert_eq!(raw_state.len(), RC_STATE_WIDTH);
        let mut inner = [Num::<E>::zero(); RC_STATE_WIDTH];
        for (in_elem, out_elem) in raw_state.iter().zip(inner.iter_mut()) {
            *out_elem = in_elem.clone();
        }
        RCState(inner)
    }
}

impl<E: Engine> Index<usize> for RCState<E> {
    type Output = Num<E>;

    fn index(&self, index: usize) -> &Self::Output {
        assert!(index < RC_STATE_WIDTH);
        &self.0[index]
    }
}

impl<E: Engine> IndexMut<usize> for RCState<E> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        assert!(index < RC_STATE_WIDTH);
        &mut self.0[index]
    }
}

pub struct DecomposedNum<E: Engine> {
    pub in_chunks: Vec<Num<E>>,
    pub out_chunks: Vec<Num<E>>,
    pub state_trns: Vec<Num<E>>,
    pub ge_p_flags: Vec<Num<E>>,
}

#[derive(Clone)]
pub struct ReinforcementConcreteGadget<E: Engine> {
    // used tables
    rc_helper_table0: Arc<LookupTableApplication<E>>,
    rc_helper_table1: Arc<LookupTableApplication<E>>,

    // constants
    alphas: [E::Fr; 2],
    betas: [E::Fr; 2],
    p_prime: u16,
    s_arr: Vec<u16>,
    b_arr: Vec<E::Fr>,
    u_arr: Vec<u16>,

    pub use_optimized_fifth_power: bool,
    mds_matrix: [[E::Fr; RC_STATE_WIDTH]; RC_STATE_WIDTH],
    round_constants: [E::Fr; RC_ROUND_CONSTS_COUNT],

    state: RCState<E>,
    num_squeezed: usize,
}

impl<E: Engine> ReinforcementConcreteGadget<E> {
    pub fn new<CS: ConstraintSystem<E>, F: Fn(u16) -> u16>(
        cs: &mut CS,
        alphas: [E::Fr; 2],
        betas: [E::Fr; 2],
        p_prime: u16,
        s_arr: Vec<u16>,
        perm_f: F,
        use_optimized_fifth_power: bool,
    ) -> Result<Self> {
        let columns3 = vec![
            PolyIdentifier::VariablesPolynomial(0),
            PolyIdentifier::VariablesPolynomial(1),
            PolyIdentifier::VariablesPolynomial(2),
        ];

        let name0: &'static str = "rc_helper_table0";
        let rc_helper_table0 = LookupTableApplication::new(
            name0,
            ReinforcementConcreterHelperTable0::new(name0),
            columns3.clone(),
            None,
            true,
        );
        let rc_helper_table0 = cs.add_table(rc_helper_table0)?;

        // we are going to check that \prod s_i >= E::Fr::modulus
        // we compute the sequence of u_i and check that p <= u_i
        let modulus = repr_to_biguint::<E::Fr>(&<E::Fr as PrimeField>::char());
        let mut x = modulus.clone() - 1u64;
        let mut u_arr = Vec::with_capacity(s_arr.len());
        let mut b_arr = Vec::with_capacity(s_arr.len());
        let mut s_prod = BigUint::one();

        for s in s_arr.iter().rev() {
            b_arr.push(biguint_to_fe::<E::Fr>(s_prod.clone()));
            s_prod *= *s;
            let u = (x.clone() % s).to_u16().unwrap();
            u_arr.push(u);
            x = (x - u) / s;

            assert!(p_prime <= u);
        }
        assert!(s_prod >= modulus);
        u_arr.reverse();
        b_arr.reverse();

        let name1: &'static str = "rc_helper_table1";
        let rc_helper_table1 = LookupTableApplication::new(
            name1,
            ReinforcementConcreterHelperTable1::new(p_prime, perm_f, &s_arr, &u_arr, name1),
            columns3.clone(),
            None,
            true,
        );
        let rc_helper_table1 = cs.add_table(rc_helper_table1)?;

        // initialize MDS matrix:
        //
        //     (2  1  1)
        // M = (1  2  1)
        //     (1  1  2)
        let one_fr = E::Fr::one();
        let mut two_fr = one_fr.clone();
        two_fr.double();
        let mds_matrix = [
            [two_fr.clone(), one_fr.clone(), one_fr.clone()],
            [one_fr.clone(), two_fr.clone(), one_fr.clone()],
            [one_fr.clone(), one_fr.clone(), two_fr.clone()],
        ];

        // initialize round constants
        let mut shake = Shake128::default();
        shake.update(RC_INIT_SHAKE);
        for i in <E::Fr as PrimeField>::char().as_ref() {
            shake.update(u64::to_le_bytes(*i));
        }
        let mut reader = shake.finalize_xof();

        let bytes = f64::ceil(E::Fr::NUM_BITS as f64 / 8f64) as usize;
        let words = f64::ceil(bytes as f64 / 8f64) as usize;
        let mod_ = E::Fr::NUM_BITS % 8;
        let mask = if mod_ == 0 { 0xFF } else { (1u8 << mod_) - 1 };

        let round_constants: [E::Fr; RC_ROUND_CONSTS_COUNT] = (0..RC_ROUND_CONSTS_COUNT)
            .map(|_| {
                let mut buf = vec![0u8; bytes];
                let mut word_buf = vec![0u64; words];
                let len = buf.len();

                loop {
                    reader.read(&mut buf);
                    buf[len - 1] &= mask;
                    for i in 0..words {
                        let mut byte_array = [0u8; 8];
                        for j in i * 8..std::cmp::min((i + 1) * 8, len) {
                            byte_array[j - i * 8] = buf[j];
                        }
                        word_buf[i] = u64::from_le_bytes(byte_array);
                    }

                    let mut tmp = <E::Fr as PrimeField>::Repr::default();
                    tmp.as_mut().copy_from_slice(&word_buf);
                    let res = E::Fr::from_repr(tmp);

                    if let Ok(el) = res {
                        break el;
                    }
                }
            })
            .collect::<Vec<E::Fr>>()
            .as_slice()
            .try_into()
            .unwrap();

        Ok(ReinforcementConcreteGadget {
            rc_helper_table0,
            rc_helper_table1,
            alphas,
            betas,
            p_prime,
            s_arr,
            u_arr,
            b_arr,
            use_optimized_fifth_power,
            mds_matrix,
            round_constants,
            state: RCState::default(),
            num_squeezed: 0,
        })
    }

    fn apply_5th_power<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        elem: &Num<E>,
    ) -> Result<Num<E>> {
        let res = match elem {
            Num::Constant(constant) => {
                let mut result = *constant;
                result.square();
                result.square();
                result.mul_assign(constant);
                Num::Constant(result)
            }
            Num::Variable(var) => {
                let fifth_power_var = if self.use_optimized_fifth_power {
                    let third = AllocatedNum::alloc(cs, || {
                        let val = *var.get_value().get()?;
                        let mut tmp = val;
                        tmp.square();
                        tmp.mul_assign(&val);
                        Ok(tmp)
                    })?;

                    let fifth = AllocatedNum::alloc(cs, || {
                        let third = *third.get_value().get()?;
                        let val = *var.get_value().get()?;
                        let mut tmp = val;
                        tmp.square();
                        tmp.mul_assign(&third);

                        Ok(tmp)
                    })?;

                    cs.new_single_gate_for_trace_step(
                        &Nonlinearity5CustomGate::default(),
                        &[],
                        &[
                            var.get_variable(),
                            third.get_variable(),
                            fifth.get_variable(),
                        ],
                        &[],
                    )?;

                    fifth
                } else {
                    let squared = AllocatedNum::alloc(cs, || {
                        let mut val = *var.get_value().get()?;
                        val.square();
                        Ok(val)
                    })?;

                    let quad = AllocatedNum::alloc(cs, || {
                        let mut val = *squared.get_value().get()?;
                        val.square();
                        Ok(val)
                    })?;

                    let fifth = AllocatedNum::alloc(cs, || {
                        let mut val = *quad.get_value().get()?;
                        val.mul_assign(var.get_value().get()?);

                        Ok(val)
                    })?;

                    let one = E::Fr::one();
                    let mut minus_one = one;
                    minus_one.negate();

                    cs.new_single_gate_for_trace_step(
                        &Rescue5CustomGate::default(),
                        &[],
                        &[
                            var.get_variable(),
                            squared.get_variable(),
                            quad.get_variable(),
                            fifth.get_variable(),
                        ],
                        &[],
                    )?;

                    fifth
                };

                Num::Variable(fifth_power_var)
            }
        };

        Ok(res)
    }

    // compute y = x^2 + a x + b
    fn compute_quadratic_term<CS>(
        cs: &mut CS,
        x: &Num<E>,
        alpha: &E::Fr,
        beta: &E::Fr,
    ) -> Result<Num<E>>
    where
        CS: ConstraintSystem<E>,
    {
        let res = match x {
            Num::Constant(constant) => {
                let mut x_squared = constant.clone();
                x_squared.square();
                let mut res = *constant;
                res.mul_assign(alpha);
                res.add_assign(beta);
                res.add_assign(&x_squared);
                Num::Constant(res)
            }
            Num::Variable(var) => {
                let quadratic_term =
                    { ArithmeticTerm::from_variable(var.variable).mul_by_variable(var.variable) };
                let linear_term =
                    ArithmeticTerm::from_variable_and_coeff(var.variable, alpha.clone());
                let cnst_term = ArithmeticTerm::constant(beta.clone());

                let res_var = AllocatedNum::alloc(cs, || {
                    let x = var.get_value().grab()?;
                    let mut x_squared = x.clone();
                    x_squared.square();
                    let mut res = x;
                    res.mul_assign(alpha);
                    res.add_assign(beta);
                    res.add_assign(&x_squared);
                    Ok(res)
                })?;
                let res_term = ArithmeticTerm::from_variable(res_var.variable);

                let mut gate = MainGateTerm::new();
                gate.add_assign(quadratic_term);
                gate.add_assign(linear_term);
                gate.add_assign(cnst_term);
                gate.sub_assign(res_term);
                cs.allocate_main_gate(gate)?;

                Num::Variable(res_var)
            }
        };

        Ok(res)
    }

    fn bricks<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<()> {
        // Bricks(x_1, x_2, x_3) = (x_1^5, x_2 * (x_1^2 + a1 * x1 + b1), x_3 * (x_2^2 + a2 * x2 + b2))
        // Bricks is encoded as the following set of constraints:
        // y_1 = x_1 ^ 5 (using custom gate)
        // tmp_1 = x_1^2 + a1 * x1 + b1
        // y_2 = tmp_1 * x_2
        // tmp_2 = x_2^2 + a2 * x2 + b2
        // y_3 = x_3 * tmp_2
        // 5 constraints in total
        let mut new_state = RCState::default();

        // y_1 = x_1 ^ 5 (using custom gate)
        new_state[0] = self.apply_5th_power(cs, &self.state[0])?;
        // tmp_1 = x_1^2 + a1 * x1 + b1
        let tmp_1 =
            Self::compute_quadratic_term(cs, &self.state[0], &self.alphas[0], &self.betas[0])?;
        // y_2 = tmp_1 * x_2
        new_state[1] = tmp_1.mul(cs, &self.state[1])?;
        // tmp_2 = x_2^2 + a2 * x2 + b2
        let tmp_2 =
            Self::compute_quadratic_term(cs, &self.state[1], &self.alphas[1], &self.betas[1])?;
        // y_3 = x_3 * tmp_2
        new_state[2] = tmp_2.mul(cs, &self.state[2])?;

        self.state = new_state;
        Ok(())
    }

    fn concrete<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS, round: usize) -> Result<()> {
        let mut new_state = RCState::default();
        let iter = self
            .mds_matrix
            .iter()
            .zip(self.round_constants[3 * round..3 * (round + 1)].iter())
            .zip(new_state.0.iter_mut());
        for ((row, cnst), out) in iter {
            let mut lc = LinearCombination::zero();
            for (coef, num) in row.iter().zip(self.state.0.iter()) {
                lc.add_assign_number_with_coeff(num, coef.clone());
            }
            lc.add_assign_constant(cnst.clone());
            *out = lc.into_num(cs)?;
        }

        self.state = new_state;
        Ok(())
    }

    fn wrap_fr_by_num<CS>(
        cs: &mut CS,
        val: E::Fr,
        is_const: bool,
        has_value: bool,
    ) -> Result<Num<E>>
    where
        CS: ConstraintSystem<E>,
    {
        let res = if is_const {
            Num::Constant(val)
        } else {
            let var = AllocatedNum::alloc(cs, || {
                if has_value {
                    Ok(val)
                } else {
                    Err(SynthesisError::AssignmentMissing)
                }
            })?;
            Num::Variable(var)
        };

        Ok(res)
    }

    fn wrap_int_by_num<CS>(cs: &mut CS, val: u16, is_const: bool, has_value: bool) -> Result<Num<E>>
    where
        CS: ConstraintSystem<E>,
    {
        let fr = u64_to_ff(val as u64);
        Self::wrap_fr_by_num(cs, fr, is_const, has_value)
    }

    fn decompose<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        num: &Num<E>,
    ) -> Result<DecomposedNum<E>> {
        let is_const = num.is_constant();
        let has_value = num.get_value().is_some();
        let value = num.get_value().unwrap_or(E::Fr::zero());
        let table = self.rc_helper_table1.clone();

        let len = self.s_arr.len();
        let mut in_chunks = Vec::with_capacity(len);
        let mut out_chunks = Vec::with_capacity(len);
        let mut state_trns = Vec::with_capacity(len);
        let mut ge_p_flags = Vec::with_capacity(len);
        let mut x = repr_to_biguint::<E::Fr>(&value.into_repr());

        for (is_first, _is_last, s) in self.s_arr.iter().rev().identify_first_last() {
            let in_chunk = (x.clone() % s).to_u16().unwrap();
            in_chunks.push(in_chunk);
            x = (x - in_chunk) / s;
            let ge_p_flag = (in_chunk >= self.p_prime) as u16 + is_first as u16;
            ge_p_flags.push(Self::wrap_int_by_num(cs, ge_p_flag, is_const, has_value)?);

            let out_chunk = if in_chunk < self.p_prime {
                let keys = [u64_to_ff::<E::Fr>(in_chunk as u64), E::Fr::one()];
                let vals = table.query(&keys[..])?;
                vals[0]
            } else {
                u64_to_ff::<E::Fr>(in_chunk as u64)
            };
            out_chunks.push(Self::wrap_fr_by_num(cs, out_chunk, is_const, has_value)?)
        }
        ge_p_flags.reverse();
        out_chunks.reverse();

        let mut control_flag = true;
        for (chunk, u) in in_chunks.iter().rev().zip(self.u_arr.iter()) {
            //              |-- 0, if chunk = u_i and control_flag = true
            //              |
            //  state_trns =|-- 1, if chunk < u_i
            //              |
            //              |-- 2, if chunk >= u_i and control flag = false
            //
            //  control flag is dropped once we encounter chunk < u_i
            let trn = match (chunk.cmp(u), control_flag) {
                (Ordering::Equal, true) => 0,
                (Ordering::Less, _) => 1,
                (Ordering::Equal, false) | (Ordering::Greater, false) => 2,
                _ => unreachable!(),
            };
            if chunk < u {
                control_flag = false;
            };
            state_trns.push(Self::wrap_int_by_num(cs, trn, is_const, has_value)?);
        }

        let in_chunks: Vec<Num<E>> = in_chunks
            .into_iter()
            .rev()
            .map(|x| Self::wrap_int_by_num(cs, x, is_const, has_value))
            .collect::<Result<Vec<_>>>()?;

        Ok(DecomposedNum {
            in_chunks,
            out_chunks,
            state_trns,
            ge_p_flags,
        })
    }

    // apply rc_table0 to the row [a, b, c, d]
    // alongside with the the following main gate:
    // if !is_final:
    //      d = c * cnst + a
    //  else:
    //      d = (b - 1) * cnst + a = b * cnst - cnst + a
    // return computed d
    fn apply_table0<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        a: &AllocatedNum<E>,
        b: &AllocatedNum<E>,
        c: &AllocatedNum<E>,
        cnst: &E::Fr,
        is_final: bool,
    ) -> Result<AllocatedNum<E>> {
        let table = self.rc_helper_table0.clone();
        let mut minus_one = E::Fr::one();
        minus_one.negate();
        let dummy = AllocatedNum::zero(cs).get_variable();
        let range_of_linear_terms = CS::MainGate::range_of_linear_terms();
        let cnst_term_idx = CS::MainGate::index_for_constant_term();

        let d = match (a.get_value(), b.get_value(), c.get_value()) {
            (Some(a_val), Some(b_val), Some(c_val)) => AllocatedNum::alloc(cs, || {
                let mut res = if is_final {
                    let mut x = b_val;
                    x.sub_assign(&E::Fr::one());
                    x
                } else {
                    c_val
                };
                res.mul_assign(&cnst);
                res.add_assign(&a_val);

                Ok(res)
            })?,
            (_, _, _) => AllocatedNum::alloc(cs, || Err(SynthesisError::AssignmentMissing))?,
        };

        let vars = [
            a.get_variable(),
            b.get_variable(),
            c.get_variable(),
            d.get_variable(),
        ];
        let coeffs = if is_final {
            [E::Fr::one(), cnst.clone(), E::Fr::zero(), minus_one.clone()]
        } else {
            [E::Fr::one(), E::Fr::zero(), cnst.clone(), minus_one.clone()]
        };
        let cnst_term = if is_final {
            let mut x = cnst.clone();
            x.negate();
            x
        } else {
            E::Fr::zero()
        };

        cs.begin_gates_batch_for_step()?;
        cs.apply_single_lookup_gate(&vars[..table.width()], table.clone())?;

        let gate_term = MainGateTerm::new();
        let (_, mut gate_coefs) = CS::MainGate::format_term(gate_term, dummy)?;
        for (idx, coef) in range_of_linear_terms.zip(coeffs.iter()) {
            gate_coefs[idx] = *coef;
        }
        gate_coefs[cnst_term_idx] = cnst_term;

        let mg = CS::MainGate::default();
        cs.new_gate_in_batch(&mg, &gate_coefs, &vars, &[])?;
        cs.end_gates_batch_for_step()?;

        Ok(d)
    }

    // actual implementation is the following:
    // for row of the form [x | signal_seq | f(x) | acc] do: (y = f(x) - notation)
    // enforce table row validity
    // running sum for input: acc_next = acc - coef * x
    // if is_final is set, simply check: acc = coef * x
    // returns updated accumulator
    fn apply_table1_acc<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        x: &AllocatedNum<E>,
        sig_seq: &AllocatedNum<E>,
        y: &AllocatedNum<E>,
        acc: &mut AllocatedNum<E>,
        coef: &E::Fr,
        is_final: bool,
    ) -> Result<()> {
        let new_acc = if !is_final {
            AllocatedNum::alloc(cs, || {
                let mut res = acc.get_value().grab()?;
                let mut tmp = x.get_value().grab()?;
                tmp.mul_assign(coef);
                res.sub_assign(&tmp);
                Ok(res)
            })?
        } else {
            AllocatedNum::zero(cs)
        };

        let mut minus_one = E::Fr::one();
        minus_one.negate();
        let dummy = AllocatedNum::zero(cs).get_variable();
        let table = self.rc_helper_table1.clone();

        let range_of_linear_terms = CS::MainGate::range_of_linear_terms();
        let range_of_next_step_linear_terms = CS::MainGate::range_of_next_step_linear_terms();
        let idx_of_last_linear_term = range_of_next_step_linear_terms
            .last()
            .expect("must have an index");

        // new_acc = prev_acc - base * key
        // or: base * key + new_acc - prev_acc = 0;
        let vars = [
            x.get_variable(),
            sig_seq.get_variable(),
            y.get_variable(),
            acc.get_variable(),
        ];
        let coeffs = [coef.clone(), E::Fr::zero(), E::Fr::zero(), minus_one];

        cs.begin_gates_batch_for_step()?;
        cs.apply_single_lookup_gate(&vars[..table.width()], table.clone())?;

        let gate_term = MainGateTerm::new();
        let (_, mut gate_coefs) = CS::MainGate::format_term(gate_term, dummy)?;

        for (idx, coef) in range_of_linear_terms.zip(coeffs.iter()) {
            gate_coefs[idx] = *coef;
        }
        if !is_final {
            gate_coefs[idx_of_last_linear_term] = E::Fr::one();
        }

        let mg = CS::MainGate::default();
        cs.new_gate_in_batch(&mg, &gate_coefs, &vars, &[])?;

        cs.end_gates_batch_for_step()?;

        *acc = new_acc;
        Ok(())
    }

    fn bars<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<()> {
        let mut new_state = RCState::default();
        let len = self.s_arr.len();

        for (in_elem, out_elem) in self.state.0.iter().cloned().zip(new_state.0.iter_mut()) {
            let decomposed_num = self.decompose(cs, &in_elem)?;
            if !in_elem.is_constant() {
                // apply all tables invocations for all indexes i (except the last one):
                // [trn_i, trn_(i+1), z_i, siq_seq_i], alongside with additional gate:
                // sig_seq_i = z_i * DIGIT_SEP * (i+1) + trn_i, where DIGIT_SEP * (i+1) is a constant
                // the last row is however of the form:
                // [trn_n, z_n, trn_0, sig_seq_n] with additional gate being:
                // sig_seq_n = (z_n - 1) * DIGIT_SEP * (n+1) + trn_n
                // by modifying the last row we achieve the following goal:
                // we need to check trn_0 is either 0 or 1, which is done by placing trn_0 into the third row
                // if trn_n = 1 or 2, then z_n is 1 or 2, hence z_n' is 0 or 1
                // if trn_n = 0, then the only valid option for z_n is 1 which in agreement with the logic:
                // trn_n = 0 => in_chunk_n == u_n => chunk_n > p_prime => z_n = 1
                let mut signal_sequence = Vec::with_capacity(len);
                let mut idx = 0;
                let iter = {
                    decomposed_num
                        .state_trns
                        .windows(2)
                        .zip(decomposed_num.ge_p_flags.iter())
                };
                for (window, z) in iter {
                    idx += 1;
                    let trn = window[0].get_variable();
                    let trn_next = window[1].get_variable();
                    let cnst = u64_to_ff::<E::Fr>((DIGIT_SEP * idx) as u64);
                    let signal =
                        self.apply_table0(cs, &trn, &trn_next, &z.get_variable(), &cnst, false)?;
                    signal_sequence.push(signal);
                }

                // deal with the last row
                // [trn_n, z_n, trn_0, sig_seq_n] with additional gate being:
                // sig_seq_n = (z_n - 1) * DIGIT_SEP * (n+1) + trn_n
                idx += 1;
                let last_trn = decomposed_num.state_trns.last().unwrap().get_variable();
                let first_trn = decomposed_num.state_trns.first().unwrap().get_variable();
                let z = decomposed_num.ge_p_flags.last().unwrap().get_variable();
                let cnst = u64_to_ff::<E::Fr>((DIGIT_SEP * idx) as u64);
                let signal = self.apply_table0(cs, &last_trn, &z, &first_trn, &cnst, true)?;
                signal_sequence.push(signal);

                let mut acc = in_elem.get_variable();
                let iter = itertools::multizip((
                    &decomposed_num.in_chunks,
                    &decomposed_num.out_chunks,
                    &signal_sequence,
                    &self.b_arr,
                ))
                .identify_first_last();

                for (_is_first, is_last, (in_chunk, out_chunk, sig_seq, coef)) in iter {
                    self.apply_table1_acc(
                        cs,
                        &in_chunk.get_variable(),
                        &sig_seq,
                        &out_chunk.get_variable(),
                        &mut acc,
                        &coef,
                        is_last,
                    )?;
                }
            }

            *out_elem = Num::lc(cs, &self.b_arr[..], &decomposed_num.out_chunks[..])?;
        }

        self.state = new_state;
        Ok(())
    }

    fn sponge_permutation<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<()> {
        self.num_squeezed = 0;

        // first concrete
        self.concrete(cs, 0)?;
        // first rounds
        for i in 1..=RC_PRE_ROUNDS_COUNT {
            self.bricks(cs)?;
            self.concrete(cs, i)?;
        }
        // bar round
        self.bars(cs)?;
        self.concrete(cs, RC_PRE_ROUNDS_COUNT + 1)?;
        // final rounds
        for i in RC_PRE_ROUNDS_COUNT + 2..=RC_TOTAL_ROUNDS_COUNT {
            self.bricks(cs)?;
            self.concrete(cs, i)?;
        }

        Ok(())
    }

    pub fn reset(&mut self, state: Option<&[Num<E>]>) {
        self.state = state
            .map(|raw_state| RCState::from_raw(raw_state))
            .unwrap_or(RCState::default());
        self.num_squeezed = 0;
    }

    pub fn squeeze<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<Num<E>> {
        if self.num_squeezed >= RC_RATE {
            self.sponge_permutation(cs)?;
        }
        let res = self.state[self.num_squeezed].clone();
        self.num_squeezed += 1;

        Ok(res)
    }

    pub fn absorb<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        elems_to_absorb: &[Num<E>],
    ) -> Result<()> {
        assert!(elems_to_absorb.len() <= RC_RATE);
        for (state, elem_to_absorb) in self.state.0.iter_mut().zip(elems_to_absorb.iter()) {
            *state = state.add(cs, elem_to_absorb)?;
        }
        self.sponge_permutation(cs)
    }

    pub fn get_cur_state(&self) -> [Num<E>; RC_STATE_WIDTH] {
        self.state.0.clone()
    }
}
