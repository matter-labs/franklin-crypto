use crate::plonk::better_better_cs::cs::*;
use crate::plonk::better_better_cs::lookup_tables::*;
use crate::plonk::better_better_cs::utils;
use crate::pairing::ff::*;
use crate::pairing::ff::{PrimeField, PrimeFieldRepr};
use crate::SynthesisError;
use crate::Engine;
use crate::plonk::better_better_cs::gadgets::num::{
    AllocatedNum,
    Num,
};

use super::tables::*;
use super::utils::*;
use crate::plonk::better_better_cs::gadgets::assignment::{
    Assignment
};
use std::sync::Arc;
use splitmut::SplitMut;
use std::{ iter, mem };
use std::collections::HashMap;
use std::cell::RefCell;

type Result<T> = std::result::Result<T, SynthesisError>;

const CHUNK_SIZE : usize = 8; 
const REG_WIDTH : usize = 32;
const SHIFT4 : usize = 4;
const SHIFT7 : usize = 7; 
const BLAKE2s_STATE_WIDTH : usize = 16;
const CS_WIDTH : usize = 4;


#[derive(Clone)]
pub struct DecomposedNum<E : Engine> {
    pub r0: Num<E>,
    pub r1: Num<E>,
    pub r2: Num<E>,
    pub r3: Num<E>,
}

impl<E: Engine> Default for DecomposedNum<E> {
    fn default() -> Self {
        DecomposedNum {
            r0: Num::default(), 
            r1: Num::default(), 
            r2: Num::default(), 
            r3: Num::default(),
        }
    }
}

impl<E: Engine> DecomposedNum<E> {
    pub fn get_var_by_idx(&self, idx: usize) -> &Num<E> {
        let res = match idx {
            0 => &self.r0,
            1 => &self.r1,
            2 => &self.r2,
            3 => &self.r3,
            _ => unreachable!(),
        };
        res
    }
}

#[derive(Clone)]
pub struct Reg<E: Engine> {
    full: Num<E>,
    decomposed: DecomposedNum<E>,
}

impl<E: Engine> Default for Reg<E> {
    fn default() -> Self {
        Reg {
            full : Num::default(),
            decomposed: DecomposedNum::default(),
        }
    }
}

impl<E: Engine> Reg<E> {
    pub fn is_const(&self) -> bool {
        self.full.is_constant()
    }

    pub fn get_value(&self) -> Option<E::Fr> {
        self.full.get_value()
    }
}


#[derive(Clone, Default)]
pub struct HashState<E: Engine>(Vec<Reg<E>>);


#[derive(Copy, Clone)]
pub enum VarTracker {
    NotAssigned,
    Variable,
    Constant,
}

// the purpose of this (and the following) struct is explained in the comments of the main text
// all linear variables are represented in the form (bool, coef, var)
// where the boolean flag asserts that variable was actually assigned a value (for self-test and debugging assistance)
#[derive(Clone)]
pub struct GateVarHelper<E: Engine>{
    assigned: VarTracker,
    coef: E::Fr,
    val: AllocatedNum<E>,
}

impl<E: Engine> Default for GateVarHelper<E> {
    fn default() -> Self {
        GateVarHelper {
            assigned: VarTracker::NotAssigned,
            coef: E::Fr::zero(),
            val: AllocatedNum::default(),
        }
    }
}

#[derive(Clone)]
pub struct GateAllocHelper<E: Engine> {
    // [a, b, c, d]
    vars: [GateVarHelper<E>; CS_WIDTH],

    cnst_sel: E::Fr,
    d_next_sel: E::Fr,
    table: Option<Arc<LookupTableApplication<E>>>  
}

impl<E: Engine> Default for GateAllocHelper<E> {
    fn default() -> Self {
        GateAllocHelper {
            vars: <[GateVarHelper<E>; CS_WIDTH]>::default(),
            cnst_sel: E::Fr::zero(),
            d_next_sel: E::Fr::zero(),
            table: None, 
        }
    }
}

impl<E: Engine> GateAllocHelper<E> {
    // force variable - checks that the variable is indeed AllocatedVar and not constant
    pub fn set_var(&mut self, idx: usize, coef: E::Fr, input: Num<E>, force_allocated: bool) -> Result<()>
    {
        assert!(idx < CS_WIDTH);
        if force_allocated && input.is_constant() {
            return Err(SynthesisError::UnexpectedIdentity);
        }

        match input {
            Num::Constant(fr) => {
                self.vars[idx].assigned = VarTracker::Constant;
                let mut tmp = fr;
                tmp.mul_assign(&coef);
                self.cnst_sel.add_assign(&tmp);
            }
            Num::Allocated(var) => {
                self.vars[idx].assigned = VarTracker::Variable;
                self.vars[idx].coef = coef;
                self.vars[idx].val = var;
            }
        }

        Ok(())
    }

    pub fn set_table(&mut self, table: Arc<LookupTableApplication<E>>) {
        self.table = Some(table)
    }

    pub fn is_prepared(&self) -> bool {
        for i in 0..CS_WIDTH {
            if let VarTracker::NotAssigned = self.vars[i].assigned {
                return false;
            }
        }
        return true;
    }

    pub fn link_with_next_row(&mut self, coef: E::Fr) {
        self.d_next_sel = coef;
    }

    pub fn new() -> Self {
        GateAllocHelper::default()
    }

    pub fn set_cnst_sel(&mut self, fr: E::Fr) {
        self.cnst_sel = fr;
    }
}


// for explanations have a llok in main text 
// let the third column (results of corresponding xors be: q0, q1, q2, q3)
// returns (z, [q0, q1, q2, q3], Option(w0, w1, w2))
#[derive(Clone)]
pub struct XorRotOutput<E: Engine> {
    pub z: Reg<E>,
    pub q_arr : Option<[Num<E>; 4]>,
    pub w_arr: Option<[Num<E>; 3]>,
    pub shifts: [usize; 4],
}


pub struct OptimizedBlake2sGadget<E: Engine> {
    xor_table: Arc<LookupTableApplication<E>>,
    xor_rotate4_table: Arc<LookupTableApplication<E>>,
    xor_rotate7_table: Arc<LookupTableApplication<E>>,
    
    iv: [u64; 8],
    iv0_twist: u64,
    sigmas : [[usize; 16]; 10],

    declared_cnsts: RefCell<HashMap<E::Fr, AllocatedNum<E>>>,
    allocated_cnsts : RefCell<HashMap<E::Fr, AllocatedNum<E>>>,
}

impl<E: Engine> OptimizedBlake2sGadget<E> {

    fn u64_to_ff(&self, n: u64) -> E::Fr {
        let mut repr : <E::Fr as PrimeField>::Repr = E::Fr::zero().into_repr();
        repr.as_mut()[0] = n;
        let res = E::Fr::from_repr(repr).expect("should parse");
        res
    }

    fn u64_to_reg(&self, n: u64) -> Reg<E> {
        let full = Num::Constant(self.u64_to_ff(n));
        let r0 = Num::Constant(self.u64_to_ff(n & 0xff));
        let r1 = Num::Constant(self.u64_to_ff((n >> CHUNK_SIZE) & 0xff));
        let r2 = Num::Constant(self.u64_to_ff((n >> (2 * CHUNK_SIZE)) & 0xff));
        let r3 = Num::Constant(self.u64_to_ff((n >> (3 * CHUNK_SIZE)) & 0xff));

        Reg {
            full, 
            decomposed: DecomposedNum { r0, r1, r2, r3}
        }
    }

    fn alloc_num_from_u64<CS: ConstraintSystem<E>>(&self, cs: &mut CS, n: Option<u64>) -> Result<Num<E>> {
        let val = n.map(|num| { self.u64_to_ff(num) });
        let new_var = AllocatedNum::alloc(cs, || {val.grab()})?;
        Ok(Num::Allocated(new_var))
    }

    fn alloc_reg_from_u64<CS: ConstraintSystem<E>>(&self, cs: &mut CS, n: Option<u64>) -> Result<Reg<E>> {
        let full_val = n.map(|num| { self.u64_to_ff(num) });
        let full = Num::Allocated(AllocatedNum::alloc(cs, || {full_val.grab()})?);
        
        let r0_val = n.map(|num| { self.u64_to_ff(num & 0xff) });
        let r0 = Num::Allocated(AllocatedNum::alloc(cs, || {r0_val.grab()})?);

        let r1_val = n.map(|num| { self.u64_to_ff((num >> CHUNK_SIZE) & 0xff) });
        let r1 = Num::Allocated(AllocatedNum::alloc(cs, || {r1_val.grab()})?);

        let r2_val = n.map(|num| { self.u64_to_ff((num >> (2 * CHUNK_SIZE)) & 0xff) });
        let r2 = Num::Allocated(AllocatedNum::alloc(cs, || {r2_val.grab()})?);

        let r3_val = n.map(|num| { self.u64_to_ff((num >> (3 * CHUNK_SIZE)) & 0xff) });
        let r3 = Num::Allocated(AllocatedNum::alloc(cs, || {r3_val.grab()})?);

        let res = Reg {
            full, 
            decomposed: DecomposedNum { r0, r1, r2, r3}
        };
        Ok(res)
    }

    fn unwrap_allocated(&self, num: &Num<E>) -> AllocatedNum<E> {
        match num {
            Num::Allocated(var) => var.clone(),
            _ => panic!("should be allocated"),
        }
    }
   
    pub fn new<CS: ConstraintSystem<E>>(cs: &mut CS) -> Result<Self> {
        let columns3 = vec![
            PolyIdentifier::VariablesPolynomial(0), 
            PolyIdentifier::VariablesPolynomial(1), 
            PolyIdentifier::VariablesPolynomial(2)
        ];

        let name1: &'static str = "xor_table";
        let xor_table = LookupTableApplication::new(
            name1,
            XorTable::new(CHUNK_SIZE, name1),
            columns3.clone(),
            true
        );

        let name2 : &'static str = "xor_rotate4_table";
        let xor_rotate4_table = LookupTableApplication::new(
            name2,
            XorRotateTable::new(CHUNK_SIZE, SHIFT4, name2),
            columns3.clone(),
            true
        );

        let name3 : &'static str = "xor_rotate7_table";
        let xor_rotate7_table = LookupTableApplication::new(
            name3,
            XorRotateTable::new(CHUNK_SIZE, SHIFT7, name3),
            columns3.clone(),
            true
        );

        let xor_table = cs.add_table(xor_table)?;
        let xor_rotate4_table = cs.add_table(xor_rotate4_table)?;
        let xor_rotate7_table = cs.add_table(xor_rotate7_table)?;

        let iv = [
            0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
            0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19,
        ];
        let iv0_twist =  0x6A09E667 ^ 0x01010000 ^ 32;

        let sigmas: [[usize; 16]; 10] = [
            [ 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15 ],
            [ 14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3 ],
            [ 11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4 ],
            [ 7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8 ],
            [ 9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13 ],
            [ 2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9 ],
            [ 12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11 ],
            [ 13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10 ],
            [ 6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5 ],
            [ 10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0 ]
        ];

        let declared_cnsts = RefCell::new(HashMap::new());
        let allocated_cnsts = RefCell::new(HashMap::new());

        Ok(OptimizedBlake2sGadget {
            xor_table,
            xor_rotate4_table,
            xor_rotate7_table,

            iv,
            iv0_twist,
            sigmas,

            declared_cnsts,
            allocated_cnsts,
        })
    }

    // the trick, we are going to use is the following:
    // we may handle two range checks (for overflow flags of0 and of1) simultaneously, using only one table access
    // more precisely we form the row of variables: [of0, of1, of0 ^ of1, ph],
    // where ph - is a placeholder variable, which is not used on current row, but may be connected to previous row
    // via usage of d_next selector
    fn allocate_gate<CS: ConstraintSystem<E>>(&self, cs: &mut CS, gate_alloc_helper: GateAllocHelper<E>) -> Result<()> {
        // first check if all variables are actually allocated
        assert!(gate_alloc_helper.is_prepared());

        let range_of_linear_terms = CS::MainGate::range_of_linear_terms();
        let dummy = AllocatedNum::alloc_zero(cs)?.get_variable();
        let gate_term = MainGateTerm::new();
        let (mut vars, mut coefs) = CS::MainGate::format_term(gate_term, dummy)?;

        // plug-in all linear terms
        for (pos, idx) in range_of_linear_terms.zip(0..CS_WIDTH) {
            if let VarTracker::Variable = gate_alloc_helper.vars[idx].assigned {
                vars[idx] = gate_alloc_helper.vars[idx].val.get_variable();
                coefs[pos] = gate_alloc_helper.vars[idx].coef;
            }
        }

        // plug-in constant term if necessary
        if !gate_alloc_helper.cnst_sel.is_zero() {
            let cnst_index = CS::MainGate::index_for_constant_term();
            coefs[cnst_index] = gate_alloc_helper.cnst_sel;
        }

        // plug-in d_next if required
        if !gate_alloc_helper.d_next_sel.is_zero() {
            let range_of_next_step_linear_terms = CS::MainGate::range_of_next_step_linear_terms();
            let idx_of_last_linear_term = range_of_next_step_linear_terms.last().expect("must have an index");
            coefs[idx_of_last_linear_term] = gate_alloc_helper.d_next_sel;
        }

        cs.begin_gates_batch_for_step()?;
        
        // apply table lookup if we have one
        if let Some(table) = gate_alloc_helper.table {
            cs.apply_single_lookup_gate(&vars[..table.width()], table.clone())?;
        }

        // apply main gate        
        let mg = CS::MainGate::default();
        cs.new_gate_in_batch(&mg, &coefs, &vars, &[])?;
        cs.end_gates_batch_for_step()?;
        
        Ok(())
    }

    fn xor_rot<CS>(&self, cs: &mut CS, a: &Num<E>, b: &Num<E>, rot: usize) -> Result<AllocatedNum<E>>
    where CS: ConstraintSystem<E>
    {
        AllocatedNum::alloc(cs, || {
            let a = a.get_value().grab()?;
            let b = b.get_value().grab()?;

            let a_repr = a.into_repr();
            let b_repr = b.into_repr();
            let a_int = a_repr.as_ref()[0];
            let b_int = b_repr.as_ref()[0];
            let a_xor_b = a_int ^ b_int;
            let res = (a_xor_b >> rot) | ((a_xor_b << (REG_WIDTH - rot)) & ((1 << REG_WIDTH) - 1));
            Ok(self.u64_to_ff(res))
        })
    }

    fn xor<CS: ConstraintSystem<E>>(&self, cs: &mut CS, a: &Num<E>, b: &Num<E>) -> Result<AllocatedNum<E>>
    {
        self.xor_rot(cs, a, b, 0)
    }

    fn constraint_all_allocated_cnsts<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<()> {
        let mut allocated_cnsts_dict = self.allocated_cnsts.borrow_mut(); 
        for (fr, variable) in self.declared_cnsts.borrow_mut().drain() {
            let self_term = ArithmeticTerm::from_variable(variable.get_variable());
            let other_term = ArithmeticTerm::constant(fr.clone());
        
            let mut term = MainGateTerm::new();
            term.add_assign(self_term);
            term.sub_assign(other_term);
            cs.allocate_main_gate(term)?;

            allocated_cnsts_dict.insert(fr, variable);
        }

        Ok(())
    }

    fn to_allocated<CS: ConstraintSystem<E>>(&self, cs: &mut CS, input: &Num<E>) -> Result<Num<E>> {
        let res = match input {
            Num::Allocated(_) => input.clone(),
            Num::Constant(fr) => {
                if fr.is_zero() {
                    Num::Allocated(AllocatedNum::alloc_zero(cs)?)
                }
                else {
                    let allocated_map = self.allocated_cnsts.borrow();
                    let mut declared_map = self.declared_cnsts.borrow_mut();

                    let var = match allocated_map.get(&fr) {
                        Some(entry) => entry.clone(),
                        None => {
                            let var = declared_map.entry(*fr).or_insert_with(|| { 
                                AllocatedNum::alloc(cs, || Ok(*fr)).expect("should allocate")
                            });
                            var.clone()
                        },
                    };
                    Num::Allocated(var)
                }
            },
        };

        Ok(res)
    }

    fn choose_table_by_rot(&self, rot: usize) -> Arc<LookupTableApplication<E>> {
        let table = match rot {
            8 | 16 => self.xor_table.clone(),
            12 => self.xor_rotate4_table.clone(),
            7 => self.xor_rotate7_table.clone(),
            _ => unreachable!(),
        };

        table
    }

    // first step of G function is handling equations of the form :
    // y = a + b + x (e.g. v[a] = v[a] + v[b] + x),
    // where a, b are available in both full and decomposed forms (in other words, are of type Reg)
    // and x is available only in full form (in other words, x is just a regular Num)
    // we want the result y to be represented in both full and decomposed forms

    // there are special cases which we want to handle separately:
    // 1) all of a, b, x - are constants: than there is actually nothing interesting,
    // no constraints will be allocated, just return the new constant (NB: what if t will be a variable)

    // 2) all of a, b, x are variables: there will be 3 rows:
    // [y0, y1, y2, y3] - decomposed parts of resulted y: y = y0 + 2^8 * y1 + 2^16 * y2 + 2^24 * y3: 
    // [a, b, x, y] - where y = a + b + x - 2^32 * of (using of via d_next selector)
    // [of, t, of ^ t, of] - range check for of and t

    // 3) if we are in between these two corner cases we are going to use the sceme as in case (2), the only difference is that
    // we are going to replace all instances of costant variables with dummy placeholders and push them instead into constant selector
    // e.g: assume thta a - is variable (AllocatedVar) and b, x - are constants : than in any case y, of, y0, y1, y2, y3 -a re variables
    // and the second row will be replaced by: 
    // [a, dummy, dummy, y], and constant selector will contain the value of x + y
    // this identical approach to handling constant and variables is hidden under the GateAllocHelper facade
    
    // NB: there is inversion in computation: we first precompute the value of y and split it into corresponding
    // chunks y0, y1, y2, y3 BEFORE allocating contraint defining y itself! this inversion will be a recurring pattern 
    // in our optimization
    // also - there is a place for additional 8-bit variable t on the last row, so there is a possibility to multiplex two
    // oveflow checks on the same row: for current of and (yet unknown) t
    // and yes, we are going to explot the inversion trick again: we take t from overflow check of step 3!

    // due to such an extended use of inversion trick we have to split all equation generations it two phases: 
    // setup - where we aforehead define all variables and compute their values
    // and actual gate allocation

    // setup of first step: given a, b, x - return [y, of] (in that order)
    fn g_ternary_additon_setup<CS>(&self, cs: &mut CS, a: &Reg<E>, b: &Reg<E>, x: &Num<E>) -> Result<(Reg<E>, Num<E>)>
    where CS: ConstraintSystem<E> 
    {
        let (y, of) = match (&a.full, &b.full, &x) {
            (Num::Constant(fr1), Num::Constant(fr2), Num::Constant(fr3)) => {
                let mut temp = fr1.clone();
                temp.add_assign(&fr2);
                temp.add_assign(&fr3);
                let f_repr = temp.into_repr();
                let y = f_repr.as_ref()[0] & ((1 << REG_WIDTH) - 1);
                (self.u64_to_reg(y), Num::default())
            },
            (_, _, _) => {
                let fr1 = a.get_value();
                let fr2 = b.get_value();
                let fr3 = x.get_value();
                let (y_val, of_val) = match (fr1, fr2, fr3) {
                    (Some(fr1), Some(fr2), Some(fr3)) => {
                        let mut temp = fr1.clone();
                        temp.add_assign(&fr2);
                        temp.add_assign(&fr3);
                        let f_repr = temp.into_repr();
                        let y = f_repr.as_ref()[0] & ((1 << REG_WIDTH) - 1);
                        let of = f_repr.as_ref()[0] >> REG_WIDTH;
                        (Some(y), Some(of))
                    },
                    (_, _, _) => (None, None)
                };
                
                let y = self.alloc_reg_from_u64(cs, y_val)?;
                let of = self.alloc_num_from_u64(cs, of_val)?;
                (y, of)
            },
        };
        Ok((y, of))
    }

    fn g_ternary_addition_process<CS: ConstraintSystem<E>>(
        &self, cs: &mut CS, 
        a: &Reg<E>, b: &Reg<E>, x: &Num<E>, // known in advance 
        y: &Reg<E>, of: &Num<E>, t: &Num<E>, // generated during setup phase
    ) -> Result<()>
    {
        if a.is_const() && b.is_const() && x.is_constant() {
            assert!(t.is_constant());
            return Ok(())
        }

        let zero = E::Fr::zero();
        let one = E::Fr::one();
        let mut minus_one = one.clone();
        minus_one.negate();

        // [y0, y1, y2, y3] - decomposed parts of resulted y: y = y0 + 2^8 * y1 + 2^16 * y2 + 2^24 * y3: 
        // [a, b, x, y] - where y = a + b + x - 2^32 * of (using of via d_next selector)
        // [of, t, of ^ t, of] - range check for of and t

        let mut first_row = GateAllocHelper::default();
        first_row.set_var(0, one.clone(), y.decomposed.r0.clone(), true)?;
        first_row.set_var(1, self.u64_to_ff(1 << CHUNK_SIZE), y.decomposed.r1.clone(), true)?;
        first_row.set_var(2, self.u64_to_ff(1 << (2 * CHUNK_SIZE)), y.decomposed.r2.clone(), true)?;
        first_row.set_var(3, self.u64_to_ff(1 << (3 * CHUNK_SIZE)), y.decomposed.r3.clone(), true)?;
        first_row.link_with_next_row(minus_one.clone());

        let mut second_row = GateAllocHelper::default();
        second_row.set_var(0, one.clone(), a.full.clone(), false)?;
        second_row.set_var(1, one.clone(), b.full.clone(), false)?;
        second_row.set_var(2, one.clone(), x.clone(), false)?;
        second_row.set_var(3, minus_one.clone(), y.full.clone(), true)?;
        let mut coef = self.u64_to_ff(1 << REG_WIDTH);
        coef.negate();
        second_row.link_with_next_row(coef);

        let mut third_row = GateAllocHelper::default();
        third_row.set_var(0, zero.clone(), of.clone(), true)?;

        // NB: t is always a variable even when it is actually a constant!
        // in this case t is simply a constant zero: map in into dummy variable instead!
        let (b, c) = match t {
            Num::Constant(fr) => {
                assert!(fr.is_zero());
                (Num::Allocated(AllocatedNum::alloc_zero(cs)?), of.clone())
            }
            Num::Allocated(_) => {
                let tmp = self.xor(cs, &of, t)?;
                (t.clone(), Num::Allocated(tmp))
            }
        };

        third_row.set_var(1, zero.clone(), b, true)?;
        third_row.set_var(2, zero.clone(), c, true)?;
        third_row.set_var(3, zero.clone(), of.clone(), true)?;
        third_row.set_table(self.xor_table.clone());

        self.allocate_gate(cs, first_row)?;
        self.allocate_gate(cs, second_row)?;
        self.allocate_gate(cs, third_row)?;

        Ok(())
    }

    // third of G function is handling equations of the form :
    // y = a + b (e.g. v[c] = v[c] + v[d]),
    // where a, b are available in both full and decomposed forms (in other words, are of type Reg)
    // we want the result y to be represented in both full and decomposed forms

    // when a, b are varibles we have only one equation of the form:
    // [y, a, b, of], y = a + b - 2^32 * of
    // and range check of of is multiplexed with range check for ternary addition (here where t there comes from!)
    fn g_binary_addition_setup<CS>(&self, cs: &mut CS, a: &Reg<E>, b: &Reg<E>) -> Result<(Reg<E>, Num<E>)> 
    where CS: ConstraintSystem<E>
    {
        let (y, of) = match (&a.full, &b.full) {
            (Num::Constant(fr1), Num::Constant(fr2)) => {
                let mut temp = fr1.clone();
                temp.add_assign(&fr2);
                let f_repr = temp.into_repr();
                let y = f_repr.as_ref()[0] & ((1 << REG_WIDTH) - 1);
                (self.u64_to_reg(y), Num::default())
            },
            (_, _) => {
                let fr1 = a.get_value();
                let fr2 = b.get_value();
                let (y_val, of_val) = match (fr1, fr2) {
                    (Some(fr1), Some(fr2)) => {
                        let mut temp = fr1.clone();
                        temp.add_assign(&fr2);
                        let f_repr = temp.into_repr();
                        let y = f_repr.as_ref()[0] & ((1 << REG_WIDTH) - 1);
                        let of = f_repr.as_ref()[0] >> REG_WIDTH;
                        (Some(y), Some(of))
                    },
                    (_, _) => (None, None)
                };
                
                let y = self.alloc_reg_from_u64(cs, y_val)?;
                let of = self.alloc_num_from_u64(cs, of_val)?;
                (y, of)
            },
        };
        Ok((y, of))
    }

    fn g_binary_addition_process<CS>(&self, cs: &mut CS, a: &Reg<E>, b: &Reg<E>, y: &Reg<E>, of: &Num<E>) -> Result<()>
    where CS: ConstraintSystem<E>
    {
        if a.is_const() && b.is_const() {
            return Ok(())
        }

        // [y, a, b, of], y = a + b - 2^32 * of
        // y + 2^32 * of - a - b = 0;

        let one = E::Fr::one();
        let mut minus_one = one.clone();
        minus_one.negate();

        let mut row = GateAllocHelper::default();
        row.set_var(0, one.clone(), y.full.clone(), true)?;
        row.set_var(1, minus_one.clone(), a.full.clone(), false)?;
        row.set_var(2, minus_one.clone(), b.full.clone(), false)?;
        row.set_var(3, self.u64_to_ff(1 << REG_WIDTH), of.clone(), true)?;
        
        self.allocate_gate(cs, row)?;
        Ok(())
    }  

    // rotate step is of the form: z = (x ^ y) >>> R
    // we will always have the following 4 rows (in case any of (x, y) is actually a variable)
    // z = /sum z[idx_k] * 8^[idx_k] ([idx_k] is permuted array of [0, 1, 2, 3])
    // x[0], y[0], z[idx_0], z,
    // [x[1], y[1], z[idx_1], z - z[idx_0] * 8^[idx_0] = w0
    // x[2], y[2], z[idx_2], z - z[idx_0] * 8^[idx_0] - z[idx_1] * 8^[idx_1] = w1
    // x[3], y[3], z[idx_3], z - z[idx_0] * 8^[idx_0] - z[idx_1] * 8^[idx_1] - z[idx_2] * 8^[idx_2] = w2
    
    // on the first 3 rows we have the link to the next row via d_next
    // on the last row we need only to check that c * 8^[idx_3] = d

    // when R is a multiple of CHUNK_LEN = 8 ( R is 8 or 16) z is already decomposed into chunks 
    // (just take [z_idx] in the right order), so no additional decomposition constraints are needed
    // in other case we prepend previous constraints with decomposition of z into z[0], z[1], z[2], z[3]
    // so that the first row will be: 
    // z[0], z[1], z[2], z[3]
    // the boolean flag needs_recomposition is responsible for this

    // let the third column (results of corresponding xors be: q0, q1, q2, q3)
    // returns (z, [q0, q1, q2, q3], Option(w0, w1, w2))
    fn g_xor_rot_setup<CS>(&self, cs: &mut CS, a: &Reg<E>, b: &Reg<E>, rot: usize) -> Result<XorRotOutput<E>>
    where CS: ConstraintSystem<E>
    {
        let res = match (&a.full, &b.full) {
            (Num::Constant(fr1), Num::Constant(fr2)) => {
                let n = fr1.into_repr().as_ref()[0];
                let m = fr2.into_repr().as_ref()[0];
                let n_xor_m = n ^ m;
                let tmp = (n_xor_m >> rot) | (((n_xor_m) << (REG_WIDTH - rot)) & ((1 << REG_WIDTH) - 1));
                
                XorRotOutput {
                    z: self.u64_to_reg(tmp),
                    q_arr: None,
                    w_arr: None,
                    shifts: [0, 0, 0, 0],
                }
            },
            (_, _) => {
                let q0 = Num::Allocated(self.xor_rot(cs, &a.decomposed.r0, &b.decomposed.r0, rot)?);
                let q1 = Num::Allocated(self.xor(cs, &a.decomposed.r1, &b.decomposed.r1)?);
                let q2 = Num::Allocated(self.xor(cs, &a.decomposed.r2, &b.decomposed.r2)?);
                let q3 = Num::Allocated(self.xor(cs, &a.decomposed.r3, &b.decomposed.r3)?);               

                let fr1 = a.get_value();
                let fr2 = b.get_value();
                let y_val = match (fr1, fr2) {
                    (Some(fr1), Some(fr2)) => {
                        let n = fr1.into_repr().as_ref()[0];
                        let m = fr2.into_repr().as_ref()[0];
                        let n_xor_m = n ^ m;
                        let res = (n_xor_m >> rot) | (((n_xor_m) << (REG_WIDTH - rot)) & ((1 << REG_WIDTH) - 1));
                        Some(res)
                    },
                    (_, _) => None,
                };

                let (y, shifts) = match rot {
                    7 => (self.alloc_reg_from_u64(cs, y_val)?, [0, 1, 9, 17]),
                    12 => (self.alloc_reg_from_u64(cs, y_val)?, [20, 0, 4, 12]),
                    8 => {
                        let full = self.alloc_num_from_u64(cs, y_val)?;
                        let reg = Reg {
                            full,
                            decomposed : DecomposedNum { r0: q1.clone(), r1: q2.clone(), r2: q3.clone(), r3: q0.clone() }
                        };
                        (reg, [24, 0, 8, 16])
                    },
                    16 => {
                        let full = self.alloc_num_from_u64(cs, y_val)?;
                        let reg = Reg {
                            full,
                            decomposed : DecomposedNum { r0: q2.clone(), r1: q3.clone(), r2: q0.clone(), r3: q1.clone() }
                        };
                        (reg, [16, 24, 0, 8])
                    },
                    _ => unreachable!(),
                };

                let mut w_arr = <[Num<E>; 3]>::default();
                let q_arr = [q0, q1, q2, q3];
                let mut cur = &y.full;
                for ((w, q), shift) in w_arr.iter_mut().zip(q_arr.iter()).zip(shifts.iter()) {
                    // w = cur - (1 << shift) * q
                    let new_var = AllocatedNum::alloc(cs, || {
                        let mut cur_val = cur.get_value().grab()?;
                        let coef = self.u64_to_ff(1 << shift);
                        let mut q_val = q.get_value().grab()?;
                        q_val.mul_assign(&coef);
                        cur_val.sub_assign(&q_val);
                        
                        Ok(cur_val)
                    })?;
                    
                    *w = Num::Allocated(new_var);
                    cur = w;
                }
                 
                XorRotOutput {
                    z: y,
                    q_arr: Some(q_arr),
                    w_arr: Some(w_arr),
                    shifts
                }
            },
        };

        Ok(res)
    }

    fn g_xor_rot_process<CS>(&self, cs: &mut CS, x: &Reg<E>, y: &Reg<E>, xor_rot_data: XorRotOutput<E>, rot: usize) -> Result<()>
    where CS: ConstraintSystem<E>
    {
        if x.is_const() && y.is_const() {
            return Ok(())
        }

        let zero = E::Fr::zero();
        let one = E::Fr::one();
        let mut minus_one = one.clone();
        minus_one.negate();

        let z = xor_rot_data.z;
        let q_arr = xor_rot_data.q_arr.unwrap();
        let w_arr = xor_rot_data.w_arr.unwrap();

        let needs_decomposition : bool = (rot % CHUNK_SIZE) != 0;
        if needs_decomposition {
            // [y0, y1, y2, y3]
            let mut row = GateAllocHelper::default();
            row.set_var(0, one.clone(), z.decomposed.r0, true)?;
            row.set_var(1, self.u64_to_ff(1 << CHUNK_SIZE), z.decomposed.r1, true)?;
            row.set_var(2, self.u64_to_ff(1 << (2 * CHUNK_SIZE)), z.decomposed.r2, true)?;
            row.set_var(3, self.u64_to_ff(1 << (3 * CHUNK_SIZE)), z.decomposed.r3, true)?;
            row.link_with_next_row(minus_one.clone());

            self.allocate_gate(cs, row)?;
        }

        // x[0], y[0], z[idx_0], z,
        // [x[1], y[1], z[idx_1], z - z[idx_0] * 8^[idx_0] = w0
        // x[2], y[2], z[idx_2], z - z[idx_0] * 8^[idx_0] - z[idx_1] * 8^[idx_1] = w1

        // equation for the first 3 rows: d - coef * c = d_next => d_next + coef * c - d = 0;        
        // equation of the last row is somehow different : c* coef - d = 0;
        // x[3], y[3], z[idx_3], z - z[idx_0] * 8^[idx_0] - z[idx_1] * 8^[idx_1] - z[idx_2] * 8^[idx_2] = w2

        for i in 0..4 {
            let a = self.to_allocated(cs, x.decomposed.get_var_by_idx(i))?;
            let b = self.to_allocated(cs, y.decomposed.get_var_by_idx(i))?;
            let c = q_arr[i].clone();
            let d = if i == 0 { z.full.clone() } else { w_arr[i-1].clone() };
            let coef = self.u64_to_ff(1 << xor_rot_data.shifts[i]);

            let mut row = GateAllocHelper::default();
            row.set_var(0, zero.clone(), a, true)?;
            row.set_var(1, zero.clone(), b, true)?;
            row.set_var(2, coef, c, true)?;
            row.set_var(3, minus_one.clone(), d, true)?;
            
            if i != 3 {
                row.link_with_next_row(one.clone());
            }
            let table = if i == 0 { self.choose_table_by_rot(rot) } else { self.xor_table.clone() };
            row.set_table(table);

            self.allocate_gate(cs, row)?;
        }

        Ok(())
    }

    fn G<CS>(&self, cs: &mut CS, v: &mut HashState<E>, idx_arr: [usize; 4], x: &Num<E>, y: &Num<E>) -> Result<()>
    where CS: ConstraintSystem<E>
    {
        let mut regs = v.0.get_muts();
        let a = regs.at(idx_arr[0])?;
        let b = regs.at(idx_arr[1])?;
        let c = regs.at(idx_arr[2])?;
        let d = regs.at(idx_arr[3])?;

        // first half of g function - setup
        let (temp_a, of1) = self.g_ternary_additon_setup(cs, a, b, x)?;
        let xor_rot_data1 = self.g_xor_rot_setup(cs, &temp_a, d, 16)?;
        let temp_d = xor_rot_data1.z.clone();
        let (temp_c, of2) = self.g_binary_addition_setup(cs, c, &temp_d)?;
        let xor_rot_data2 = self.g_xor_rot_setup(cs, b, &temp_c, 12)?;
        let temp_b = xor_rot_data2.z.clone(); 

        // first half of g function - burn preallocated variables to protoboard
        println!("1");
        self.g_ternary_addition_process(cs, a, b, x, &temp_a, &of1, &of2)?;
        println!("2");
        self.g_xor_rot_process(cs, &temp_a, d, xor_rot_data1, 16)?;
        println!("3");
        self.g_binary_addition_process(cs, c, &temp_d, &temp_c, &of2)?;
        self.g_xor_rot_process(cs, b, &temp_c, xor_rot_data2, 12)?;
        
        // second half of g function - setup
        let (new_a, of1) = self.g_ternary_additon_setup(cs, &temp_a, &temp_b, y)?;
        let xor_rot_data1 = self.g_xor_rot_setup(cs, &new_a, &temp_d, 8)?;
        let new_d = xor_rot_data1.z.clone();
        let (new_c, of2) = self.g_binary_addition_setup(cs, &temp_c, &new_d)?;
        let xor_rot_data2 = self.g_xor_rot_setup(cs, &temp_b, &new_c, 7)?;
        let new_b = xor_rot_data2.z.clone(); 

        // second half of g function - burn preallocated variables to protoboard
        self.g_ternary_addition_process(cs, &temp_a, &temp_b, y, &new_a, &of1, &of2)?;
        self.g_xor_rot_process(cs, &new_a, &temp_d, xor_rot_data1, 8)?;
        self.g_binary_addition_process(cs, &temp_c, &new_d, &new_c, &of2)?;
        self.g_xor_rot_process(cs, &temp_b, &new_c, xor_rot_data2, 7)?;
        
        *a = new_a;
        *b = new_b;
        *c = new_c;
        *d = new_d;

        Ok(())
    }

    // x ^ cnst = y
    // the trick used : assume that the constant is non-zero only for the 2-nd and 3-rd chunk
    // then the first row will be :
    // x[2], cnst[2], y[2], y_full
    // x[3], cnst[3], y[3], y_full - y[2] * (1 << 16)
    // x[0], x[4], dummy, y_full - y[2] * (1 << 16) - y[3] * (1 << 24)

    // if there are n -rows (and 1 <= n <= 3) modifed there will be n+1 constraints
    // if all rows are modified (n = 4) there will be 4 constraints
    fn var_xor_const<CS: ConstraintSystem<E>>(&self, cs: &mut CS, input: &DecomposedNum<E>, cnst: u64) -> Result<Reg<E>>
    {
        assert_ne!(cnst, 0);
        let zero = E::Fr::zero();
        let one = E::Fr::one();
        let mut minus_one = one.clone();
        minus_one.negate();

        let full_var = AllocatedNum::alloc(cs, || {
            let r0 = input.r0.get_value().grab()?.into_repr().as_ref()[0];
            let r1 = input.r1.get_value().grab()?.into_repr().as_ref()[0];
            let r2 = input.r2.get_value().grab()?.into_repr().as_ref()[0];
            let r3 = input.r3.get_value().grab()?.into_repr().as_ref()[0];

            let n = (r0 + (r1 << 8) + (r2 << 16) + (r3 << 24)) ^ cnst;
            Ok(self.u64_to_ff(n))
        })?;
        let full = Num::Allocated(full_var);
        
        let mut idx_used = [false, false, false, false];
        let mut res_chunks = [input.r0.clone(), input.r1.clone(), input.r2.clone(), input.r3.clone()];
        let mut d = full.clone();

        for i in 0..4 {
            let byte_val = (cnst >> 8 * i) & ((1 << CHUNK_SIZE) - 1);
            if byte_val != 0 {
                idx_used[i] = true;
                let a = input.get_var_by_idx(i).clone();

                let num = Num::Constant(self.u64_to_ff(byte_val));
                let b = self.to_allocated(cs, &num)?;
                
                let c = Num::Allocated(self.xor(cs, &a, &b)?);
                res_chunks[i] = c.clone();

                let mut row = GateAllocHelper::default();
                row.set_var(0, zero.clone(), a, true)?;
                row.set_var(1, zero.clone(), b, true)?;
                row.set_var(2, self.u64_to_ff(1u64 << (CHUNK_SIZE * i)), c.clone(), true)?;
                row.set_var(3, minus_one.clone(), d.clone(), true)?;
            
                if i != 3 || idx_used.iter().any(|flag| !flag)  {
                    row.link_with_next_row(one.clone());
                }
                row.set_table(self.xor_table.clone());
                self.allocate_gate(cs, row)?;

                let w = AllocatedNum::alloc(cs, || {
                    let mut d_val = d.get_value().grab()?;
                    let coef = self.u64_to_ff(1 << (CHUNK_SIZE * i));
                    let mut c_val = c.get_value().grab()?;
                    c_val.mul_assign(&coef);
                    d_val.sub_assign(&c_val);
                        
                    Ok(d_val)
                })?;
                d = Num::Allocated(w)
            }
        }

        // TODO: there is still room for optimizations when 3 out of 4 chunks are modified
        // then the constraint for the last row will be completely redundant!
        // and hence the last row may be multiplexed with constant allocation
        if idx_used.iter().any(|flag| !flag) {
            // for all unused chunks allocate with initial values:
            // equation of the form a * coef_a + b * coef_b + c * coef_d - d = 0;
            let mut pos = 0;
            let dummy = Num::Allocated(AllocatedNum::alloc_zero(cs)?);
            let mut row = GateAllocHelper::default();

            for i in 0..3 {
                while pos < 4 && idx_used[pos] { pos += 1};    
                let var = match pos {
                    0 | 1 | 2 | 3 => input.get_var_by_idx(pos).clone(),
                    _ => dummy.clone(),
                };
                row.set_var(i, self.u64_to_ff(1 << (i * CHUNK_SIZE)), var, true)?;
            }

            assert_eq!(pos, 4);
            row.set_var(3, minus_one, d, true)?;
            self.allocate_gate(cs, row)?;
        }

        let reg = Reg {
            full,
            decomposed : DecomposedNum {
                r0: res_chunks[0].clone(), r1 : res_chunks[1].clone(), r2: res_chunks[2].clone(), r3: res_chunks[3].clone(),
            },
        };
        Ok(reg)
    }

    fn var_xor_var<CS: ConstraintSystem<E>>(&self, cs: &mut CS, x: &DecomposedNum<E>, y: &DecomposedNum<E>) -> Result<Reg<E>>
    {
        let zero = E::Fr::zero();
        let one = E::Fr::one();
        let mut minus_one = one.clone();
        minus_one.negate();

        let full_var = AllocatedNum::alloc(cs, || {
            let x0 = x.r0.get_value().grab()?.into_repr().as_ref()[0];
            let x1 = x.r1.get_value().grab()?.into_repr().as_ref()[0];
            let x2 = x.r2.get_value().grab()?.into_repr().as_ref()[0];
            let x3 = x.r3.get_value().grab()?.into_repr().as_ref()[0];
            let n = x0 + (x1 << 8) + (x2 << 16) + (x3 << 24);

            let y0 = y.r0.get_value().grab()?.into_repr().as_ref()[0];
            let y1 = y.r1.get_value().grab()?.into_repr().as_ref()[0];
            let y2 = y.r2.get_value().grab()?.into_repr().as_ref()[0];
            let y3 = y.r3.get_value().grab()?.into_repr().as_ref()[0];
            let m = y0 + (y1 << 8) + (y2 << 16) + (y3 << 24);

            Ok(self.u64_to_ff(n ^ m))
        })?;
        
        let full = Num::Allocated(full_var);
        let mut res_chunks = <[Num<E>; 4]>::default();
        let mut d = full.clone();

        for i in 0..4 {   
            let a = x.get_var_by_idx(i).clone();
            let b = y.get_var_by_idx(i).clone();
            let c = Num::Allocated(self.xor(cs, &a, &b)?);
            res_chunks[i] = c.clone();

            let mut row = GateAllocHelper::default();
            row.set_var(0, zero.clone(), a, true)?;
            row.set_var(1, zero.clone(), b, true)?;
            row.set_var(2, self.u64_to_ff(1 << (CHUNK_SIZE * i)), c.clone(), true)?;
            row.set_var(3, minus_one.clone(), d.clone(), true)?;
        
            if i != 3 {
                row.link_with_next_row(one.clone());
            }
            row.set_table(self.xor_table.clone());
            self.allocate_gate(cs, row)?;

            let w = AllocatedNum::alloc(cs, || {
                let mut d_val = d.get_value().grab()?;
                let coef = self.u64_to_ff(1 << (CHUNK_SIZE * i));
                let mut c_val = c.get_value().grab()?;
                c_val.mul_assign(&coef);
                d_val.sub_assign(&c_val);
                    
                Ok(d_val)
            })?;
            d = Num::Allocated(w)
        }
        
        let reg = Reg {
            full,
            decomposed : DecomposedNum {
                r0: res_chunks[0].clone(), r1 : res_chunks[1].clone(), r2: res_chunks[2].clone(), r3: res_chunks[3].clone(),
            },
        };
        Ok(reg)
    }

    // for description look comments preceeding "apply ternary xor"
    fn var_xor_var_with_multiplexing<CS>(&self, cs: &mut CS, x: &DecomposedNum<E>, y: &DecomposedNum<E>) -> Result<DecomposedNum<E>>
    where CS: ConstraintSystem<E>
    {
        let mut temp_chunks = <[Num<E>; 4]>::default(); 
        let zero = E::Fr::zero();
        let one = E::Fr::one();

        // calculate temp (in decomposed form) multiplexing the calculation with constant allocation
        for i in 0..4 {
            let a = x.get_var_by_idx(i).clone();
            let b = y.get_var_by_idx(i).clone();
            let c = Num::Allocated(self.xor(cs, &a, &b)?);
            temp_chunks[i] = c.clone();

            let (d, cnst_sel) = match self.declared_cnsts.borrow().is_empty() {
                true => (Num::Allocated(AllocatedNum::alloc_zero(cs)?), E::Fr::zero()),
                false => {
                    let mut input_dict = self.declared_cnsts.borrow_mut();
                    let mut output_dict = self.allocated_cnsts.borrow_mut();
                    let key = input_dict.keys().next().unwrap().clone();
                    let val = input_dict.remove(&key).unwrap();
                    
                    let d = Num::Allocated(val.clone());
                    let mut cnst_sel = key.clone();
                    cnst_sel.negate();

                    output_dict.insert(key, val);
                    (d, cnst_sel)
                }
            };

            let mut row = GateAllocHelper::default();
            row.set_var(0, zero.clone(), a, true)?;
            row.set_var(1, zero.clone(), b, true)?;
            row.set_var(2, zero.clone(), c, true)?;
            row.set_var(3, one.clone(), d, true)?;
            row.set_cnst_sel(cnst_sel);
            row.set_table(self.xor_table.clone());
    
            self.allocate_gate(cs, row)?;
        }

        Ok(DecomposedNum { 
            r0 : temp_chunks[0].clone(), r1: temp_chunks[1].clone(), r2: temp_chunks[2].clone(), r3: temp_chunks[3].clone() 
        })
    }

    // handle ternary xor: y := a ^ b ^ c and return y in both full and decomposed form
    // we use the following optimizations: all constants are multiplexed into one
    // if all a, b, c are variables, there will be two rows steps:
    // first we calculate temp = a ^ b (only in decomposed form: temp[0], temp[1], temp[2], temp[3])
    // then as usual do:
    // temp[0], c[0], y[0], y_full
    // temp[1], c[1], y[1], y_full - y[0] * 2^8
    // temp[2], c[2], y[2], y_full - y[0] * 2^8 - y[1] * 2^16
    // temp[3], c[3], y[3], y_full - y[0] * 2^8 - y[1] * 2^16 - y[2] * 2^24

    // note that during calculation of temp_decomposed, no main gate is used (only application of xor table)
    // as well as d register remains vacant
    // we nay exploit the fact multiplexing xor-table-check with constant allocation!
    // more precisely: if there are any constant cnst0 waiting to be allocated, we may burn the following row:
    // a[i], b[i], temp[i], cnst, with the main gate equation d = const_cel = cnst! 
    fn apply_ternary_xor<CS: ConstraintSystem<E>>(&self, cs: &mut CS, a: &Reg<E>, b: &Reg<E>, c: &Reg<E>) -> Result<Reg<E>> {
        let res = match ((a.is_const(), a), (b.is_const(), b), (c.is_const(), c)) {
            // all are constants
            ((true, cnst_reg0), (true, cnst_reg1), (true, cnst_reg2)) => {
                let n0 = cnst_reg0.full.get_value().unwrap().into_repr().as_ref()[0];
                let n1 = cnst_reg1.full.get_value().unwrap().into_repr().as_ref()[0];
                let n2 = cnst_reg2.full.get_value().unwrap().into_repr().as_ref()[0];
                self.u64_to_reg(n0 ^ n1 ^ n2)
            },
            // one variable and two are constants
            ((false, var_reg), (true, cnst_reg0), (true, cnst_reg1)) | ((true, cnst_reg0), (false, var_reg), (true, cnst_reg1)) |
            ((true, cnst_reg0), (true, cnst_reg1), (false, var_reg)) => {
                let n0 = cnst_reg0.full.get_value().unwrap().into_repr().as_ref()[0];
                let n1 = cnst_reg1.full.get_value().unwrap().into_repr().as_ref()[0];
                self.var_xor_const(cs, &var_reg.decomposed, n0 ^ n1)?
            },
            // two are variables and one is constant
            ((false, var_reg0), (true, cnst_reg), (false, var_reg1)) | ((true, cnst_reg), (false, var_reg0), (false, var_reg1)) |
            ((false, var_reg0), (false, var_reg1), (true, cnst_reg)) => {
                let tmp = self.var_xor_var_with_multiplexing(cs, &var_reg0.decomposed, &var_reg1.decomposed)?;
                let n = cnst_reg.get_value().unwrap().into_repr().as_ref()[0];
                self.var_xor_const(cs, &tmp, n)?
            }
            // all three are variables
            _ => {
                let tmp = self.var_xor_var_with_multiplexing(cs, &a.decomposed, &b.decomposed)?;
                self.var_xor_var(cs, &tmp, &c.decomposed)?
            }
        };

        Ok(res) 
    }

    fn apply_xor_with_const<CS: ConstraintSystem<E>>(&self, cs: &mut CS, reg: &Reg<E>, cnst: u64) -> Result<Reg<E>>
    {
        if reg.is_const() {
            let temp = reg.full.get_value().unwrap();
            let f_repr = temp.into_repr();
            let n = f_repr.as_ref()[0];
            return Ok(self.u64_to_reg(n ^ cnst))
        }
        self.var_xor_const(cs, &reg.decomposed, cnst)
    }

    fn F<CS>(&self, cs: &mut CS, hash_state: HashState<E>, m: &[Num<E>], total_len: u64, last_block: bool) -> Result<HashState<E>>
    where CS: ConstraintSystem<E>
    {
        // Initialize local work vector v[0..15]
        let mut v = HashState(Vec::with_capacity(BLAKE2s_STATE_WIDTH));
        // First half from state.
        for i in 0..(BLAKE2s_STATE_WIDTH / 2) {
            v.0.push(hash_state.0[i].clone());
        }
        // Second half from IV.
        for i in 0..(BLAKE2s_STATE_WIDTH / 2) {
            let reg = self.u64_to_reg(self.iv[i]);
            v.0.push(reg);
        }

        v.0[12] = self.apply_xor_with_const(cs, &mut v.0[12], total_len & ((1 << REG_WIDTH) - 1))?; // Low word of the offset.
        v.0[13] = self.apply_xor_with_const(cs, &mut v.0[13], total_len >> REG_WIDTH)?; // High word.
        if last_block {
            // NB: xor with very special constant: x + y = 0xffffffff?
            v.0[14] = self.apply_xor_with_const(cs, &mut v.0[14], 0xffffffff)?; // Invert all bits.
        }

        // Cryptographic mixing: ten rounds
        for i in 0..10 {
            // Message word selection permutation for this round.
            let s = &self.sigmas[i];

            self.G(cs, &mut v, [0, 4, 8, 12], &m[s[0]], &m[s[1]])?;
            self.G(cs, &mut v, [1, 5, 9, 13], &m[s[2]], &m[s[3]])?;
            self.G(cs, &mut v, [2, 6, 10, 14], &m[s[4]], &m[s[5]])?;
            self.G(cs, &mut v, [3, 7, 11, 15], &m[s[6]], &m[s[7]])?;
            self.G(cs, &mut v, [0, 5, 10, 15], &m[s[8]], &m[s[9]])?;
            self.G(cs, &mut v, [1, 6, 11, 12], &m[s[10]], &m[s[11]])?;
            self.G(cs, &mut v, [2, 7, 8, 13], &m[s[12]], &m[s[13]])?;
            self.G(cs, &mut v, [3, 4, 9, 14], &m[s[14]], &m[s[15]])?;
        }

        // XOR the two halves.
        let mut res = HashState(Vec::with_capacity(BLAKE2s_STATE_WIDTH / 2));
        for i in 0..(BLAKE2s_STATE_WIDTH / 2) {
            // h[i] := h[i] ^ v[i] ^ v[i + 8]
            let t = self.apply_ternary_xor(cs, &hash_state.0[i], &v.0[i], &v.0[i + (BLAKE2s_STATE_WIDTH / 2)])?;
            res.0.push(t);
        }
        Ok(res)
    }

    pub fn digest<CS: ConstraintSystem<E>>(&self, cs: &mut CS, data: &[Num<E>]) -> Result<Vec<Num<E>>> 
    {
        // h[0..7] := IV[0..7] // Initialization Vector.
        let mut total_len : u64 = 0;
        let mut hash_state = HashState(Vec::with_capacity(BLAKE2s_STATE_WIDTH / 2));
        for i in 0..(BLAKE2s_STATE_WIDTH / 2) {
            let num = if i == 0 { self.iv0_twist } else { self.iv[i] };
            let reg = self.u64_to_reg(num);
            hash_state.0.push(reg);
        }

        for (_is_first, is_last, block) in data.chunks(16).identify_first_last() 
        {
            assert_eq!(block.len(), 16);
            total_len += 64;
            hash_state = self.F(cs, hash_state, &block[..], total_len, is_last)?;
        }

        // allocate all remaining consts
        self.constraint_all_allocated_cnsts(cs)?;

        let mut res = Vec::with_capacity(BLAKE2s_STATE_WIDTH / 2);
        for elem in hash_state.0.drain(0..(BLAKE2s_STATE_WIDTH / 2)) {
            res.push(elem.full);
        }
        Ok(res)
    }
}

impl<E: Engine> Blake2sGadget<E> for OptimizedBlake2sGadget<E> {
    fn new<CS: ConstraintSystem<E>>(cs: &mut CS) -> Result<Self> {
        OptimizedBlake2sGadget::new(cs)
    }
    fn digest<CS: ConstraintSystem<E>>(&self, cs: &mut CS, data: &[Num<E>]) -> Result<Vec<Num<E>>> {
        self.digest(cs, data)
    }
}
