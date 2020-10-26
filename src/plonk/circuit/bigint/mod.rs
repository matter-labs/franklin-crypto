use crate::bellman::pairing::{
    Engine,
};

use crate::bellman::pairing::ff::{
    Field,
    PrimeField,
    PrimeFieldRepr,
    BitIterator
};

use crate::bellman::{
    SynthesisError,
};

use crate::bellman::plonk::better_better_cs::cs::{
    Variable, 
    ConstraintSystem,
    ArithmeticTerm,
    MainGateTerm,
    Width4MainGateWithDNext,
    MainGate,
    GateInternal,
    Gate,
    LinearCombinationOfTerms,
    PolynomialMultiplicativeTerm,
    PolynomialInConstraint,
    TimeDilation,
    Coefficient,
    PlonkConstraintSystemParams,
    PlonkCsWidth4WithNextStepParams,
    TrivialAssembly
};

use crate::circuit::Assignment;

use super::allocated_num::*;

pub mod bigint;
pub mod field;
pub mod range_constraint_gate;
pub mod range_constraint_functions;
pub mod range_constraint_with_two_bit_gate;
pub mod single_table_range_constraint;

use self::range_constraint_gate::TwoBitDecompositionRangecheckCustomGate;

// dummy for now, will address later based on either lookup/range check or trivial
// single bit / two bit decompositions
#[track_caller]
pub fn constraint_num_bits<E: Engine, CS: ConstraintSystem<E>>(cs: &mut CS, el: &Num<E>, num_bits: usize) -> Result<(), SynthesisError> {
    match el {
        Num::Constant(c) => {
            let bits = c.into_repr().num_bits() as usize;
            assert!(bits <= num_bits);
        },
        Num::Variable(el) => {
            if let Some(value) = el.get_value() {
                let bits = value.into_repr().num_bits() as usize;
                assert!(bits <= num_bits);
            }
            let infos = get_range_constraint_info(&*cs);
            match infos[0].strategy {
                RangeConstraintStrategy::MultiTable => {
                    self::range_constraint_functions::coarsely_enforce_using_multitable(cs, &el, num_bits)?;
                },
                RangeConstraintStrategy::SingleTableInvocation => {
                    self::single_table_range_constraint::enforce_using_single_column_table(cs, &el, num_bits)?;
                },
                RangeConstraintStrategy::CustomTwoBitGate => {
                    let _ = create_range_constraint_chain(cs, &el, num_bits)?;
                }
                _ => {unimplemented!("range constraint strategies other than multitable, single table or custom gate are not yet handled")}
            }
        }
    }
    
    Ok(())
}

// splits an element into slices of fixed bit widths in LE order
pub fn split_into_slices<F: PrimeField>(
    el: &F,
    slice_width: usize,
    num_slices: usize
) -> Vec<F> {
    let mut repr = el.into_repr();
    let mut slices = Vec::with_capacity(num_slices);
    let mask = (1u64 << slice_width) - 1u64;
    for _ in 0..num_slices {
        let slice = repr.as_ref()[0] & mask;

        let mut r = F::Repr::default();
        r.as_mut()[0] = slice;

        let slice = F::from_repr(r).unwrap();
        slices.push(slice);

        repr.shr(slice_width as u32);
    }

    slices
}

pub fn split_some_into_slices<F: PrimeField>(
    el: Option<F>,
    slice_width: usize,
    num_slices: usize
) -> Vec<Option<F>> {
    if let Some(v) = el.as_ref() {
        split_into_slices(v, slice_width, num_slices).into_iter().map(|el| Some(el)).collect()
    } else {
        vec![None; num_slices]
    }
}

fn split_into_accululating_slices<F: PrimeField>(
    el: &F,
    slice_width: usize,
    num_slices: usize
) -> Vec<F> {
    let bases = split_into_slices(el, slice_width, num_slices);
    let mut slices = Vec::with_capacity(num_slices);
    let mut accum = F::zero();
    let mut base = F::one();
    for _ in 0..slice_width {
        base.double();
    }
    let mut factor = F::one();
    for s in bases.into_iter() {
        let mut tmp = s;
        tmp.mul_assign(&factor);
        accum.add_assign(&tmp);
        slices.push(accum);

        factor.mul_assign(&base);
    }

    slices
}

fn split_into_bit_constraint_slices<F: PrimeField>(
    el: &F,
    slice_width: usize,
    num_slices: usize
) -> Vec<F> {
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

use std::sync::atomic::{AtomicUsize, Ordering};

pub(crate) static RANGE_GATES_COUNTER: AtomicUsize = AtomicUsize::new(0);

// This is a case for no lookup tables that constraints 8 bits per gate
#[track_caller]
pub fn create_range_constraint_chain<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS, 
    to_constraint: &AllocatedNum<E>, 
    num_bits: usize
) -> Result<Vec<AllocatedNum<E>>, SynthesisError> {
    assert!(num_bits > 0);
    assert!(num_bits & 1 == 0);
    assert_eq!(CS::Params::STATE_WIDTH, 4, "this only works for a state of width 4 for now");
    if let Some(v) = to_constraint.get_value() {
        let t = self::bigint::fe_to_biguint(&v);
        assert!(t.bits() as usize <= num_bits, "value is {} that is {} bits, while expected {} bits", t.to_str_radix(16), t.bits(), num_bits);
    }
    let num_elements = num_bits / 2;
    let mut slices: Vec<Option<E::Fr>> = if let Some(v) = to_constraint.get_value() {
        split_into_bit_constraint_slices(&v, 2, num_elements).into_iter().map(|el| Some(el)).collect()
    } else {
        vec![None; num_elements]
    };

    let last_val = slices.pop().unwrap();
    if let Some(last_val) = last_val {
        if let Some(v) = to_constraint.get_value() {
            assert_eq!(last_val, v);
        }
    }
    
    let mut result = vec![];
    for v in slices.into_iter() {
        let a = AllocatedNum::alloc(
            cs, 
            || {
                Ok(*v.get()?)
            }
        )?;

        result.push(a);
    }

    // last element is actually an element we want to constraint
    result.push(to_constraint.clone());

    let mut num_gates = num_bits / 8;
    if num_gates % 8 != 0 {
        num_gates += 1;
    }

    let mut raw_variables = Vec::with_capacity(result.len() + 1);
    // let zero_var = AllocatedNum::zero(cs).get_variable();
    // raw_variables.push(zero_var);
    raw_variables.push(cs.get_explicit_zero()?);
    // we start at D(x) with 0
    for el in result.iter() {
        raw_variables.push(el.get_variable());
    }

    if raw_variables.len() % 4 != 1 {
        let to_add = (5 - (raw_variables.len() % 4)) % 4;

        let mut four = E::Fr::one();
        four.double();
        four.double();

        let four = Some(four);

        use crate::circuit::SomeField;

        let mut previous_value = to_constraint.get_value();

        for _ in 0..to_add {
            let new_value = previous_value.mul(&four);
            let padding = cs.alloc(
                || {
                    Ok(*new_value.get()?)
                }
            )?;

            raw_variables.push(padding);

            previous_value = new_value;
        }
    }

    assert_eq!(raw_variables.len() % 4, 1, "variables len = {}", raw_variables.len());

    let mut rows = raw_variables.chunks_exact(4);

    let gate = TwoBitDecompositionRangecheckCustomGate::default();

    for row in &mut rows {
        let mut row = row.to_vec();
        row.reverse();
        cs.new_single_gate_for_trace_step(
            &gate, 
            &[], 
            &row, 
            &[]
        )?;
    }

    let last = rows.remainder();
    assert!(last.len() == 1);

    let last = last[0];

    let dummy = CS::get_dummy_variable();

    // cause we touch D_Next place an empty gate to the next row

    let (mut variables, coeffs) = CS::MainGate::format_term(MainGateTerm::new(), dummy)?;
    *variables.last_mut().unwrap() = last;

    cs.new_single_gate_for_trace_step(
        &CS::MainGate::default(), 
        &coeffs, 
        &variables, 
        &[]
    )?;

    RANGE_GATES_COUNTER.fetch_add(num_gates+1, Ordering::SeqCst);

    Ok(result)
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum RangeConstraintStrategy {
    MultiTable,
    SingleTableInvocation,
    CustomTwoBitGate,
    NaiveSingleBit
}

impl RangeConstraintStrategy {
    pub fn can_access_minimal_multiple_quants(&self) -> bool {
        match self {
            RangeConstraintStrategy::MultiTable => false,
            RangeConstraintStrategy::SingleTableInvocation => true,
            RangeConstraintStrategy::CustomTwoBitGate => true,
            RangeConstraintStrategy::NaiveSingleBit => false,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RangeConstraintInfo {
    pub minimal_multiple: usize,
    pub optimal_multiple: usize,
    pub multiples_per_gate: usize,
    pub linear_terms_used: usize,
    pub strategy: RangeConstraintStrategy,
}

const RANGE_CHECK_MULTIAPPLICATION_TABLE_NAME: &'static str = "Range check table";
const RANGE_CHECK_SINGLE_APPLICATION_TABLE_NAME: &'static str = "Range check table for a single column";

pub fn get_range_constraint_info<E: Engine, CS: ConstraintSystem<E>>(cs: &CS) -> Vec<RangeConstraintInfo> {
    let mut strategies = Vec::with_capacity(4);

    use crate::bellman::plonk::better_better_cs::cs::PolyIdentifier;

    if let Ok(multi) = cs.get_multitable(RANGE_CHECK_MULTIAPPLICATION_TABLE_NAME) {
        let width = crate::log2_floor(multi.size());
        let multiples = multi.applies_over().len();
        let table_width_over_polys = multi.applies_over().len();

        assert!(multiples <= 3);
        assert!(multi.applies_over() == &[PolyIdentifier::VariablesPolynomial(0), PolyIdentifier::VariablesPolynomial(1), PolyIdentifier::VariablesPolynomial(2)]);

        let strategy = RangeConstraintInfo {
            minimal_multiple: width as usize,
            optimal_multiple: (width as usize) * multiples,
            multiples_per_gate: multiples,
            linear_terms_used: table_width_over_polys,
            strategy: RangeConstraintStrategy::MultiTable
        };

        strategies.push(strategy);
    }

    if let Ok(single) = cs.get_table(RANGE_CHECK_SINGLE_APPLICATION_TABLE_NAME) {
        let width = crate::log2_floor(single.size());
        let table_width_over_polys = single.applies_over().len();

        assert!(single.applies_over() == &[PolyIdentifier::VariablesPolynomial(0), PolyIdentifier::VariablesPolynomial(1), PolyIdentifier::VariablesPolynomial(2)]);

        let strategy = RangeConstraintInfo {
            minimal_multiple: width as usize,
            optimal_multiple: width as usize,
            multiples_per_gate: 1,
            linear_terms_used: table_width_over_polys,
            strategy: RangeConstraintStrategy::SingleTableInvocation
        };
    
        strategies.push(strategy);
    }

    if CS::Params::STATE_WIDTH == 4 && CS::Params::HAS_CUSTOM_GATES {
        let strategy = RangeConstraintInfo {
            minimal_multiple: 2,
            optimal_multiple: 8,
            multiples_per_gate: 4,
            linear_terms_used: 0,
            strategy: RangeConstraintStrategy::CustomTwoBitGate
        };

        strategies.push(strategy);
    }

    let strategy = RangeConstraintInfo {
        minimal_multiple: 1,
        optimal_multiple: 1,
        multiples_per_gate: 1,
        linear_terms_used: 0,
        strategy: RangeConstraintStrategy::NaiveSingleBit
    };

    strategies.push(strategy);

    strategies
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn check_two_bit_gate() {
        use crate::bellman::pairing::bn256::{Bn256, Fr};
        use crate::bellman::plonk::better_better_cs::cs::*;
        use crate::plonk::circuit::bigint::*;
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
        
                let result = lc.into_allocated_num(cs).unwrap();
            
                let num = AllocatedNum::alloc(
                    cs,
                    || {
                        Ok(Fr::from_str("40000").unwrap())
                    }
                ).unwrap();
        
                let _ = create_range_constraint_chain(cs, &num, 18)?;

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

        let proof = assembly.create_proof::<_, RollingKeccakTranscript<Fr>>(
            &worker, 
            &setup, 
            &crs_mons,
            None
        ).unwrap();
    }
}