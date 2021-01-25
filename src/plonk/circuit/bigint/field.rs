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
    PlonkConstraintSystemParams
};

use super::super::allocated_num::{AllocatedNum, Num};
use super::super::linear_combination::LinearCombination;
use super::super::simple_term::Term;
use super::super::boolean::{Boolean, AllocatedBit};
use crate::circuit::SomeField;

use super::*;
use super::bigint::*;
use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::Zero;

// Parameters of the representation
#[derive(Clone, Debug)]
pub struct RnsParameters<E: Engine, F: PrimeField>{
    // this is kind-of normal UintX limbs
    pub binary_limbs_params: LimbedRepresentationParameters<E>,
    pub num_binary_limbs: usize,
    pub binary_modulus: BigUint,
    pub num_limbs_for_in_field_representation: usize,

    // convenience
    pub base_field_modulus: BigUint,
    pub binary_representation_max_value: BigUint,

    // modulus if the field that we represent
    // we know the modulus and how large will be limbs in the base case
    // of maximally filled distribution
    pub represented_field_modulus: BigUint,
    pub binary_limbs_bit_widths: Vec<usize>,
    pub binary_limbs_max_values: Vec<BigUint>,

    // we do modular reductions, so we want to have these for convenience
    pub represented_field_modulus_limbs: Vec<E::Fr>,
    pub represented_field_modulus_negated_limbs_biguints: Vec<BigUint>,
    pub represented_field_modulus_negated_limbs: Vec<E::Fr>,

    pub represented_field_modulus_in_base_field: E::Fr,

    // -modulus of represented field in base field
    pub represented_field_modulus_negated_in_base_field: E::Fr,

    pub range_check_info: RangeConstraintInfo,

    pub prefer_single_limb_allocation: bool,
    pub prefer_single_limb_carry_propagation: bool,

    pub (crate) _marker: std::marker::PhantomData<F>
}

impl<'a, E: Engine, F: PrimeField> RnsParameters<E, F>{
    pub fn max_representable_value(&self) -> BigUint {
        let mut tmp = self.base_field_modulus.clone() * &self.binary_representation_max_value;
        tmp = tmp.sqrt();
        debug_assert!(&tmp >= &self.represented_field_modulus, 
            "not sufficient capacity to represent modulus: can represent up to {} bits, modulus is {} bits", 
            tmp.bits() - 1, 
            self.represented_field_modulus.bits()
        );

        tmp
    }

    pub fn new_for_field(limb_size: usize, intermediate_limb_capacity: usize, num_binary_limbs:usize) -> Self {
        let default_strategy = RangeConstraintInfo {
            minimal_multiple: 2,
            optimal_multiple: 8,
            multiples_per_gate: 4,
            linear_terms_used: 4,
            strategy: RangeConstraintStrategy::CustomTwoBitGate
        };

        Self::new_for_field_with_strategy(limb_size, intermediate_limb_capacity, num_binary_limbs, default_strategy, false)
    }

    pub fn new_for_field_with_strategy(
        limb_size: usize, 
        intermediate_limb_capacity: usize, 
        num_binary_limbs:usize,
        strategy: RangeConstraintInfo,
        prefer_single_limb_allocation: bool
    ) -> Self {
        let binary_limbs_params = LimbedRepresentationParameters::new(limb_size, intermediate_limb_capacity);

        let minimal_multiple = strategy.minimal_multiple;
        assert!(limb_size % minimal_multiple == 0, "limb size is not a multiple of range check quant");

        let base_field_modulus = repr_to_biguint::<E::Fr>(&E::Fr::char());
        let binary_modulus = BigUint::from(1u64) << (num_binary_limbs * limb_size);
        let binary_representation_max_value = binary_modulus.clone() - BigUint::from(1u64);

        let represented_field_modulus = repr_to_biguint::<F>(&F::char());

        let represented_modulo_base = biguint_to_fe(repr_to_biguint::<F>(&F::char()) % &base_field_modulus);

        let represented_modulus_negated_modulo_binary = binary_modulus.clone() - &represented_field_modulus;

        let mask = BigUint::from(1u64) << limb_size;

        let mut binary_limbs_max_bits_if_in_field = Vec::with_capacity(num_binary_limbs);
        let mut binary_limbs_max_values_if_in_field = Vec::with_capacity(num_binary_limbs);
        let mut tmp = represented_field_modulus.clone();

        use num_traits::Zero;

        let mut num_limbs_for_in_field_representation = 0;

        let mut freshly_allocated_max_value = BigUint::from(0u64);
        let mut shift = 0;

        for _ in 0..num_binary_limbs {
            if tmp.is_zero() {
                binary_limbs_max_bits_if_in_field.push(0);
                binary_limbs_max_values_if_in_field.push(BigUint::from(0u64));
            } else {
                let current_bits = tmp.bits() as usize;
                tmp >>= limb_size;
                if tmp.is_zero() {
                    // this is a last limb
                    let _remainder = current_bits % minimal_multiple;
                    // if remainder != 0 {
                    //     current_bits += minimal_multiple - remainder;
                    // }
                    binary_limbs_max_bits_if_in_field.push(current_bits);
                    let max_value = (BigUint::from(1u64) << current_bits) - BigUint::from(1u64);

                    freshly_allocated_max_value += &max_value << shift;
                    binary_limbs_max_values_if_in_field.push(max_value);

                    shift += current_bits;
                } else {
                    binary_limbs_max_bits_if_in_field.push(binary_limbs_params.limb_size_bits);
                    binary_limbs_max_values_if_in_field.push(binary_limbs_params.limb_max_value.clone());
                    freshly_allocated_max_value += &binary_limbs_params.limb_max_value << shift;

                    shift += binary_limbs_params.limb_size_bits;
                }
                num_limbs_for_in_field_representation += 1;
            }
        }

        let mut modulus_limbs = vec![];
        let mut tmp = represented_field_modulus.clone();

        for _ in 0..num_binary_limbs {
            let chunk = tmp.clone() % &mask;
            let fe = biguint_to_fe::<E::Fr>(chunk);
            modulus_limbs.push(fe);
            tmp >>= limb_size;
        }

        let mut tmp = represented_modulus_negated_modulo_binary.clone();

        let mut negated_modulus_chunks_bit_width = vec![];
        let mut negated_modulus_chunks = vec![];
        let mut represented_field_modulus_negated_limbs = vec![];

        for _ in 0..num_binary_limbs {
            let chunk = tmp.clone() % &mask;
            negated_modulus_chunks_bit_width.push(chunk.bits() as usize);
            negated_modulus_chunks.push(chunk.clone());
            let fe = biguint_to_fe::<E::Fr>(chunk);
            represented_field_modulus_negated_limbs.push(fe);
            tmp >>= limb_size;
        }

        let repr_modulus_negated = base_field_modulus.clone() - (represented_field_modulus.clone() % &base_field_modulus.clone());
        let repr_modulus_negated = biguint_to_fe(repr_modulus_negated);

        let new = Self {
            binary_limbs_params,
            num_binary_limbs,
            binary_modulus,
            base_field_modulus: base_field_modulus.clone(),
            num_limbs_for_in_field_representation,
            binary_representation_max_value,
            represented_field_modulus,
            binary_limbs_bit_widths: binary_limbs_max_bits_if_in_field.clone(),
            binary_limbs_max_values: binary_limbs_max_values_if_in_field.clone(),
            represented_field_modulus_negated_limbs_biguints : negated_modulus_chunks,
            represented_field_modulus_limbs: modulus_limbs,
            represented_field_modulus_negated_limbs,
            represented_field_modulus_negated_in_base_field: repr_modulus_negated,
            range_check_info: strategy,
            prefer_single_limb_allocation: prefer_single_limb_allocation,
            prefer_single_limb_carry_propagation: false,
            represented_field_modulus_in_base_field: represented_modulo_base,

            _marker: std::marker::PhantomData
        };

        if freshly_allocated_max_value >= new.max_representable_value() {
            panic!("Newly allocated value will have limit of {} ({} bits) that is larger than max intermediate value {} ({} bits) before forced reduction",
            &freshly_allocated_max_value, freshly_allocated_max_value.bits(), new.max_representable_value(), new.max_representable_value().bits());
        }

        if new.can_allocate_from_double_limb_witness() {
            assert!(E::Fr::CAPACITY as usize >= limb_size * 2, "double limb size must not overflow the capacity");
        }

        new
    }

    pub fn can_allocate_from_double_limb_witness(&self) -> bool {
        if self.prefer_single_limb_allocation == true {
            return false;
        }

        if self.range_check_info.strategy.can_access_minimal_multiple_quants() {
            true
        } else {
            self.prefer_single_limb_allocation == false && self.binary_limbs_params.limb_size_bits % self.range_check_info.optimal_multiple == 0
        }
    }

    pub fn set_prefer_single_limb_allocation(&mut self, new_value: bool) {
        self.prefer_single_limb_allocation = new_value;
    }

    pub fn set_prefer_double_limb_carry_propagation(&mut self, value: bool) {
        self.prefer_single_limb_carry_propagation = !value;
    }

    pub fn propagate_carries_using_double_limbs(&self) -> bool {
        !self.prefer_single_limb_carry_propagation
    }
}

#[derive(Clone, Debug)]
pub struct FieldElement<'a, E: Engine, F: PrimeField>{
    // this is kind-of normal UintX limbs
    pub binary_limbs: Vec<Limb<E>>,
    // we can not multiply by power of modulus of our base field E,
    // so we keep only one single limb
    pub base_field_limb: Term<E>,

    pub representation_params: &'a RnsParameters<E, F>,
    pub value: Option<F>,
}

impl<'a, E: Engine, F: PrimeField> std::fmt::Display for FieldElement<'a, E, F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "FieldElement {{ ")?;
        write!(f, "Modulus = {}, ", F::char())?;
        write!(f, "Value = {:?}, ", self.get_field_value())?;
        if let Some(v) = self.get_value() {
            write!(f, "Value from binary limbs = {}, ", v.to_str_radix(16))?;
        } else {
            write!(f, "Value from binary limbs = None, ")?;
        }
        for (i, l) in self.binary_limbs.iter().enumerate() {
            write!(f, "Limb {}: value = {:?}, max_value = {}, bits = {}, ", i, l.term.get_value(), l.max_value.to_str_radix(16), l.max_value.bits())?;
        }
        write!(f, "Base field limb value = {:?} ", self.base_field_limb.get_value())?;
        writeln!(f, "}}")
    }
}

pub fn split_into_limbs<E: Engine, F: PrimeField>(
    value: F,
    params: &RnsParameters<E, F>
) -> (Vec<E::Fr>, E::Fr) {
    let value_as_bigint = fe_to_biguint(&value);
    let binary_limb_values = split_into_fixed_number_of_limbs(
        value_as_bigint, 
        params.binary_limbs_params.limb_size_bits, 
        params.num_binary_limbs
    );
    assert_eq!(binary_limb_values.len(), params.num_binary_limbs);

    let base_limb = fe_to_biguint(&value) % &params.base_field_modulus;
    let base_limb = biguint_to_fe::<E::Fr>(base_limb);

    let binary_limbs: Vec<E::Fr> = binary_limb_values.into_iter().map(|el| biguint_to_fe::<E::Fr>(el)).collect();
    assert_eq!(binary_limbs.len(), params.num_binary_limbs);

    return (binary_limbs, base_limb);
}

pub fn value_to_limbs<E: Engine, F: PrimeField>(
    value: Option<F>,
    params: &RnsParameters<E, F>
) -> (Vec<Option<E::Fr>>, Option<E::Fr>) {
    let num_limbs = params.num_binary_limbs;

    match value {
        Some(value) => {
            let (binary_limbs, base_limb) = split_into_limbs(value, params);
            let binary_limbs: Vec<Option<E::Fr>> = binary_limbs.into_iter().map(|el| Some(el)).collect();
            assert_eq!(binary_limbs.len(), params.num_binary_limbs);

            return (binary_limbs, Some(base_limb));
        },
        None => {
            return (vec![None; num_limbs], None);
        }
    }
}

impl<'a, E: Engine, F: PrimeField> FieldElement<'a, E, F> {
    pub fn into_limbs(self) -> Vec<Term<E>> {
        let mut result = vec![];
        for limb in self.binary_limbs.iter() {
            let t = limb.term.clone();
            result.push(t);
        }

        result
    }

    // pub fn constant(
    //     value: F,
    //     params: &'a RnsParameters<E, F>
    // ) -> Self {
    //     let (binary_limb_values, base_limb_value) = split_into_limbs(value, params);

    //     let mut binary_limbs = Vec::with_capacity(params.num_binary_limbs);

    //     for (l, &width) in binary_limb_values.into_iter()
    //         .zip(params.binary_limbs_bit_widths.iter())
    //     {
    //         if width == 0 {
    //             assert!(l.is_zero());
    //         }
    //         let limb = Limb::new_constant_from_field_value(l);
    //         binary_limbs.push(limb);
    //     }

    //     let base_limb = Term::from_constant(base_limb_value);

    //     Self {
    //         binary_limbs,
    //         base_field_limb: base_limb,
    //         representation_params: params,
    //         value: Some(value),
    //     }
    // }

    pub fn new_allocated<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        value: Option<F>,
        params: &'a RnsParameters<E, F>
    ) -> Result<Self, SynthesisError> {
        let (binary_limbs, _) = value_to_limbs(value, params);

        let mut witnesses = Vec::with_capacity(params.num_binary_limbs);

        for (l, &width) in binary_limbs.into_iter()
            .zip(params.binary_limbs_bit_widths.iter())
        {
            if width == 0 {
                witnesses.push(Num::Constant(E::Fr::zero()));
            } else {
                let a = AllocatedNum::alloc(cs, || {
                    Ok(*l.get()?)
                })?;

                let n = Num::Variable(a);

                witnesses.push(n);
            }
        }

        Self::coarsely_allocate_from_single_limb_witnesses(cs, &witnesses, false, params)
    }

    pub fn new_allocated_in_field<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        value: Option<F>,
        params: &'a RnsParameters<E, F>
    ) -> Result<Self, SynthesisError> {
        let (binary_limbs, _) = value_to_limbs(value, params);

        let mut witnesses = Vec::with_capacity(params.num_binary_limbs);

        for (l, &width) in binary_limbs.into_iter()
            .zip(params.binary_limbs_bit_widths.iter())
        {
            if width == 0 {
                witnesses.push(Num::Constant(E::Fr::zero()));
            } else {
                let a = AllocatedNum::alloc(cs, || {
                    Ok(*l.get()?)
                })?;

                let n = Num::Variable(a);

                witnesses.push(n);
            }
        }

        Self::allocate_from_single_limb_witnesses_in_field(cs, &witnesses, params)
    }

    /// Allocate a field element from witnesses for individual binary(!) limbs,
    /// such that highest limb may be a little (up to range constraint granularity)
    /// larger than for an element that is in a field. Number of limbs is limited,
    /// so that number of binary limbs is strictly enough to represent value in-field
    #[track_caller]
    pub fn allocate_from_single_limb_witnesses_in_field<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        witnesses: &[Num<E>],
        params: &'a RnsParameters<E, F>
    ) -> Result<Self, SynthesisError> {
        assert_eq!(params.num_limbs_for_in_field_representation, witnesses.len());
        assert!(params.binary_limbs_params.limb_size_bits % params.range_check_info.minimal_multiple == 0, 
            "limb size must be divisible by range constraint strategy granularity");

        let mut binary_limbs_allocated = Vec::with_capacity(params.num_binary_limbs);

        let mut base_field_lc = LinearCombination::<E>::zero();

        let shift_constant = params.binary_limbs_params.shift_left_by_limb_constant;
        let mut current_constant = E::Fr::one();

        let mut this_value = BigUint::from(0u64);
        let mut value_is_none = false;

        for (witness_idx, w) in witnesses.iter().enumerate() {
            match w {
                Num::Constant(value) => {
                    let v = fe_to_biguint(value);
                    this_value += v.clone() << (witness_idx*params.binary_limbs_params.limb_size_bits);

                    let (expected_width, expected_max_value) = 
                        (params.binary_limbs_bit_widths[witness_idx], params.binary_limbs_max_values[witness_idx].clone());

                    assert!(expected_width > 0);
                    assert!(v.bits() as usize <= expected_width);
                    assert!(v <= expected_max_value);

                    let limb = Limb::<E>::new_constant(
                        v
                    );

                    binary_limbs_allocated.push(limb);
                },
                Num::Variable(var) => {
                    let limb_value = if let Some(v) = var.get_value() {
                        let v = fe_to_biguint(&v);
                        this_value += v.clone() << (witness_idx*params.binary_limbs_params.limb_size_bits);

                        Some(v)
                    } else {
                        value_is_none = true;

                        None
                    };

                    let (expected_width, expected_max_value) = 
                        (params.binary_limbs_bit_widths[witness_idx], params.binary_limbs_max_values[witness_idx].clone());

                    assert!(expected_width > 0);
                    if let Some(v) = limb_value.as_ref() {
                        assert!(v <= &expected_max_value, "limb is {}, max value is {}", v.to_str_radix(16), expected_max_value.to_str_radix(16));
                    }

                    // match over strategy

                    match params.range_check_info.strategy {
                        RangeConstraintStrategy::MultiTable => {
                            self::range_constraint_functions::coarsely_enforce_using_multitable(cs, var, expected_width)?;
                        },
                        RangeConstraintStrategy::SingleTableInvocation => {
                            self::single_table_range_constraint::enforce_using_single_column_table(cs, var, expected_width)?;
                        },
                        RangeConstraintStrategy::CustomTwoBitGate => {
                            let _ = create_range_constraint_chain(cs, var, expected_width)?;
                        }
                        _ => {unimplemented!("range constraint strategies other than multitable, single table or custom gate are not yet handled")}
                    }

                    let term = Term::<E>::from_allocated_num(var.clone());

                    let limb = Limb::<E>::new( 
                        term,
                        expected_max_value,
                    );

                    binary_limbs_allocated.push(limb);
                }
            }

            // keep track of base field limb
            base_field_lc.add_assign_number_with_coeff(&w, current_constant);
            current_constant.mul_assign(&shift_constant);
        }

        // add to full number of binary limbs
        binary_limbs_allocated.resize(params.num_binary_limbs, Self::zero_limb());

        let base_field_limb_num = base_field_lc.into_num(cs)?;

        let base_field_term = Term::<E>::from_num(base_field_limb_num);

        let this_value = if value_is_none {
            None
        } else {
            Some(this_value)
        };

        let this_value = some_biguint_to_fe::<F>(&this_value);

        let new = Self {
            binary_limbs: binary_limbs_allocated,
            base_field_limb: base_field_term,
            representation_params: params,
            value: this_value,
        };

        assert!(new.needs_reduction() == false);

        Ok(new)
    }

    /// Allocate a field element from witnesses for individual binary(!) limbs,
    /// such that highest limb may be a little (up to range constraint granularity)
    /// larger than for an element that is in a field.
    /// If `may_overflow` == true then all limbs may be as large limb bit width
    #[track_caller]
    pub fn coarsely_allocate_from_single_limb_witnesses<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        witnesses: &[Num<E>],
        may_overflow: bool,
        params: &'a RnsParameters<E, F>
    ) -> Result<Self, SynthesisError> {
        assert!(params.num_binary_limbs == witnesses.len());
        assert!(params.binary_limbs_params.limb_size_bits % params.range_check_info.minimal_multiple == 0, 
            "limb size must be divisible by range constraint strategy granularity");

        let mut binary_limbs_allocated = Vec::with_capacity(params.num_binary_limbs);

        let mut base_field_lc = LinearCombination::<E>::zero();

        let shift_constant = params.binary_limbs_params.shift_left_by_limb_constant;
        let mut current_constant = E::Fr::one();

        let mut this_value = BigUint::from(0u64);
        let mut value_is_none = false;

        for (witness_idx, w) in witnesses.iter().enumerate() {
            match w {
                Num::Constant(value) => {
                    let v = fe_to_biguint(value);
                    this_value += v.clone() << (witness_idx*params.binary_limbs_params.limb_size_bits);


                    // if the element must fit into the field than pad with zeroes
                    if may_overflow == false && witness_idx >= params.num_limbs_for_in_field_representation {
                        assert!(value.is_zero());
                        binary_limbs_allocated.push(Self::zero_limb());
                        continue;
                    }

                    let (expected_width, expected_max_value) = if may_overflow {
                        (params.binary_limbs_params.limb_size_bits, params.binary_limbs_params.limb_max_value.clone())
                    } else {
                        (params.binary_limbs_bit_widths[witness_idx], params.binary_limbs_max_values[witness_idx].clone())
                    };

                    assert!(expected_width > 0);
                    assert!(v.bits() as usize <= expected_width);
                    assert!(v <= expected_max_value);

                    let limb = Limb::<E>::new_constant(
                        v
                    );

                    binary_limbs_allocated.push(limb);
                },
                Num::Variable(var) => {
                    let limb_value = if let Some(v) = var.get_value() {
                        let v = fe_to_biguint(&v);
                        this_value += v.clone() << (witness_idx*params.binary_limbs_params.limb_size_bits);

                        Some(v)
                    } else {
                        value_is_none = true;

                        None
                    };

                    // if the element must fit into the field than pad with zeroes
                    if may_overflow == false && witness_idx >= params.num_limbs_for_in_field_representation {
                        unreachable!("should not try to allocate a value in a field with non-constant high limbs");
                    }

                    let (mut expected_width, mut expected_max_value) = if may_overflow {
                        (params.binary_limbs_params.limb_size_bits, params.binary_limbs_params.limb_max_value.clone())
                    } else {
                        (params.binary_limbs_bit_widths[witness_idx], params.binary_limbs_max_values[witness_idx].clone())
                    };

                    if expected_width % params.range_check_info.minimal_multiple != 0 {
                        expected_width = make_multiple(expected_width, params.range_check_info.minimal_multiple);
                        expected_max_value = (BigUint::from(1u64) << expected_width) - BigUint::from(1u64);
                    }

                    assert!(expected_width > 0);
                    if let Some(v) = limb_value.as_ref() {
                        assert!(v <= &expected_max_value);
                    }

                    assert!(expected_width % params.range_check_info.minimal_multiple == 0, 
                        "limb size must be divisible by range constraint strategy granularity");

                    // match over strategy

                    match params.range_check_info.strategy {
                        RangeConstraintStrategy::MultiTable => {
                            self::range_constraint_functions::coarsely_enforce_using_multitable(cs, var, expected_width)?;
                        },
                        RangeConstraintStrategy::SingleTableInvocation => {
                            self::single_table_range_constraint::enforce_using_single_column_table(cs, var, expected_width)?;
                        },
                        RangeConstraintStrategy::CustomTwoBitGate => {
                            let _ = create_range_constraint_chain(cs, var, expected_width)?;
                        }
                        _ => {unimplemented!("range constraint strategies other than multitable, single table or custom gate are not yet handled")}
                    }

                    let term = Term::<E>::from_allocated_num(var.clone());

                    let limb = Limb::<E>::new( 
                        term,
                        expected_max_value,
                    );

                    binary_limbs_allocated.push(limb);
                }
            }

            // keep track of base field limb
            base_field_lc.add_assign_number_with_coeff(&w, current_constant);
            current_constant.mul_assign(&shift_constant);
        }

        let base_field_limb_num = base_field_lc.into_num(cs)?;

        let base_field_term = Term::<E>::from_num(base_field_limb_num);

        let this_value = if value_is_none {
            None
        } else {
            Some(this_value)
        };

        let this_value = some_biguint_to_fe::<F>(&this_value);

        let new = Self {
            binary_limbs: binary_limbs_allocated,
            base_field_limb: base_field_term,
            representation_params: params,
            value: this_value,
        };

        if may_overflow == false {
            assert!(new.needs_reduction() == false);
        }

        Ok(new)
    }

    /// Allocate a field element from witnesses for individual binary(!) limbs,
    /// such that highest limb may be a little (up to range constraint granularity)
    /// larger than for an element that is in a field.
    #[track_caller]
    pub fn coarsely_allocate_for_known_bit_width<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        value: Option<BigUint>,
        width: usize,
        params: &'a RnsParameters<E, F>
    ) -> Result<Self, SynthesisError> {
        assert!(width > 0);
        assert!(params.binary_limbs_params.limb_size_bits % params.range_check_info.minimal_multiple == 0, 
            "limb size must be divisible by range constraint strategy granularity");

        let mut binary_limbs_allocated = Vec::with_capacity(params.num_binary_limbs);

        let mut base_field_lc = LinearCombination::<E>::zero();

        let shift_constant = params.binary_limbs_params.shift_left_by_limb_constant;
        let mut current_constant = E::Fr::one();

        let this_value = some_biguint_to_fe::<F>(&value);

        let (limb_values, limb_sizes) = slice_into_limbs_of_max_size(value, width, params.binary_limbs_params.limb_size_bits);

        let last_idx = limb_values.len() - 1;
        for (idx, (value, mut size)) in limb_values.into_iter().zip(limb_sizes.into_iter()).enumerate() {
            let value_as_fe = some_biguint_to_fe::<E::Fr>(&value);

            let a = AllocatedNum::alloc(
                cs, 
                || {
                    Ok(*value_as_fe.get()?)
                }
            )?;

            let remainder = size % params.range_check_info.minimal_multiple;

            if remainder != 0 {
                if idx == last_idx {
                    size += params.range_check_info.minimal_multiple - remainder;
                } else {
                    unreachable!("only last limb may have not strictly divisible by granularity width");
                }
            }

            let max_value = (BigUint::from(1u64) << size) - BigUint::from(1u64);

            match params.range_check_info.strategy {
                RangeConstraintStrategy::MultiTable => {
                    self::range_constraint_functions::coarsely_enforce_using_multitable(cs, &a, size)?;
                },
                RangeConstraintStrategy::SingleTableInvocation => {
                    self::single_table_range_constraint::enforce_using_single_column_table(cs, &a, size)?;
                },
                RangeConstraintStrategy::CustomTwoBitGate => {
                    let _ = create_range_constraint_chain(cs, &a, size)?;
                }
                _ => {unimplemented!("range constraint strategies other than multitable, single table or custom gate are not yet handled")}
            }

            let term = Term::<E>::from_allocated_num(a.clone());

            let limb = Limb::<E>::new( 
                term,
                max_value,
            );

            binary_limbs_allocated.push(limb);

            base_field_lc.add_assign_variable_with_coeff(&a, current_constant);
            current_constant.mul_assign(&shift_constant);
        }

        binary_limbs_allocated.resize(params.num_binary_limbs, Self::zero_limb());
        
        let base_field_limb_num = base_field_lc.into_num(cs)?;

        let base_field_term = Term::<E>::from_num(base_field_limb_num);

        let new = Self {
            binary_limbs: binary_limbs_allocated,
            base_field_limb: base_field_term,
            representation_params: params,
            value: this_value,
        };

        Ok(new)
    }

    pub fn coarsely_allocate_for_unknown_width<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        value: Option<BigUint>,
        params: &'a RnsParameters<E, F>
    ) -> Result<Self, SynthesisError> {
        if params.can_allocate_from_double_limb_witness() == true {
            let slices = Self::slice_into_double_limb_witnesses(value, cs, params, true)?;

            Self::from_double_size_limb_witnesses(cs, &slices, true, params)
        } else {
            assert!(params.binary_limbs_params.limb_size_bits % params.range_check_info.minimal_multiple == 0, 
                "limb size must be divisible by range constraint strategy granularity");

            let slices = Self::slice_into_limb_witnesses(value, cs, params)?;

            Self::coarsely_allocate_from_single_limb_witnesses(cs, &slices, true, params)
        }
    }

    pub fn from_double_size_limb_witnesses<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        witnesses: &[Num<E>],
        top_limb_may_overflow: bool,
        params: &'a RnsParameters<E, F>
    ) -> Result<Self, SynthesisError> {
        assert!(params.num_binary_limbs == 2 * witnesses.len());
        // until we make better handling of a case that top limb should be zero
        // we make sure that 
        assert!(params.num_limbs_for_in_field_representation & 1 == 0);

        let mut binary_limbs_allocated = Vec::with_capacity(params.num_binary_limbs);

        let mut base_field_lc = LinearCombination::<E>::zero();

        let mut shift_constant = params.binary_limbs_params.shift_left_by_limb_constant;
        shift_constant.square();

        let mut current_constant = E::Fr::one();

        let mut this_value = BigUint::from(0u64);
        let mut value_is_none = false;

        for (witness_idx, w) in witnesses.iter().enumerate() {
            match w {
                Num::Constant(value) => {
                    let v = fe_to_biguint(value);
                    this_value += v.clone() << (witness_idx*2*params.binary_limbs_params.limb_size_bits);

                    let limb_values = split_into_fixed_number_of_limbs(
                        v, 
                        params.binary_limbs_params.limb_size_bits, 
                        2
                    );

                    assert!(limb_values.len() == 2);

                    let low_idx = witness_idx*2;
                    let high_idx = witness_idx*2+1;

                    // there are two cases:
                    // - can not overflow and indexes are in range for in-range field element
                    // - can not overflow and indexes are NOT in range for in-range field element
                    // - can overflow

                    // we can merge first and third, so handle second first

                    if low_idx < params.num_limbs_for_in_field_representation {
                        assert!(high_idx < params.num_limbs_for_in_field_representation)
                    }

                    // if the element must fit into the field than pad with zeroes
                    if top_limb_may_overflow == false &&
                        low_idx >= params.num_limbs_for_in_field_representation && 
                        high_idx >= params.num_limbs_for_in_field_representation {

                        assert!(limb_values[0].is_zero());
                        assert!(limb_values[1].is_zero());

                        binary_limbs_allocated.push(Self::zero_limb());
                        binary_limbs_allocated.push(Self::zero_limb());

                        continue;
                    }

                    let (expected_low_width, _expected_low_max_value) = if top_limb_may_overflow {
                        (params.binary_limbs_params.limb_size_bits, params.binary_limbs_params.limb_max_value.clone())
                    } else {
                        (params.binary_limbs_bit_widths[low_idx], params.binary_limbs_max_values[low_idx].clone())
                    };

                    let (expected_high_width, _expected_high_max_value) = if top_limb_may_overflow {
                        (params.binary_limbs_params.limb_size_bits, params.binary_limbs_params.limb_max_value.clone())
                    } else {
                        (params.binary_limbs_bit_widths[high_idx], params.binary_limbs_max_values[high_idx].clone())
                    };

                    assert!(expected_low_width > 0);
                    assert!(expected_high_width > 0);

                    assert!(limb_values[0].bits() as usize <= expected_low_width);
                    assert!(limb_values[1].bits() as usize <= expected_high_width);

                    for v in limb_values.into_iter() {
                        let limb = Limb::<E>::new_constant(
                            v
                        );

                        binary_limbs_allocated.push(limb);
                    }
                },
                Num::Variable(var) => {
                    let _limb_values = if let Some(v) = var.get_value() {
                        let v = fe_to_biguint(&v);
                        this_value += v.clone() << (witness_idx*2*params.binary_limbs_params.limb_size_bits);

                        let limb_values = split_some_into_fixed_number_of_limbs(
                            Some(v), 
                            params.binary_limbs_params.limb_size_bits, 
                            2
                        );

                        limb_values
                    } else {
                        value_is_none = true;

                        vec![None; 2]
                    };

                    let low_idx = witness_idx*2;
                    let high_idx = witness_idx*2+1;

                    // there are two cases:
                    // - can not overflow and indexes are in range for in-range field element
                    // - can not overflow and indexes are NOT in range for in-range field element
                    // - can overflow

                    // we can merge first and third, so handle second first

                    if low_idx < params.num_limbs_for_in_field_representation {
                        assert!(high_idx < params.num_limbs_for_in_field_representation)
                    }

                    // if the element must fit into the field than pad with zeroes
                    if top_limb_may_overflow == false &&
                        low_idx >= params.num_limbs_for_in_field_representation && 
                        high_idx >= params.num_limbs_for_in_field_representation {

                        unreachable!("should not try to allocate a value in a field with non-constant high limbs");
                    }

                    let (expected_low_width, expected_low_max_value) = if top_limb_may_overflow {
                        (params.binary_limbs_params.limb_size_bits, params.binary_limbs_params.limb_max_value.clone())
                    } else {
                        (params.binary_limbs_bit_widths[low_idx], params.binary_limbs_max_values[low_idx].clone())
                    };

                    let (expected_high_width, expected_high_max_value) = if top_limb_may_overflow {
                        (params.binary_limbs_params.limb_size_bits, params.binary_limbs_params.limb_max_value.clone())
                    } else {
                        (params.binary_limbs_bit_widths[high_idx], params.binary_limbs_max_values[high_idx].clone())
                    };

                    assert!(expected_low_width > 0);
                    assert!(expected_high_width > 0);
                    if top_limb_may_overflow {
                        assert_eq!(expected_low_width, expected_high_width);
                    }

                    assert_eq!(params.binary_limbs_params.limb_max_value.clone(), expected_low_max_value);

                    assert!(expected_high_width & 1 == 0);
                    // if expected_high_width & 1 == 1 {
                    //     expected_high_width += 1;
                    // }

                    let expected_width = expected_high_width + params.binary_limbs_params.limb_size_bits;
                    let chain = create_range_constraint_chain(cs, var, expected_width)?;
                    assert!(expected_width % chain.len() == 0);
                    let constrained_bits_per_element = expected_width / chain.len();
                    let high_limb_idx = expected_high_width / constrained_bits_per_element - 1;
                    let high_term = Term::<E>::from_allocated_num(chain[high_limb_idx].clone());

                    let mut shift = E::Fr::one();
                    for _ in 0..params.binary_limbs_params.limb_size_bits {
                        shift.double();
                    }

                    let mut high_part_shifted_and_negated = high_term.clone();
                    high_part_shifted_and_negated.scale(&shift);
                    high_part_shifted_and_negated.negate();

                    let full_term = Term::from_allocated_num(var.clone());

                    let low_term = full_term.add(cs, &high_part_shifted_and_negated)?;

                    let low_limb = Limb::<E>::new( 
                        low_term.clone(),
                        params.binary_limbs_params.limb_max_value.clone(),
                    );

                    binary_limbs_allocated.push(low_limb);

                    let high_limb = Limb::<E>::new( 
                        high_term,
                        expected_high_max_value
                    );

                    binary_limbs_allocated.push(high_limb);
                }
            }

            // keep track of base field limb
            base_field_lc.add_assign_number_with_coeff(&w, current_constant);
            current_constant.mul_assign(&shift_constant);
        }

        let base_field_limb_num = base_field_lc.into_num(cs)?;

        let base_field_term = Term::<E>::from_num(base_field_limb_num);

        let this_value = if value_is_none {
            None
        } else {
            Some(this_value)
        };

        let this_value = some_biguint_to_fe::<F>(&this_value);

        let new = Self {
            binary_limbs: binary_limbs_allocated,
            base_field_limb: base_field_term,
            representation_params: params,
            value: this_value,
        };

        Ok(new)
    }

    pub fn new_constant(
        v: F,
        params: &'a RnsParameters<E, F>
    ) -> Self {
        let value = fe_to_biguint(&v);
        let binary_limb_values = split_into_fixed_number_of_limbs(
            value.clone(), 
            params.binary_limbs_params.limb_size_bits,
            params.num_binary_limbs
        );
        let base_limb_value = value.clone() % &params.base_field_modulus;

        let base_limb = biguint_to_fe::<E::Fr>(base_limb_value.clone());

        let mut binary_limbs_allocated = Vec::with_capacity(binary_limb_values.len());
        for l in binary_limb_values.into_iter()
        {
            let f = biguint_to_fe(l.clone());
            let term = Term::<E>::from_constant(f);
            let limb = Limb::<E>::new(
                term,
                l
            );

            binary_limbs_allocated.push(limb);
        }

        let base_limb = Term::<E>::from_constant(base_limb);

        assert_eq!(fe_to_biguint(&v) % &params.base_field_modulus, fe_to_biguint(&base_limb.get_value().unwrap()));

        Self {
            binary_limbs: binary_limbs_allocated,
            base_field_limb: base_limb,
            representation_params: params,
            value: Some(v),
        }
    }

    fn zero_limb() -> Limb<E> {
        let term = Term::<E>::from_constant(E::Fr::zero());

        let limb = Limb::<E>::new(
            term,
            BigUint::from(0u64)
        );

        limb
    }

    fn one_limb() -> Limb<E> {
        let term = Term::<E>::from_constant(E::Fr::one());

        let limb = Limb::<E>::new(
            term,
            BigUint::from(1u64)
        );

        limb
    }

    pub fn zero(
        params: &'a RnsParameters<E, F>
    ) -> Self {
        let zero_limb = Self::zero_limb();

        let binary_limbs = vec![zero_limb.clone(); params.num_binary_limbs];
    
        Self {
            binary_limbs: binary_limbs,
            base_field_limb: Term::<E>::from_constant(E::Fr::zero()),
            representation_params: params,
            value: Some(F::zero()),
        }
    }

    pub fn one(
        params: &'a RnsParameters<E, F>
    ) -> Self {
        let one_limb = Self::one_limb();
        let zero_limb = Self::zero_limb();

        let mut binary_limbs = Vec::with_capacity(params.num_binary_limbs);
        binary_limbs.push(one_limb);
        binary_limbs.resize(params.num_binary_limbs, zero_limb.clone());
    
        Self {
            binary_limbs: binary_limbs,
            base_field_limb: Term::<E>::from_constant(E::Fr::one()),
            representation_params: params,
            value: Some(F::one()),
        }
    }

    // return current value unreduced
    pub(crate) fn get_value(&self) -> Option<BigUint> {
        let shift = self.representation_params.binary_limbs_params.limb_size_bits;

        let mut result = BigUint::from(0u64);

        for l in self.binary_limbs.iter().rev() {
            if let Some(l) = l.get_value() {
                result <<= shift;
                result += l;
            } else {
                return None;
            }
        }

        Some(result)
    }

    pub fn get_field_value(&self) -> Option<F> {
        self.value
    }

    // return maximum value based on maximum limb values
    pub(crate) fn get_max_value(&self) -> BigUint {
        let shift = self.representation_params.binary_limbs_params.limb_size_bits;

        let mut result = BigUint::from(0u64);

        for l in self.binary_limbs.iter().rev() {
            result <<= shift;
            result += l.max_value();
        }

        result
    }

    pub fn is_constant(&self) -> bool {
        for l in self.binary_limbs.iter() {
            if !l.is_constant() {
                return false;
            }
        }

        self.base_field_limb.is_constant()
    }

    pub fn is_zero<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
    ) -> Result<(Boolean, Self), SynthesisError> 
    {
        let x = self;
        let x = x.reduce_if_necessary(cs)?;

        let mut lc = LinearCombination::zero();
  
        let num = x.base_field_limb.collapse_into_num(cs)?;
        let not_zero = num.is_zero(cs)?.not();
        lc.add_assign_boolean_with_coeff(&not_zero, E::Fr::one());
        
        for limb in x.binary_limbs.iter() {
            let num = limb.term.collapse_into_num(cs)?;
            let not_zero = num.is_zero(cs)?.not();
            lc.add_assign_boolean_with_coeff(&not_zero, E::Fr::one());
        }

        let num = lc.into_num(cs)?;
        // if any of the limbs !=0 then lc != 0
        let is_zero = num.is_zero(cs)?;
        
        Ok((is_zero, x))
    }

    fn is_modulus<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
    ) -> Result<(Boolean, Self), SynthesisError> 
    {
        let x = self;
        let x = x.reduce_if_necessary(cs)?;
        let params = x.representation_params;

        let mut lc = LinearCombination::zero();
  
        let num = x.base_field_limb.collapse_into_num(cs)?;
        let base_limb_of_modulus = Num::Constant(params.represented_field_modulus_in_base_field);
        let not_modulus = Num::equals(cs, &num, &base_limb_of_modulus)?.not();
        lc.add_assign_boolean_with_coeff(&not_modulus, E::Fr::one());
        
        for (limb, modulus_limb) in x.binary_limbs.iter().zip(params.represented_field_modulus_limbs.iter()) {
            let num = limb.term.collapse_into_num(cs)?;
            let limb = Num::<E>::Constant(*modulus_limb);
            let not_modulus = Num::equals(cs, &num, &limb)?.not();
            lc.add_assign_boolean_with_coeff(&not_modulus, E::Fr::one());
        }

        let num = lc.into_num(cs)?;
        // if any of the limbs !=0 then lc != 0
        let is_modulus = num.is_zero(cs)?;
        
        Ok((is_modulus, x))
    }

    pub fn negated<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS
    ) -> Result<(Self, Self), SynthesisError> {
        let (new, (_, this)) = Self::zero(&self.representation_params).sub(cs, self)?;

        Ok((new, this))
    }

    pub fn is_within_2_in_modulus_len(
        &self
    ) -> bool {
        if self.is_constant() {
            return true;
        }

        let max_value = self.get_max_value();
        let ceil = BigUint::from(1u64) << F::NUM_BITS;

        max_value < ceil
    }

    pub fn needs_reduction(
        &self
    ) -> bool {
        if self.is_constant() {
            return false;
        }

        // let's see if we ever need to reduce individual limbs into the default ranges
        // first trivial check
        let mut needs_reduction = self.get_max_value() > self.representation_params.max_representable_value();
        let max_limb_value = &self.representation_params.binary_limbs_params.limb_max_intermediate_value;
        for binary_limb in self.binary_limbs.iter() {
            needs_reduction = needs_reduction || &binary_limb.max_value() > max_limb_value;
        }

        needs_reduction
    }

    #[track_caller]
    pub fn reduce_if_necessary<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS
    ) -> Result<Self, SynthesisError> {
        if self.is_constant() {
            return Ok(self);
        }

        if self.needs_reduction() {
            return self.reduction_impl(cs);
        }

        Ok(self)
    }

    #[track_caller]
    pub fn force_reduce_into_field<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS
    ) -> Result<Self, SynthesisError> {
        self.reduction_impl(cs)
    }

    #[track_caller]
    pub(crate) fn reduction_impl<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS
    ) -> Result<Self, SynthesisError> {
        if self.is_constant() {
            return Ok(self);
        }

        let params = self.representation_params;

        // first perform actual reduction in the field that we try to represent
        let (q, rem) = if let Some(v) = self.get_value() {
            let (q, rem) = v.div_rem(&params.represented_field_modulus);
            debug_assert_eq!(fe_to_biguint(&self.get_field_value().unwrap()), rem);
            (Some(q), Some(rem))
        } else {
            (None, None)
        };
        
        let max_q_bits = (self.get_max_value() / &params.represented_field_modulus).bits() as usize;
        assert!(max_q_bits <= E::Fr::CAPACITY as usize, "for no quotient size can overflow capacity");

        let q_as_field_repr = if max_q_bits == 0 {
            Self::zero(&params)
        } else { 
            let q_as_field_repr = Self::coarsely_allocate_for_known_bit_width(
                cs,
                q, 
                max_q_bits, 
                &params
            )?;

            q_as_field_repr
        };

        let r_fe = some_biguint_to_fe::<F>(&rem);

        let r_elem = Self::new_allocated(
            cs,
            r_fe,
            params
        )?;

        assert!(r_elem.needs_reduction() == false);

        // perform constraining by implementing multiplication
        // x = q*p + r

        let one = Self::one(self.representation_params);

        Self::constraint_fma_with_multiple_additions(
            cs,
            &self, 
            &one,
            &[],
            &q_as_field_repr, 
            &[r_elem.clone()],
        )?;

        Ok(r_elem)
    }

    #[track_caller]
    pub(crate) fn strict_reduction_impl<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS
    ) -> Result<Self, SynthesisError> {
        if self.is_constant() {
            return Ok(self);
        }

        let params = self.representation_params;

        // first perform actual reduction in the field that we try to represent
        let (q, rem) = if let Some(v) = self.get_value() {
            let (q, rem) = v.div_rem(&params.represented_field_modulus);
            debug_assert_eq!(fe_to_biguint(&self.get_field_value().unwrap()), rem);
            (Some(q), Some(rem))
        } else {
            (None, None)
        };
        
        let max_q_bits = (self.get_max_value() / &params.represented_field_modulus).bits() as usize;
        assert!(max_q_bits <= E::Fr::CAPACITY as usize, "for no quotient size can overflow capacity");

        let q_as_field_repr = if max_q_bits == 0 {
            Self::zero(&params)
        } else { 
            let q_as_field_repr = Self::coarsely_allocate_for_known_bit_width(
                cs,
                q, 
                max_q_bits, 
                &params
            )?;

            q_as_field_repr
        };

        let r_fe = some_biguint_to_fe::<F>(&rem);

        let r_elem = Self::new_allocated_in_field(
            cs, 
            r_fe, 
            params
        )?;

        assert!(r_elem.needs_reduction() == false);

        // perform constraining by implementing multiplication
        // x = q*p + r

        let one = Self::one(self.representation_params);

        Self::constraint_fma_with_multiple_additions(
            cs,
            &self, 
            &one,
            &[],
            &q_as_field_repr, 
            &[r_elem.clone()],
        )?;

        Ok(r_elem)
    }

    fn slice_into_double_limb_witnesses<CS: ConstraintSystem<E>>(
        value: Option<BigUint>,
        cs: &mut CS,
        params: &RnsParameters<E, F>,
        can_overflow: bool
    ) -> Result<Vec<Num<E>>, SynthesisError> {
        assert!(params.num_binary_limbs % 2 == 0);

        if can_overflow {
            let num_witness = params.num_binary_limbs / 2;
            let witness_limbs = split_some_into_fixed_number_of_limbs(
                value, 
                params.binary_limbs_params.limb_size_bits * 2, 
                num_witness
            );

            let mut witnesses = vec![];
            for l in witness_limbs.into_iter() {
                let v = some_biguint_to_fe::<E::Fr>(&l);
                let w = AllocatedNum::alloc(cs, 
                || {
                    Ok(*v.get()?)
                })?;

                witnesses.push(Num::Variable(w));
            }

            Ok(witnesses)
        } else {
            let mut num_witness = params.num_limbs_for_in_field_representation / 2;
            if params.num_limbs_for_in_field_representation % 2 != 0 {
                num_witness += 1;
            }

            let witness_limbs = split_some_into_fixed_number_of_limbs(
                value, 
                params.binary_limbs_params.limb_size_bits * 2, 
                num_witness
            );

            let mut witnesses = vec![];
            for l in witness_limbs.into_iter() {
                let v = some_biguint_to_fe::<E::Fr>(&l);
                let w = AllocatedNum::alloc(cs, 
                || {
                    Ok(*v.get()?)
                })?;

                witnesses.push(Num::Variable(w));
            }

            witnesses.resize(
                params.num_binary_limbs / 2,
                Num::Constant(E::Fr::zero())
            );

            Ok(witnesses)
        }
    }

    fn slice_into_limb_witnesses<CS: ConstraintSystem<E>>(
        value: Option<BigUint>,
        cs: &mut CS,
        params: &RnsParameters<E, F>,
    ) -> Result<Vec<Num<E>>, SynthesisError> {
        let witness_limbs = split_some_into_fixed_number_of_limbs(
            value, 
            params.binary_limbs_params.limb_size_bits, 
            params.num_binary_limbs
        );

        let mut witnesses = vec![];
        for l in witness_limbs.into_iter() {
            let v = some_biguint_to_fe::<E::Fr>(&l);
            let w = AllocatedNum::alloc(cs, 
            || {
                Ok(*v.get()?)
            })?;

            witnesses.push(Num::Variable(w));
        }

        Ok(witnesses)
    }

    pub fn add<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
        other: Self
    ) -> Result<(Self, (Self, Self)), SynthesisError> {
        let params = self.representation_params;

        let this = self.reduce_if_necessary(cs)?;
        let other = other.reduce_if_necessary(cs)?;

        // perform addition without reduction, so it will eventually be reduced later on

        let mut new_binary_limbs = vec![];

        for (l, r) in this.binary_limbs.iter()
                        .zip(other.binary_limbs.iter()) 
        {
            let new_term = l.term.add(cs, &r.term)?;
            let new_max_value = l.max_value.clone() + &r.max_value;

            let limb = Limb::<E>::new(new_term, new_max_value);
            new_binary_limbs.push(limb);
        }

        let new_base_limb = this.base_field_limb.add(cs, &other.base_field_limb)?;

        let new_value = this.get_field_value().add(&other.get_field_value());

        let new = Self {
            binary_limbs: new_binary_limbs,
            base_field_limb: new_base_limb,
            value: new_value,
            representation_params: params
        };

        Ok((new, (this, other)))
    }

    pub fn double<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
    ) -> Result<(Self, Self), SynthesisError> {
        let params = self.representation_params;

        let this = self.reduce_if_necessary(cs)?;

        // perform addition without reduction, so it will eventually be reduced later on

        let mut two = E::Fr::one();
        two.double();

        let mut new_binary_limbs = vec![];

        for l in this.binary_limbs.iter()
        {
            let mut new_term = l.term.clone();
            new_term.scale(&two);
            let new_max_value = l.max_value.clone() * BigUint::from(2u64);

            let limb = Limb::<E>::new(new_term, new_max_value);
            new_binary_limbs.push(limb);
        }

        let mut new_base_limb = this.base_field_limb.clone();
        new_base_limb.scale(&two);

        let new_value = this.get_field_value().add(&this.get_field_value());

        let new = Self {
            binary_limbs: new_binary_limbs,
            base_field_limb: new_base_limb,
            value: new_value,
            representation_params: params
        };

        Ok((new, this))
    }

    pub fn sub<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
        other: Self
    ) -> Result<(Self, (Self, Self)), SynthesisError> {
        let params = self.representation_params;

        // subtraction is a little more involved

        // first do the constrant propagation
        if self.is_constant() && other.is_constant() {
            let tmp = self.get_field_value().sub(&other.get_field_value());

            let new = Self::new_constant(tmp.unwrap(), params);

            return Ok((new, (self, other)));
        }

        if other.is_constant() {
            let tmp = other.get_field_value().negate();

            let other_negated = Self::new_constant(tmp.unwrap(), params);

            // do the constant propagation in addition

            let (result, (this, _)) = self.add(cs, other_negated)?;

            return Ok((result, (this, other)));
        }

        let this = self.reduce_if_necessary(cs)?;
        let other = other.reduce_if_necessary(cs)?;

        // keep track for potential borrows and subtract binary limbs

        // construct data on from what positions we would borrow

        let mut borrow_max_values = vec![];
        let mut borrow_bit_widths = vec![];

        let mut previous = None;

        // let mut max_subtracted = BigUint::from(0u64);

        for l in other.binary_limbs.iter() {
            let mut max_value = l.max_value();
            if let Some(previous_shift) = previous.take() {
                max_value += BigUint::from(1u64) << (previous_shift - params.binary_limbs_params.limb_size_bits);
            }

            let borrow_bits = std::cmp::max(params.binary_limbs_params.limb_size_bits, (max_value.bits() as usize) + 1);

            borrow_max_values.push(max_value);
            borrow_bit_widths.push(borrow_bits);

            previous = Some(borrow_bits);
        }

        // now we can determine how many moduluses of the represented field 
        // we have to add to never underflow

        let shift = params.binary_limbs_params.limb_size_bits * (params.num_binary_limbs - 1);

        let mut multiples_to_add_at_least = borrow_max_values.last().unwrap().clone() << shift;
        multiples_to_add_at_least = multiples_to_add_at_least / &params.represented_field_modulus;

        let mut multiples = multiples_to_add_at_least * &params.represented_field_modulus;

        let mut loop_limit = 100;

        loop {
            let start = params.binary_limbs_params.limb_size_bits * (params.num_binary_limbs - 1);
            let end = start + params.binary_limbs_params.limb_size_bits;

            let slice = get_bit_slice(
                multiples.clone(), 
                start, 
                end
            );

            if &slice < borrow_max_values.last().unwrap() {
                multiples += &params.represented_field_modulus;
            } else {
                break;
            }
            loop_limit -= 1;
            if loop_limit == 0 {
                panic!();
            }
        }

        let multiple_slices = split_into_fixed_number_of_limbs(
            multiples.clone(), 
            params.binary_limbs_params.limb_size_bits, 
            params.num_binary_limbs
        );

        // create new limbs

        let mut previous = None;

        let last_idx = this.binary_limbs.len() - 1;

        let mut new_binary_limbs = vec![];

        let mut new_multiple = BigUint::from(0u64);

        for (idx, (((l, r), &bits), multiple)) in this.binary_limbs.iter()
                                            .zip(other.binary_limbs.iter())
                                            .zip(borrow_bit_widths.iter())
                                            .zip(multiple_slices.iter())
                                            .enumerate()
        {
            let mut tmp = BigUint::from(1u64) << bits;
            if let Some(previous_bits) = previous.take() {
                if idx != last_idx {
                    tmp -= BigUint::from(1u64) << (previous_bits - params.binary_limbs_params.limb_size_bits);
                } else {
                    tmp = BigUint::from(1u64) << (previous_bits - params.binary_limbs_params.limb_size_bits);
                }
            }
            let constant = if idx != last_idx {
                tmp + multiple
            } else {
                multiple.clone() - tmp
            };

            new_multiple += constant.clone() << (params.binary_limbs_params.limb_size_bits * idx);

            let constant_as_fe = biguint_to_fe::<E::Fr>(constant.clone());

            let mut tmp = l.term.clone();
            tmp.add_constant(&constant_as_fe);

            let mut other_negated = r.term.clone();
            other_negated.negate();

            let r = tmp.add(cs, &other_negated)?;

            let new_max_value = l.max_value() + constant;

            let limb = Limb::<E>::new(
                r,
                new_max_value
            );

            new_binary_limbs.push(limb);

            previous = Some(bits);
        }

        // let residue_to_add = multiples % &params.base_field_modulus;
        let residue_to_add = new_multiple % &params.base_field_modulus;
        let constant_as_fe = biguint_to_fe::<E::Fr>(residue_to_add.clone());

        let mut tmp = this.base_field_limb.clone();
        tmp.add_constant(&constant_as_fe);

        let mut other_negated = other.base_field_limb.clone();
        other_negated.negate();

        let new_base_limb = tmp.add(cs, &other_negated)?;

        let new_value = this.get_field_value().sub(&other.get_field_value());

        let new = Self {
            binary_limbs: new_binary_limbs,
            base_field_limb: new_base_limb,
            value: new_value,
            representation_params: params
        };

        Ok((new, (this, other)))
    }

    pub fn mul<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
        other: Self
    ) -> Result<(Self, (Self, Self)), SynthesisError> {
        let params = self.representation_params;

        let this = self.reduce_if_necessary(cs)?;
        let other = other.reduce_if_necessary(cs)?;

        if this.is_constant() && other.is_constant() {
            let r = this.get_field_value().mul(&other.get_field_value());
            let new = Self::new_constant(r.unwrap(), params);

            return Ok((new, (this, other)));
        }

        let (q, r) = match (this.get_value(), other.get_value()) {
            (Some(t), Some(o)) => {
                let value = t * o;
                let (q, r) = value.div_rem(&params.represented_field_modulus);

                (Some(q), Some(r))
            }
            _ => (None, None)
        };

        let q_elem = Self::coarsely_allocate_for_unknown_width(cs, q, params)?;


        let r_elem = Self::new_allocated(
            cs, 
            some_biguint_to_fe(&r), 
            params
        )?;

        // we constraint a * b = q*p + rem

        Self::constraint_fma_with_multiple_additions(
            cs, 
            &this,
            &other,
            &[],
            &q_elem,
            &[r_elem.clone()],
        )?;

        Ok((r_elem, (this, other)))
    }

    pub fn square<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
    ) -> Result<(Self, Self), SynthesisError> {
        let params = self.representation_params;

        let this = self.reduce_if_necessary(cs)?;

        if this.is_constant() {
            let r = this.get_field_value().mul(&this.get_field_value());
            let new = Self::new_constant(r.unwrap(), params);

            return Ok((new, this));
        }

        let (q, r) = match this.get_value() {
            Some(t) => {
                let value = t.clone() * t;
                let (q, r) = value.div_rem(&params.represented_field_modulus);

                (Some(q), Some(r))
            }
            _ => (None, None)
        };

        let q_elem = Self::coarsely_allocate_for_unknown_width(cs, q, params)?;

        let r_elem = Self::new_allocated(
            cs, 
            some_biguint_to_fe(&r), 
            params
        )?;

        // we constraint a * b = q*p + rem

        Self::constraint_square_with_multiple_additions(
            cs, 
            &this,
            &[],
            &q_elem,
            &[r_elem.clone()],
        )?;

        Ok((r_elem, this))
    }

    pub fn fma_with_addition_chain<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
        to_mul: Self,
        to_add: Vec<Self>
    ) -> Result<(Self, (Self, Self, Vec<Self>)), SynthesisError> {
        let params = self.representation_params;

        let mut final_value = self.get_field_value();
        final_value = final_value.mul(&to_mul.get_field_value());
        for a in to_add.iter() {
            final_value = final_value.add(&a.get_field_value());
        }

        let this = self.reduce_if_necessary(cs)?;
        let to_mul = to_mul.reduce_if_necessary(cs)?;

        let mut value_is_none = false;
        let mut value = BigUint::from(0u64);
        match (this.get_value(), to_mul.get_value()) {
            (Some(t), Some(m)) => {
                value += t * m;
            },
            _ => {
                value_is_none = true;
            }
        }
        
        let mut all_constants = this.is_constant() && to_mul.is_constant();
        for a in to_add.iter() {
            if let Some(v) = a.get_value() {
                value += v;
            } else {
                value_is_none = true;
            }
            all_constants = all_constants & a.is_constant();
        } 
        let (q, r) = value.div_rem(&params.represented_field_modulus);

        if all_constants {
            let r = biguint_to_fe::<F>(r);
            let new = Self::new_constant(r, params);
            return Ok((new, (this, to_mul, to_add)));
        }

        let (q, r) = if value_is_none {
            (None, None)
        } else {
            (Some(q), Some(r))
        };

        let q_elem = Self::coarsely_allocate_for_unknown_width(cs, q, params)?;

        let r_elem = Self::new_allocated(
            cs, 
            some_biguint_to_fe(&r), 
            params
        )?;

        Self::constraint_fma_with_multiple_additions(
            cs, 
            &this,
            &to_mul,
            &to_add,
            &q_elem,
            &[r_elem.clone()],
        )?;

        return Ok((r_elem, (this, to_mul, to_add)));
    }

    pub fn square_with_addition_chain<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
        to_add: Vec<Self>
    ) -> Result<(Self, (Self, Vec<Self>)), SynthesisError> {
        let params = self.representation_params;

        let mut final_value = self.get_field_value();
        final_value = final_value.mul(&self.get_field_value());
        for a in to_add.iter() {
            final_value = final_value.add(&a.get_field_value());
        }

        let this = self.reduce_if_necessary(cs)?;

        let mut value_is_none = false;
        let mut value = BigUint::from(0u64);
        match this.get_value() {
            Some(t) => {
                value += t.clone() * &t;
            },
            _ => {
                value_is_none = true;
            }
        }
        let mut all_constants = this.is_constant();
        for a in to_add.iter() {
            if let Some(v) = a.get_value() {
                value += v;
            } else {
                value_is_none = true;
            }
            all_constants = all_constants & a.is_constant();
        } 
        let (q, r) = value.div_rem(&params.represented_field_modulus);

        if all_constants {
            let r = biguint_to_fe::<F>(r);
            let new = Self::new_constant(r, params);
            return Ok((new, (this, to_add)));
        }

        let (q, r) = if value_is_none {
            (None, None)
        } else {
            (Some(q), Some(r))
        };

        let q_elem = Self::coarsely_allocate_for_unknown_width(cs, q, params)?;

        let r_elem = Self::new_allocated(
            cs, 
            some_biguint_to_fe(&r), 
            params
        )?;

        Self::constraint_square_with_multiple_additions(
            cs, 
            &this,
            &to_add,
            &q_elem,
            &[r_elem.clone()],
        )?;

        return Ok((r_elem, (this, to_add)));
    }

    #[track_caller]
    pub fn div<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
        den: Self,
    ) -> Result<(Self, (Self, Self)), SynthesisError> {
        let params = self.representation_params;
        // we do self/den = result mod p
        // so we constraint result * den = q * p + self

        // Self::div_from_addition_chain(
        //     cs,
        //     &[self.clone()],
        //     den
        // )

        // code here is duplicated a little to avoid reduction mess

        let this = self.reduce_if_necessary(cs)?;
        let den = den.reduce_if_necessary(cs)?;

        if this.is_constant() && den.is_constant() {
            let mut tmp = den.get_field_value().unwrap().inverse().unwrap();
            tmp.mul_assign(&this.get_field_value().unwrap());

            let new = Self::new_constant(tmp, params);

            return Ok((new, (this, den)));
        }

        let (_inv, result, q, _rem) = match (this.get_value(), den.get_value()) {
            (Some(this), Some(den)) => {
                let inv = mod_inverse(&den, &params.represented_field_modulus);
                let result = (this.clone() * &inv) % &params.represented_field_modulus;

                let value = den.clone() * &result - &this;
                let (q, rem) = value.div_rem(&params.represented_field_modulus);

                use crate::num_traits::Zero;
                assert!(rem.is_zero(), "remainder = {}", rem.to_str_radix(16));

                (Some(inv), Some(result), Some(q), Some(rem))
            },
            _ => {
                (None, None, None, None)
            }
        };

        let q_elem = Self::coarsely_allocate_for_unknown_width(cs, q, params)?;

        // let q_wit = Self::slice_into_double_limb_witnesses(q, cs, params, true)?;

        // let q_elem = Self::from_double_size_limb_witnesses(
        //     cs, 
        //     &q_wit, 
        //     true, 
        //     params
        // )?;

        let inv_wit = Self::new_allocated(
            cs, 
            some_biguint_to_fe::<F>(&result),
            params
        )?;

        Self::constraint_fma_with_multiple_additions(
            cs, 
            &den,
            &inv_wit,
            &[],
            &q_elem,
            &[this.clone()],
        )?;

        Ok((inv_wit, (this, den)))
    }

    #[track_caller]
    pub(crate) fn div_from_addition_chain<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        nums: Vec<Self>,
        den: Self
    ) -> Result<(Self, (Vec<Self>, Self)), SynthesisError> {
        let params = den.representation_params;

        // we do (a1 + a2 + ... + an) /den = result mod p
        // a1 + a2 + ... + an = result * den mod p
        // result*den = q*p + (a1 + a2 + ... + an)
        // so we place nums into the remainders (don't need to negate here)

        let den = den.reduce_if_necessary(cs)?;

        let mut value_is_none = false;

        let inv = if let Some(den) = den.get_value() {
            let inv = mod_inverse(&den, &params.represented_field_modulus);

            Some(inv)
        } else {
            value_is_none = true;

            None
        };

        let mut num_value = BigUint::from(0u64);
        let mut all_constant = den.is_constant();

        let mut reduced_nums = Vec::with_capacity(nums.len());

        for n in nums.into_iter() {
            let n = n.reduce_if_necessary(cs)?;
            if let Some(value) = n.get_value() {
                num_value += value;
            } else {
                value_is_none = true;
            }

            all_constant = all_constant & n.is_constant();
            reduced_nums.push(n);
        }
        let num_value = if value_is_none {
            None
        } else {
            Some(num_value)
        };

        let (result, q, _rem) = match (num_value, den.get_value(), inv.clone()) {
            (Some(num_value), Some(den), Some(inv)) => {
                let mut lhs = num_value.clone();

                let mut rhs = BigUint::from(0u64);

                let result = (num_value.clone() * &inv) % &params.represented_field_modulus;

                rhs += result.clone() * &den;
                let value = den * &result - num_value;
        
                let (q, rem) = value.div_rem(&params.represented_field_modulus);

                lhs += q.clone() * &params.represented_field_modulus;

                assert_eq!(lhs, rhs);
        
                use crate::num_traits::Zero;
                assert!(rem.is_zero(), "remainder = {}", rem.to_str_radix(16));

                (Some(result), Some(q), Some(rem))
            },
            _ => {
                (None, None, None)
            }
        };

        if all_constant {
            let v = biguint_to_fe::<F>(result.unwrap());
            let new = Self::new_constant(v, params);
            return Ok((new, (reduced_nums, den)));
        }

        let q_elem = Self::coarsely_allocate_for_unknown_width(cs, q, params)?;

        let result_wit = Self::new_allocated(
            cs, 
            some_biguint_to_fe::<F>(&result),
            params
        )?;

        Self::constraint_fma_with_multiple_additions(
            cs, 
            &den,
            &result_wit,
            &[],
            &q_elem,
            &reduced_nums,
        )?;

        Ok((result_wit, (reduced_nums, den)))
    }

    // returns first if true and second if false
    pub fn select<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        flag: &Boolean,
        first: Self,
        second: Self
    ) -> Result<(Self, (Self, Self)), SynthesisError> {
        match flag {
            Boolean::Constant(c) => {
                if *c {
                    return Ok((first.clone(), (first, second)));
                } else {
                    return Ok((second.clone(), (first, second)));
                }
            },
            _ => {}
        }

        let first = first.reduce_if_necessary(cs)?;
        let second = second.reduce_if_necessary(cs)?;

        let flag_as_term = Term::<E>::from_boolean(flag);

        // flag * a + (1-flag)*b = flag * (a-b) + b

        let mut new_binary_limbs = vec![];

        for (l, r) in first.binary_limbs.iter()
                    .zip(second.binary_limbs.iter()) 
        {
            let mut minus_b = r.term.clone();
            minus_b.negate();
            let a_minus_b = l.term.add(cs, &minus_b)?;

            let n = Term::<E>::fma(cs, &flag_as_term, &a_minus_b, &r.term)?;

            let new_max = std::cmp::max(l.max_value(), r.max_value());

            let new_limb = Limb::new(
                n,
                new_max
            );

            new_binary_limbs.push(new_limb);
        }

        let mut minus_b = second.base_field_limb.clone();
        minus_b.negate();
        let a_minus_b = first.base_field_limb.add(cs, &minus_b)?;

        let new_base_limb = Term::<E>::fma(cs, &flag_as_term, &a_minus_b, &second.base_field_limb)?;

        let new_value = if let Some(f) = flag.get_value() {
            if f {
                first.get_field_value()
            } else {
                second.get_field_value()
            }
        } else {
            None
        };

        let new = Self {
            binary_limbs: new_binary_limbs,
            base_field_limb: new_base_limb,
            value: new_value,
            representation_params: first.representation_params
        };

        Ok((new, (first, second)))
    }

    // negates if true
    pub fn conditional_negation<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        flag: &Boolean,
        this: Self,
    ) -> Result<(Self, (Self, Self)), SynthesisError> {
        let (negated, this) = this.negated(cs)?;

        let (selected, (negated, this)) = Self::select(cs, flag, negated, this)?;

        Ok((selected, (this, negated)))
    }

    fn constraint_fma_with_multiple_additions<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        mul_a: &Self,
        mul_b: &Self,
        addition_elements: &[Self],
        result_quotient: &Self,
        result_remainder_decomposition: &[Self],
    ) -> Result<(), SynthesisError> {
        // remember the schoolbook multiplication

        //  0       0       a1      a0
        // x
        //  0       0       b1      b0
        // =
        //  0      high(a1*b1)     high(a0*b0) + low(b0*a1)        low(a0*b0)
        // +
        // .... 
        // =

        // so we want to take 0th binary limb of mul_a and multiply it by 0th binary limb of b
        // and may be add something there, but if we do it naively we will not overflow the base(!)
        // field element capacity, but most likely we'll overflow a number of bits that
        // we would like to keep in the limb (params.binary_limbs_params.limb_intermediate_value_capacity)

        // so we perform the multiplication of binary limb by binary limb and immediately split it into
        // two limbs of target capacity kind of high(a0*b0) and low(a0*b0) on a picture above

        // For now this is quite generic, but in most cases we will have default-filled limbs here

        // total goal is to prove that a*b + \sum addition_elements = q * p + r
        // we transform it into the form for each limb

        // a{0} * b{0} + \sum addition_elements{0} - q{0} * p{0} - r{0}

        // next limb is more complicated
        // a{1} * b{0} + a{0} * b{1} + \sum addition_elements{1} - q{1} * p{0} - q{0} * p{1} - r{1}
        // what saves us is that p{i} are constants, so in principle we only have less multiplications

        // we also should keep in mind that single pair of limbs addition can NOT overflow two limb width
        // and we assume that all parameters are normalized, so we will later on check that "double carry"
        // is not longer than some expected value
        let params = mul_a.representation_params;

        let mut result_limbs = vec![vec![]; params.num_binary_limbs];

        let target_limbs = params.num_binary_limbs;

        let mut expected_binary_max_values = vec![vec![]; params.num_binary_limbs];

        for target in 0..target_limbs {
            let mut pairs = vec![];
            for i in 0..params.num_binary_limbs {
                for j in 0..params.num_binary_limbs {
                    if i + j == target {       
                        pairs.push((i, j));
                    }
                }
            }

            for (i, j) in pairs.into_iter() {
                // we take a and b limbs plus quotient and modulus limbs
                let mut q_limb = result_quotient.binary_limbs[i].term.clone();
                q_limb.scale(&params.represented_field_modulus_negated_limbs[j]);

                let tmp = Term::<E>::fma(cs, &mul_a.binary_limbs[i].term, &mul_b.binary_limbs[j].term, &q_limb)?;
                // also keep track of the length
                let mut max_value = mul_a.binary_limbs[i].max_value() * mul_b.binary_limbs[j].max_value();
                max_value += params.represented_field_modulus_negated_limbs_biguints[j].clone() << params.binary_limbs_params.limb_size_bits;

                result_limbs[target].push(tmp);
                expected_binary_max_values[target].push(max_value);
            }
        }

        let mut collapsed_max_values = Vec::with_capacity(expected_binary_max_values.len());

        for max_values_components in expected_binary_max_values.into_iter() {
            let mut max_value = BigUint::from(0u64);
            for c in max_values_components.into_iter() {
                max_value += c;
            }

            collapsed_max_values.push(max_value);
        }

        let params = mul_a.representation_params;

        if params.propagate_carries_using_double_limbs() {
            Self::propagate_carries_using_double_limb_approach(
                cs,
                (result_limbs, collapsed_max_values),
                addition_elements,
                result_remainder_decomposition,
                params
            )?;
        } else {
            Self::propagate_carries_using_single_limb_approach(
                cs,
                (result_limbs, collapsed_max_values),
                addition_elements,
                result_remainder_decomposition,
                params
            )?;
        }

        // now much more trivial part - multiply base field basis

        let mut minus_qp_in_base_field = result_quotient.base_field_limb.clone();
        minus_qp_in_base_field.scale(&params.represented_field_modulus_negated_in_base_field);

        let ab_in_base_field = Term::<E>::fma(cs, &mul_a.base_field_limb, &mul_b.base_field_limb, &minus_qp_in_base_field)?;

        let mut addition_chain = vec![];
        for a in addition_elements.iter() {
            addition_chain.push(a.base_field_limb.clone());
        }

        for result_remainder in result_remainder_decomposition.iter() {
            let mut negated_remainder_in_base_field = result_remainder.base_field_limb.clone();
            negated_remainder_in_base_field.negate();
            addition_chain.push(negated_remainder_in_base_field);
        }

        let must_be_zero = ab_in_base_field.add_multiple(cs, &addition_chain)?;
        let must_be_zero = must_be_zero.collapse_into_num(cs)?;

        match must_be_zero {
            Num::Constant(c) => {
                assert!(c.is_zero());
            },
            Num::Variable(var) => {
                var.assert_equal_to_constant(cs, E::Fr::zero())?;
            }
        }

        Ok(())
    }

    fn constraint_square_with_multiple_additions<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        this: &Self,
        addition_elements: &[Self],
        result_quotient: &Self,
        result_remainder_decomposition: &[Self],
    ) -> Result<(), SynthesisError> {
        let params = this.representation_params;

        let mut result_limbs = vec![vec![]; params.num_binary_limbs];

        let target_limbs = params.num_binary_limbs;

        let mut expected_binary_max_values = vec![vec![]; params.num_binary_limbs];

        for target in 0..target_limbs {
            let mut pairs = vec![];
            let mut factors = vec![];
            for i in 0..params.num_binary_limbs {
                for j in 0..params.num_binary_limbs {
                    if i + j == target {       
                        if let Some(idx) = pairs.iter().position(|el| el == &(j, i)) {
                            if i != j {
                                factors[idx] += 1;
                            }
                        } else {
                            factors.push(1);
                            pairs.push((i, j));
                        }
                    }
                }
            }

            let mut two = E::Fr::one();
            two.double();

            for (f, (i, j)) in factors.into_iter().zip(pairs.into_iter()) {
                // we take a and b limbs plus quotient and modulus limbs
                let tmp = if i == j {
                    assert!(f == 1);
                    let mut q_limb = result_quotient.binary_limbs[i].term.clone();
                    q_limb.scale(&params.represented_field_modulus_negated_limbs[j]);

                    let tmp = Term::<E>::square_with_factor_and_add(cs, &this.binary_limbs[i].term, &q_limb, &E::Fr::one())?;

                    tmp
                } else {
                    assert!(f == 2);
                    let factor = two;
                    let mut q_limb = result_quotient.binary_limbs[i].term.clone();
                    q_limb.scale(&params.represented_field_modulus_negated_limbs[j]);

                    let mut t = this.binary_limbs[j].term.clone();
                    t.scale(&factor);
                    let tmp = Term::<E>::fma(cs, &this.binary_limbs[i].term, &t, &q_limb)?;

                    tmp
                };
                result_limbs[target].push(tmp);

                // also keep track of the length
                let factor = BigUint::from(f as u64);
                let mut max_value = this.binary_limbs[i].max_value() * this.binary_limbs[j].max_value() * factor;
                if f == 1 {
                    max_value += params.represented_field_modulus_negated_limbs_biguints[j].clone() << params.binary_limbs_params.limb_size_bits;

                    expected_binary_max_values[target].push(max_value);

                } else {
                    let mut q_limb = result_quotient.binary_limbs[j].term.clone();
                    q_limb.scale(&params.represented_field_modulus_negated_limbs[i]);

                    max_value += params.represented_field_modulus_negated_limbs_biguints[j].clone() << params.binary_limbs_params.limb_size_bits;
                    max_value += params.represented_field_modulus_negated_limbs_biguints[i].clone() << params.binary_limbs_params.limb_size_bits;

                    result_limbs[target].push(q_limb);

                    expected_binary_max_values[target].push(max_value);
                }
            }
        }

        let mut collapsed_max_values = vec![];

        for max_values_components in expected_binary_max_values.into_iter()
        {
            let mut max_value = BigUint::from(0u64);
            for c in max_values_components.into_iter() {
                max_value += c;
            }

            collapsed_max_values.push(max_value);
        }

        let params = this.representation_params;

        if params.propagate_carries_using_double_limbs() {
            Self::propagate_carries_using_double_limb_approach(
                cs,
                (result_limbs, collapsed_max_values),
                addition_elements,
                result_remainder_decomposition,
                params
            )?;
        } else {
            Self::propagate_carries_using_single_limb_approach(
                cs,
                (result_limbs, collapsed_max_values),
                addition_elements,
                result_remainder_decomposition,
                params
            )?;
        }

        // now much more trivial part - multiply base field basis

        let mut minus_qp_in_base_field = result_quotient.base_field_limb.clone();
        minus_qp_in_base_field.scale(&params.represented_field_modulus_negated_in_base_field);

        let ab_in_base_field = Term::<E>::fma(cs, &this.base_field_limb, &this.base_field_limb, &minus_qp_in_base_field)?;

        let mut addition_chain = vec![];
        for a in addition_elements.iter() {
            addition_chain.push(a.base_field_limb.clone());
        }

        for result_remainder in result_remainder_decomposition.iter() {
            let mut negated_remainder_in_base_field = result_remainder.base_field_limb.clone();
            negated_remainder_in_base_field.negate();
            addition_chain.push(negated_remainder_in_base_field);
        }

        let must_be_zero = ab_in_base_field.add_multiple(cs, &addition_chain)?;
        let must_be_zero = must_be_zero.collapse_into_num(cs)?;

        match must_be_zero {
            Num::Constant(c) => {
                assert!(c.is_zero());
            },
            Num::Variable(var) => {
                var.assert_equal_to_constant(cs, E::Fr::zero())?;
            }
        }

        Ok(())
    }

    fn propagate_carries_using_double_limb_approach<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        bases: (Vec<Vec<Term<E>>>, Vec<BigUint>),
        add: &[Self],
        sub: &[Self],
        params: &RnsParameters<E, F>
    ) -> Result<(), SynthesisError> {
        // keep track of the max values after additions

        let (result_limbs, collapsed_max_values) = bases;

        let mut double_limb_max_bits = vec![];
        let mut last_single_limb_max_bits = None;

        let target_limbs = (params.num_binary_limbs >> 1) << 1;

        for i in (0..target_limbs).step_by(2) {
            let mut max_value = BigUint::from(0u64);
            max_value += &collapsed_max_values[i];
            max_value += &collapsed_max_values[i+1] << params.binary_limbs_params.limb_size_bits;
            for a in add.iter() {
                max_value += a.binary_limbs[i].max_value();
                max_value += a.binary_limbs[i+1].max_value() << params.binary_limbs_params.limb_size_bits;
            }

            let max_bits = max_value.bits() as usize;

            assert!(max_bits >= 2*params.binary_limbs_params.limb_size_bits);
            assert!(max_bits <= E::Fr::CAPACITY as usize, "max width is higher than unique representation in double limb carry propagation");

            let carry_max_bits = max_bits - 2*params.binary_limbs_params.limb_size_bits;

            double_limb_max_bits.push(carry_max_bits);
        }

        if params.num_binary_limbs & 1 == 1 {
            let idx = params.num_binary_limbs - 1;

            let mut max_value = BigUint::from(0u64);

            max_value += &collapsed_max_values[idx];
            for a in add.iter() {
                max_value += a.binary_limbs[idx].max_value();
            }

            let max_bits = max_value.bits() as usize;
            assert!(max_bits >= params.binary_limbs_params.limb_size_bits);
            assert!(max_bits <= E::Fr::CAPACITY as usize);

            let carry_max_bits = max_bits - params.binary_limbs_params.limb_size_bits;

            last_single_limb_max_bits = Some(carry_max_bits);
        }

        let shift_right_one_limb_constant = params.binary_limbs_params.shift_right_by_limb_constant;
        let mut shift_right_two_limb_constant = shift_right_one_limb_constant;
        shift_right_two_limb_constant.square();

        let shift_left_one_limb_constant = params.binary_limbs_params.shift_left_by_limb_constant;
        let mut shift_left_two_limb_constant = shift_left_one_limb_constant;
        shift_left_two_limb_constant.square();

        // propagate carries

        let mut minus_one = E::Fr::one();
        minus_one.negate();

        let mut double_limb_carries = vec![];

        let mut chunk_of_previous_carry = None;

        let last_idx = target_limbs - 1;

        for i in (0..target_limbs).step_by(2) {
            let mut contributions = vec![];

            for c in result_limbs[i].iter() {
                contributions.push(c.clone());
            }

            for c in result_limbs[i+1].iter() {
                let mut tmp = c.clone();
                tmp.scale(&shift_left_one_limb_constant);
                contributions.push(tmp);
            }

            for result_remainder in sub.iter() {
                let mut tmp = result_remainder.binary_limbs[i].term.clone();
                tmp.negate();
                contributions.push(tmp);
    
                let mut tmp = result_remainder.binary_limbs[i+1].term.clone();
                tmp.scale(&shift_left_one_limb_constant);
                tmp.negate();
                contributions.push(tmp);
            }

            for addition_element in add.iter() {
                let tmp = addition_element.binary_limbs[i].term.clone();
                contributions.push(tmp);

                let mut tmp = addition_element.binary_limbs[i+1].term.clone();
                tmp.scale(&shift_left_one_limb_constant);
                contributions.push(tmp);
            }

            if let Some(previous) = chunk_of_previous_carry.take() {
                contributions.push(previous);
            }

            // collapse contributions
            let (base, other) = contributions.split_first().unwrap();
            let mut r = base.add_multiple(cs, &other)?;

            r.scale(&shift_right_two_limb_constant);

            if i+1 == last_idx && last_single_limb_max_bits.is_none() {
                // we don't need to propagate any further
            } else {
                chunk_of_previous_carry = Some(r.clone());
            };

            double_limb_carries.push(r);
        }

        if let Some(last_bits) = last_single_limb_max_bits {
            let idx = params.num_binary_limbs - 1;

            let mut contributions = vec![];

            for c in result_limbs[idx].iter() {
                contributions.push(c.clone());
            }

            for result_remainder in sub.iter() {
                let mut tmp = result_remainder.binary_limbs[idx].term.clone();
                tmp.negate();
                contributions.push(tmp);
            }

            for addition_element in add.iter() {
                let tmp = addition_element.binary_limbs[idx].term.clone();
                contributions.push(tmp);
            }

            if let Some(previous) = chunk_of_previous_carry.take() {
                contributions.push(previous);
            }

            // collapse contributions
            let (base, other) = contributions.split_first().unwrap();
            let mut r = base.add_multiple(cs, &other)?;

            r.scale(&shift_right_one_limb_constant);

            double_limb_carries.push(r);
            double_limb_max_bits.push(last_bits);
        }

        assert!(chunk_of_previous_carry.is_none());

        assert_eq!(double_limb_carries.len(), double_limb_max_bits.len());

        // now we need to perform individual constraining

        match params.range_check_info.strategy {
            RangeConstraintStrategy::MultiTable => {
                super::range_constraint_functions::adaptively_coarsely_constraint_multiple_with_multitable(cs, &double_limb_carries, &double_limb_max_bits)?;
            },
            RangeConstraintStrategy::SingleTableInvocation => {
                super::single_table_range_constraint::adaptively_constraint_multiple_with_single_table(cs, &double_limb_carries, &double_limb_max_bits)?;
            },
            RangeConstraintStrategy::CustomTwoBitGate => {
                super::range_constraint_functions::adaptively_coarsely_constraint_multiple_with_two_bit_decomposition(cs, &double_limb_carries, &double_limb_max_bits)?;
            },
            _ => unimplemented!("other forms of range constraining are not implemented")
        }

        Ok(())
    }

    fn propagate_carries_using_single_limb_approach<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        bases: (Vec<Vec<Term<E>>>, Vec<BigUint>),
        add: &[Self],
        sub: &[Self],
        params: &RnsParameters<E, F>
    ) -> Result<(), SynthesisError> {
        let num_limbs = params.num_binary_limbs;

        // keep track of the max values after additions

        let (result_limbs, collapsed_max_values) = bases;

        let mut limb_max_bits = vec![];

        // work over max bits

        for (limb_idx, collapsed_limb_max_value) in collapsed_max_values.into_iter().enumerate() {
            let mut max_value = collapsed_limb_max_value;
            for a in add.iter() {
                max_value += a.binary_limbs[limb_idx].max_value();
            }

            let max_bits = max_value.bits() as usize;

            assert!(max_bits >= params.binary_limbs_params.limb_size_bits);
            assert!(max_bits <= E::Fr::CAPACITY as usize);

            let carry_max_bits = max_bits - params.binary_limbs_params.limb_size_bits;

            limb_max_bits.push(carry_max_bits);
        }

        let shift_right_one_limb_constant = params.binary_limbs_params.shift_right_by_limb_constant;
        // let shift_left_one_limb_constant = params.binary_limbs_params.shift_left_by_limb_constant;

        // propagate carries

        let mut minus_one = E::Fr::one();
        minus_one.negate();

        let mut carries = vec![];

        let mut chunk_of_previous_carry = None;

        for i in 0..num_limbs {
            let mut contributions = vec![];

            for c in result_limbs[i].iter() {
                contributions.push(c.clone());
            }

            for result_remainder in sub.iter() {
                let mut tmp = result_remainder.binary_limbs[i].term.clone();
                tmp.negate();
                contributions.push(tmp);
            }

            for addition_element in add.iter() {
                let tmp = addition_element.binary_limbs[i].term.clone();
                contributions.push(tmp);
            }

            if let Some(previous) = chunk_of_previous_carry.take() {
                contributions.push(previous);
            }

            // collapse contributions
            let (base, other) = contributions.split_first().unwrap();
            let mut r = base.add_multiple(cs, &other)?;

            r.scale(&shift_right_one_limb_constant);

            if i+1 == num_limbs {
                // we don't need to propagate any further
            } else {
                chunk_of_previous_carry = Some(r.clone());
            };

            carries.push(r);
        }

        assert!(chunk_of_previous_carry.is_none());

        assert_eq!(limb_max_bits.len(), carries.len());

        // now we need to perform individual constraining

        match params.range_check_info.strategy {
            RangeConstraintStrategy::MultiTable => {
                super::range_constraint_functions::adaptively_coarsely_constraint_multiple_with_multitable(cs, &carries, &limb_max_bits)?;
            },
            RangeConstraintStrategy::SingleTableInvocation => {
                super::single_table_range_constraint::adaptively_constraint_multiple_with_single_table(cs, &carries, &limb_max_bits)?;
            },
            RangeConstraintStrategy::CustomTwoBitGate => {
                super::range_constraint_functions::adaptively_coarsely_constraint_multiple_with_two_bit_decomposition(cs, &carries, &limb_max_bits)?;
            },
            _ => unimplemented!("other forms of range constraining are not implemented")
        }

        Ok(())
    }

    fn cong_factor(value: BigUint, modulus: &BigUint) -> Option<usize> {
        let mut tmp = modulus.clone();
        let mut loop_limit = 100;

        use num_traits::ToPrimitive;

        let factor = value.clone() / modulus;
        tmp += factor.clone() * modulus;
        let ff = factor.to_usize();
        if ff.is_none() {
            return None;
        }
        let mut factor = ff.unwrap();
        if factor > 16 {
            return None;
        }
        loop {
            if &tmp < &value {
                tmp += modulus;
                factor += 1;
            } else {
                break;
            }
            loop_limit -= 1;
            if loop_limit == 0 {
                panic!();
            }
        }

        Some(factor)
    }

    /// check that element is in a field and is strictly less
    /// than modulus
    pub fn enforce_is_normalized<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
    ) -> Result<Self, SynthesisError> {
        if self.is_constant() {
            return Ok(self);
        }

        let params = self.representation_params;

        let this = self.reduce_if_necessary(cs)?;

        let modulus_limbs = split_into_fixed_number_of_limbs(
            params.represented_field_modulus.clone(), 
            params.binary_limbs_params.limb_size_bits, 
            params.num_binary_limbs
        ); 

        let borrow_witnesses = if let Some(v) = this.get_value() {
            let value_limbs = split_into_fixed_number_of_limbs(
                v, 
                params.binary_limbs_params.limb_size_bits, 
                params.num_binary_limbs
            ); 
            let mut wit = Vec::with_capacity(params.num_binary_limbs - 1);

            let mut previous = None;

            for (m, v) in modulus_limbs.iter().zip(value_limbs.into_iter()).rev().skip(1).rev() {
                let mut v = v;
                if let Some(p) = previous.take() {
                    v -= p;
                }
                if &v > m {
                    wit.push(Some(true));
                    previous = Some(BigUint::from(1u64));
                } else {
                    wit.push(Some(false));
                    previous = Some(BigUint::from(0u64));
                }
            }

            assert_eq!(wit.len(), params.num_binary_limbs - 1);

            wit
        } else {
            vec![None; params.num_binary_limbs - 1]
        };

        let mut modulus_limbs_as_fe = Vec::with_capacity(modulus_limbs.len());
        for m in modulus_limbs.into_iter() {
            let m = biguint_to_fe::<E::Fr>(m);
            modulus_limbs_as_fe.push(m);
        }

        let mut borrow_bits = vec![];
        for w in borrow_witnesses.into_iter() {
            let b = Boolean::from(AllocatedBit::alloc(
                cs,
                w
            )?);
            borrow_bits.push(b)
        }

        let mut previous = None;

        let mut results = Vec::with_capacity(params.num_binary_limbs);

        for ((l, b), m) in this.binary_limbs.iter()
                            .zip(borrow_bits.into_iter())
                            .zip(modulus_limbs_as_fe.iter()) 
        {
            let mut tmp = l.term.clone();
            tmp.negate();
            tmp.add_constant(m);

            let mut this_borrow = Term::<E>::from_boolean(&b);
            this_borrow.scale(&params.binary_limbs_params.shift_left_by_limb_constant);

            if let Some(p) = previous {
                let mut previous_borrow = Term::<E>::from_boolean(&p);
                previous_borrow.negate();

                let r = tmp.add_multiple(cs, &[this_borrow, previous_borrow])?;
                results.push(r);
            } else {
                let r = tmp.add(cs, &this_borrow)?;
                results.push(r);
            }

            previous = Some(b);
        }

        assert!(previous.is_some());

        let p = previous.unwrap();

        let mut tmp = this.binary_limbs.last().unwrap().term.clone();
        tmp.negate();
        tmp.add_constant(modulus_limbs_as_fe.last().unwrap());

        let mut previous_borrow = Term::<E>::from_boolean(&p);
        previous_borrow.negate();
        let r = tmp.add(cs, &previous_borrow)?;
        results.push(r);

        for r in results.into_iter() {
            let el = r.collapse_into_num(cs)?;
            let el = el.get_variable();
            let expected_width = params.binary_limbs_params.limb_size_bits;
            match params.range_check_info.strategy {
                RangeConstraintStrategy::MultiTable => {
                    self::range_constraint_functions::coarsely_enforce_using_multitable(cs, &el, expected_width)?;
                },
                RangeConstraintStrategy::SingleTableInvocation => {
                    self::single_table_range_constraint::enforce_using_single_column_table(cs, &el, expected_width)?;
                },
                RangeConstraintStrategy::CustomTwoBitGate => {
                    let _ = create_range_constraint_chain(cs, &el, expected_width)?;
                }
                _ => {unimplemented!("range constraint strategies other than multitable, single table or custom gate are not yet handled")}
            }
        }

        Ok(this)
    }

    #[track_caller]
    pub fn enforce_equal<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        this: Self,
        other: Self
    ) -> Result<(), SynthesisError> {
        match (this.is_constant(), other.is_constant()) {
            (true, true) => {
                let a = this.get_field_value().unwrap();
                let b = other.get_field_value().unwrap();
                assert!(a == b);

                return Ok(())
            },
            _ => {

            }
        };

        let before = cs.get_current_step_number();

        let this = this.force_reduce_close_to_modulus(cs)?.enforce_is_normalized(cs)?;
        let other = other.force_reduce_close_to_modulus(cs)?.enforce_is_normalized(cs)?;

        for (a, b) in this.binary_limbs.iter().zip(other.binary_limbs.iter()) {
            let a = a.term.into_num();
            let b = b.term.into_num();
            a.enforce_equal(cs, &b)?;
        }

        let a = this.base_field_limb.into_num();
        let b = other.base_field_limb.into_num();

        a.enforce_equal(cs, &b)?;

        crate::plonk::circuit::counter::increment_counter_by(cs.get_current_step_number() - before);

        Ok(())
    }

    #[track_caller]
    pub fn special_case_enforce_not_equal<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        first: Self,
        second: Self
    ) -> Result<(Self, Self), SynthesisError> {
        match (first.get_field_value(), second.get_field_value()) {
            (Some(f), Some(s)) => {
                assert!(f != s, "values are actually equal");
            },
            _ => {}
        }

        let first = first.force_reduce_close_to_modulus(cs)?;
        let second = second.force_reduce_close_to_modulus(cs)?;

        assert!(first.is_within_2_in_modulus_len());
        assert!(second.is_within_2_in_modulus_len());

        let swap_witness = match (first.get_value(), second.get_value()) {
            (Some(first), Some(second)) => {
                Some(second > first)
            },
            _ => {
                None
            }
        };

        let swap = Boolean::from(AllocatedBit::alloc(cs, swap_witness)?);

        let (selected_first, (second, first)) = Self::select(cs, &swap, second, first)?;
        let (selected_second, (first, second)) = Self::select(cs, &swap, first, second)?;

        let (diff, _) = selected_first.sub_noborrow(cs, selected_second)?;
        // we know that binary limbs of both first and second are within range
        // 0 < q < first, second < 2^(log_2(q)) < 2q
        // so subtraction result is either 0 or q if we perform subtraction for comparison

        // if initial values were equal we either have diff == or diff == modulus

        let (diff_is_zero, diff) = diff.is_zero(cs)?;
        let (diff_is_modulus, _) = diff.is_modulus(cs)?;

        let equal = Boolean::or(cs, &diff_is_zero, &diff_is_modulus)?;
        Boolean::enforce_equal(cs, &equal, &Boolean::constant(false))?;

        Ok((first, second))
    }

    fn sub_noborrow<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
        other: Self
    ) -> Result<(Self, (Self, Self)), SynthesisError> {
        let params = self.representation_params;

        // subtraction is a little more involved

        // first do the constrant propagation
        if self.is_constant() && other.is_constant() {
            assert!(self.get_value().unwrap() >= other.get_value().unwrap());

            let tmp = self.get_field_value().sub(&other.get_field_value());

            let new = Self::new_constant(tmp.unwrap(), params);

            return Ok((new, (self, other)));
        }

        if other.is_constant() {
            unreachable!("Not yet implemented");
            // let tmp = other.get_field_value().negate();

            // let other_negated = Self::new_constant(tmp.unwrap(), params);

            // // do the constant propagation in addition

            // let (result, (this, _)) = self.add(cs, other_negated)?;

            // return Ok((result, (this, other)));
        }

        let this = self;

        let mut borrow = None;

        let mut minus_one = E::Fr::one();
        minus_one.negate();

        let mut new_binary_limbs = vec![];
        let mut new_base_limb_lc = LinearCombination::zero();

        let mut shift = 0;

        for (_idx, (((l, r), &limb_width), max_value)) in this.binary_limbs.iter()
                                            .zip(other.binary_limbs.iter())
                                            .zip(params.binary_limbs_bit_widths.iter())
                                            .zip(params.binary_limbs_max_values.iter())
                                            .enumerate()
        {
            let borrow_shift = biguint_to_fe(BigUint::from(1u64) << limb_width);
            assert_eq!(&l.max_value, max_value);
            assert_eq!(&r.max_value, max_value);
            let borrow_bit_witness = match (l.term.get_value(), r.term.get_value()) {
                (Some(l), Some(r)) => {
                    Some(l.into_repr() < r.into_repr())
                },
                _ => {
                    None
                }
            };

            let new_borrow = Boolean::from(AllocatedBit::alloc(cs, borrow_bit_witness)?);
            let mut r_term_negated = r.term.clone();
            r_term_negated.negate();

            let mut sub_result = LinearCombination::zero();
            sub_result.add_assign_term(&l.term);
            sub_result.add_assign_term(&r_term_negated);
            sub_result.add_assign_boolean_with_coeff(&new_borrow, borrow_shift);
            if let Some(borrow) = borrow.take() {
                sub_result.add_assign_boolean_with_coeff(&borrow, minus_one);
            }
            
            let sub_result = sub_result.into_num(cs)?;
            constraint_num_bits(cs, &sub_result, limb_width)?;

            new_base_limb_lc.add_assign_number_with_coeff(&sub_result, biguint_to_fe(BigUint::from(1u64) << shift));

            let term = Term::from_num(sub_result);
            let limb = Limb {
                max_value: max_value.clone(),
                term: term
            };
            new_binary_limbs.push(limb);

            shift += limb_width;
            borrow = Some(new_borrow);
        }

        let borrow = borrow.take().unwrap();
        Boolean::enforce_equal(cs, &borrow, &Boolean::Constant(false))?;

        let new_base_limb = new_base_limb_lc.into_num(cs)?;

        let new_value = this.get_field_value().sub(&other.get_field_value());

        let new = Self {
            binary_limbs: new_binary_limbs,
            base_field_limb: Term::from_num(new_base_limb),
            value: new_value,
            representation_params: params
        };

        assert_eq!(new.get_field_value().unwrap(), biguint_to_fe(new.get_value().unwrap()));

        Ok((new, (this, other)))
    }

    // #[track_caller]
    // pub fn equals<CS: ConstraintSystem<E>>(
    //     &self,
    //     cs: &mut CS,
    //     other: &Self
    // ) -> Result<Boolean, SynthesisError> {
    //     match (self.is_constant(), other.is_constant()) {
    //         (true, true) => {
    //             let a = self.get_field_value().unwrap();
    //             let b = other.get_field_value().unwrap();

    //             return Ok(Boolean::constant(a == b));
    //         },
    //         _ => {

    //         }
    //     };

    //     let before = cs.get_current_step_number();

    //     let mut lc = LinearCombination::zero();

    //     let this = self.clone().force_reduce_into_field(cs)?.enforce_is_normalized(cs)?;
    //     let other = other.clone().force_reduce_into_field(cs)?.enforce_is_normalized(cs)?;

    //     for (a, b) in this.binary_limbs.iter().zip(other.binary_limbs.iter()) {
    //         let a = a.term.into_num();
    //         let b = b.term.into_num();
    //         let not_equal = Num::equals(cs, &a, &b)?.not();
    //         lc.add_assign_boolean_with_coeff(&not_equal, E::Fr::one());
    //     }

    //     let a = this.base_field_limb.into_num();
    //     let b = other.base_field_limb.into_num();
    //     let not_equal = Num::equals(cs, &a, &b)?.not();
    //     lc.add_assign_boolean_with_coeff(&not_equal, E::Fr::one());

    //     let as_num = lc.into_num(cs)?;
    //     // if any of the terms was not equal then lc != 0
    //     let equal = as_num.is_zero(cs)?;

    //     crate::plonk::circuit::counter::increment_counter_by(cs.get_current_step_number() - before);

    //     Ok(equal)
    // }

    #[track_caller]
    pub fn force_reduce_close_to_modulus<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS
    ) -> Result<Self, SynthesisError> {
        if !self.is_within_2_in_modulus_len() {
            let reduced = self.strict_reduction_impl(cs)?;

            return Ok(reduced)
        }

        Ok(self)
    }
        
    #[track_caller]
    pub fn equals<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        this: Self,
        other: Self
    ) -> Result<(Boolean, (Self, Self)), SynthesisError> {
        match (this.is_constant(), other.is_constant()) {
            (true, true) => {
                let a = this.get_field_value().unwrap();
                let b = other.get_field_value().unwrap();

                return Ok((Boolean::constant(a == b), (this, other)));
            },
            _ => {

            }
        };

        let before = cs.get_current_step_number();

        let this = this.force_reduce_close_to_modulus(cs)?;
        let other = other.force_reduce_close_to_modulus(cs)?;

        let result = Self::equals_assuming_reduced(cs, this.clone(), other.clone())?;

        crate::plonk::circuit::counter::increment_counter_by(cs.get_current_step_number() - before);

        Ok((result, (this, other)))
    }

    #[track_caller]
    pub fn equals_assuming_reduced<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        first: Self,
        second: Self
    ) -> Result<Boolean, SynthesisError> {
        match (first.is_constant(), second.is_constant()) {
            (true, true) => {
                let a = first.get_field_value().unwrap();
                let b = second.get_field_value().unwrap();

                return Ok(Boolean::constant(a == b));
            },
            _ => {

            }
        };

        let mut lc = LinearCombination::zero();

        let this = first.enforce_is_normalized(cs)?;
        let other = second.enforce_is_normalized(cs)?;

        for (a, b) in this.binary_limbs.iter().zip(other.binary_limbs.iter()) {
            let a = a.term.collapse_into_num(cs)?;
            let b = b.term.collapse_into_num(cs)?;
            let not_equal = Num::equals(cs, &a, &b)?.not();
            lc.add_assign_boolean_with_coeff(&not_equal, E::Fr::one());
        }

        let a = this.base_field_limb.collapse_into_num(cs)?;
        let b = other.base_field_limb.collapse_into_num(cs)?;
        let not_equal = Num::equals(cs, &a, &b)?.not();
        lc.add_assign_boolean_with_coeff(&not_equal, E::Fr::one());

        let as_num = lc.into_num(cs)?;
        // if any of the terms was not equal then lc != 0
        let equal = as_num.is_zero(cs)?;

        Ok(equal)
    }

    // #[track_caller]
    // pub fn enforce_not_equal<CS: ConstraintSystem<E>>(
    //     &self,
    //     cs: &mut CS,
    //     other: &Self
    // ) -> Result<(), SynthesisError> {
    //     let equal = self.equals(cs, other)?;
    //     Boolean::enforce_equal(cs, &equal, &Boolean::constant(false))?;

    //     Ok(())
    // }

    #[track_caller]
    pub fn enforce_not_equal<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        this: Self,
        other: Self
    ) -> Result<(Self, Self), SynthesisError> {
        let this = this.force_reduce_close_to_modulus(cs)?;
        let other = other.force_reduce_close_to_modulus(cs)?;
        let equal = Self::equals_assuming_reduced(cs, this.clone(), other.clone())?;
        Boolean::enforce_equal(cs, &equal, &Boolean::constant(false))?;

        Ok((this, other))
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::plonk::circuit::*;

    #[test]
    fn test_bn_254() {
        use crate::bellman::pairing::bn256::{Fq, Bn256, Fr};

        let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

        let init_function = move || {
            let cs = TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();

            cs
        };

        test_allocation_on_random_witnesses(&params, &init_function);
        test_add_on_random_witnesses(&params, &init_function);
        test_sub_on_random_witnesses(&params, &init_function);
        test_mul_on_random_witnesses(&params, &init_function);
        test_square_on_random_witnesses(&params, &init_function);
        test_negation_on_random_witnesses(&params, &init_function);
        test_equality_on_random_witnesses(&params, &init_function);
        test_non_equality_on_random_witnesses(&params, &init_function);
        test_select_on_random_witnesses(&params, &init_function);
        test_conditional_negation_on_random_witnesses(&params, &init_function);
        test_long_addition_chain_on_random_witnesses(&params, &init_function);
        test_long_negation_chain_on_random_witnesses(&params, &init_function);
        test_long_subtraction_chain_on_random_witnesses(&params, &init_function);
        test_inv_mul_on_random_witnesses(&params, &init_function);
    }

    #[test]
    fn test_bn_254_with_multitable() {
        use crate::bellman::pairing::bn256::{Fq, Bn256, Fr};

        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        use crate::bellman::plonk::better_better_cs::cs::*;

        let (params, init_function) = {
            let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

            let over = vec![PolyIdentifier::VariablesPolynomial(0), PolyIdentifier::VariablesPolynomial(1), PolyIdentifier::VariablesPolynomial(2)];
            let table = MultiTableApplication::<Bn256>::new_range_table_of_width_3(16, over).unwrap();

            cs.add_multitable(table).unwrap();

            let strats = get_range_constraint_info(&cs);

            let params = RnsParameters::<Bn256, Fq>::new_for_field_with_strategy(
                80, 
                110, 
                4, 
                strats[0],
                true
            );

            let init_function = move || {
                cs.clone()
                // let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();
    
                // let over = vec![PolyIdentifier::VariablesPolynomial(0), PolyIdentifier::VariablesPolynomial(1), PolyIdentifier::VariablesPolynomial(2)];
                // let table = MultiTableApplication::<Bn256>::new_range_table_of_width_3(16, over).unwrap();
        
                // cs.add_multitable(table).unwrap();
    
                // cs
            };

            (params, init_function)
        };

        

        test_allocation_on_random_witnesses(&params, &init_function);
        test_add_on_random_witnesses(&params, &init_function);
        test_sub_on_random_witnesses(&params, &init_function);
        test_mul_on_random_witnesses(&params, &init_function);
        test_square_on_random_witnesses(&params, &init_function);
        test_negation_on_random_witnesses(&params, &init_function);
        test_equality_on_random_witnesses(&params, &init_function);
        test_non_equality_on_random_witnesses(&params, &init_function);
        test_select_on_random_witnesses(&params, &init_function);
        test_conditional_negation_on_random_witnesses(&params, &init_function);
        test_long_addition_chain_on_random_witnesses(&params, &init_function);
        test_long_negation_chain_on_random_witnesses(&params, &init_function);
        test_long_subtraction_chain_on_random_witnesses(&params, &init_function);
        test_inv_mul_on_random_witnesses(&params, &init_function);
    }


    #[test]
    fn test_bls_12_381() {
        use crate::bellman::pairing::bls12_381::{Bls12, Fr, Fq};

        let params = RnsParameters::<Bls12, Fq>::new_for_field(64, 110, 8);
        // let params = RnsParameters::<Bls12, Fq>::new_for_field(88, 120, 6);

        println!("Max representable = {}, with {} bits", params.max_representable_value().to_str_radix(16), params.max_representable_value().bits());

        let init_function = move || {
            let cs = TrivialAssembly::<Bls12, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

            cs
        };

        test_allocation_on_random_witnesses(&params, &init_function);
        test_add_on_random_witnesses(&params, &init_function);
        test_sub_on_random_witnesses(&params, &init_function);
        test_mul_on_random_witnesses(&params, &init_function);
        test_square_on_random_witnesses(&params, &init_function);
        test_negation_on_random_witnesses(&params, &init_function);
        test_equality_on_random_witnesses(&params, &init_function);
        test_non_equality_on_random_witnesses(&params, &init_function);
        test_select_on_random_witnesses(&params, &init_function);
        test_conditional_negation_on_random_witnesses(&params, &init_function);
        test_long_addition_chain_on_random_witnesses(&params, &init_function);
        test_long_negation_chain_on_random_witnesses(&params, &init_function);
        test_long_subtraction_chain_on_random_witnesses(&params, &init_function);
        test_inv_mul_on_random_witnesses(&params, &init_function);
    }


    fn test_mul_on_random_witnesses<E: Engine, F: PrimeField, P: PlonkConstraintSystemParams<E>, I: Fn() -> TrivialAssembly::<E, P, Width4MainGateWithDNext>>(
        params: &RnsParameters<E, F>,
        init: &I
    ){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for i in 0..100 {
            let mut cs = init();

            let a_f: F = rng.gen();
            let b_f: F = rng.gen();
            let a = FieldElement::new_allocated(
                &mut cs, 
                Some(a_f), 
                &params
            ).unwrap();

            let a_base = biguint_to_fe::<E::Fr>(fe_to_biguint(&a_f) % repr_to_biguint::<E::Fr>(&E::Fr::char()));
            assert_eq!(a_base, a.base_field_limb.get_value().unwrap());

            let b = FieldElement::new_allocated(
                &mut cs, 
                Some(b_f),
                &params
            ).unwrap();

            let b_base = biguint_to_fe::<E::Fr>(fe_to_biguint(&b_f) % repr_to_biguint::<E::Fr>(&E::Fr::char()));
            assert_eq!(b_base, b.base_field_limb.get_value().unwrap());
    
            let (result, (a, b)) = a.mul(&mut cs, b).unwrap();

            assert!(cs.is_satisfied());

            let mut m = a_f;
            m.mul_assign(&b_f);

            assert_eq!(result.value.unwrap(), m);

            assert_eq!(result.get_value().unwrap(), fe_to_biguint(&m));

            if i == 0 {
                let a = a.reduce_if_necessary(&mut cs).unwrap();
                let b = b.reduce_if_necessary(&mut cs).unwrap();
                let base = cs.n();
                use std::sync::atomic::Ordering;
                let k = super::super::RANGE_GATES_COUNTER.load(Ordering::SeqCst);
                let _ = result.mul(&mut cs, a).unwrap();
                let k = super::super::RANGE_GATES_COUNTER.load(Ordering::SeqCst) - k;
                println!("Single multiplication taken {} gates", cs.n() - base);
                println!("Range checks take {} gates", k);
            }
        }
    }

    fn test_allocation_on_random_witnesses<E: Engine, F: PrimeField, P: PlonkConstraintSystemParams<E>, I: Fn() -> TrivialAssembly::<E, P, Width4MainGateWithDNext>>(
        params: &RnsParameters<E, F>,
        init: &I
    ){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for i in 0..100 {
            let mut cs = init();

            let a_f: F = rng.gen();
            let a = FieldElement::new_allocated(
                &mut cs, 
                Some(a_f), 
                &params
            ).unwrap();

            let a_const = FieldElement::new_constant(
                a_f, 
                &params
            );

            let a_base = biguint_to_fe::<E::Fr>(fe_to_biguint(&a_f) % repr_to_biguint::<E::Fr>(&E::Fr::char()));
            assert_eq!(a_base, a.base_field_limb.get_value().unwrap());
            assert_eq!(a_base, a_const.base_field_limb.get_value().unwrap());

            for (l, r) in a.binary_limbs.iter().zip(a_const.binary_limbs.iter()) {
                assert_eq!(l.get_field_value().unwrap(), r.get_field_value().unwrap());
                assert_eq!(l.get_value().unwrap(), r.get_value().unwrap());
            }
        }
    }

    fn test_equality_on_random_witnesses<E: Engine, F: PrimeField, P: PlonkConstraintSystemParams<E>, I: Fn() -> TrivialAssembly::<E, P, Width4MainGateWithDNext>>(
        params: &RnsParameters<E, F>,
        init: &I
    ){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for i in 0..100 {
            let mut cs = init();

            let a_f: F = rng.gen();
            let a = FieldElement::new_allocated(
                &mut cs, 
                Some(a_f), 
                &params
            ).unwrap();

            let a_const = FieldElement::new_constant(
                a_f, 
                &params
            );

            let b = FieldElement::new_allocated(
                &mut cs, 
                Some(a_f), 
                &params
            ).unwrap();

            let _ = FieldElement::enforce_equal(&mut cs, a.clone(), b.clone()).unwrap();
            let _ = FieldElement::enforce_equal(&mut cs, a.clone(), a_const.clone()).unwrap();

            assert!(cs.is_satisfied());
        }
    }

    fn test_non_equality_on_random_witnesses<E: Engine, F: PrimeField, P: PlonkConstraintSystemParams<E>, I: Fn() -> TrivialAssembly::<E, P, Width4MainGateWithDNext>>(
        params: &RnsParameters<E, F>,
        init: &I
    ){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for i in 0..100 {
            let mut cs = init();

            let a_f: F = rng.gen();
            let b_f: F = rng.gen();

            let a = FieldElement::new_allocated(
                &mut cs, 
                Some(a_f), 
                &params
            ).unwrap();

            let a_const = FieldElement::new_constant(
                a_f, 
                &params
            );

            let b = FieldElement::new_allocated(
                &mut cs, 
                Some(b_f), 
                &params
            ).unwrap();

            let b_const = FieldElement::new_constant(
                b_f, 
                &params
            );

            //TODO

            // a.enforce_not_equal(&mut cs, &b).unwrap();
            // a.enforce_not_equal(&mut cs, &b_const).unwrap();
            // a_const.enforce_not_equal(&mut cs, &b_const).unwrap();

            assert!(cs.is_satisfied());
        }
    }

    fn test_negation_on_random_witnesses<E: Engine, F: PrimeField, P: PlonkConstraintSystemParams<E>, I: Fn() -> TrivialAssembly::<E, P, Width4MainGateWithDNext>>(
        params: &RnsParameters<E, F>,
        init: &I
    ){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for i in 0..100 {
            let mut cs = init();

            let a_f: F = rng.gen();
            let a = FieldElement::new_allocated(
                &mut cs, 
                Some(a_f), 
                &params
            ).unwrap();

            let mut neg = a_f;
            neg.negate();

            let n_const = FieldElement::new_constant(neg, &params);

            let (n, a) = a.negated(&mut cs).unwrap();
            assert!(n.get_value().unwrap() <= n.get_max_value());

            let n = n.reduction_impl(&mut cs).unwrap();
            let _ = FieldElement::enforce_equal(&mut cs, n.clone(), n_const.clone()).unwrap();

            let (nn, n) = n.negated(&mut cs).unwrap();
            let nn = nn.reduction_impl(&mut cs).unwrap();

            let _ = FieldElement::enforce_equal(&mut cs, nn.clone(), a.clone()).unwrap();

            assert!(cs.is_satisfied());
        }
    }

    fn test_square_on_random_witnesses<E: Engine, F: PrimeField, P: PlonkConstraintSystemParams<E>, I: Fn() -> TrivialAssembly::<E, P, Width4MainGateWithDNext>>(
        params: &RnsParameters<E, F>,
        init: &I
    ){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for i in 0..100 {
            let mut cs = init();

            let a_f: F = rng.gen();
            let b_f: F = rng.gen();
            let a = FieldElement::new_allocated(
                &mut cs, 
                Some(a_f), 
                &params
            ).unwrap();

            let a_base = biguint_to_fe::<E::Fr>(fe_to_biguint(&a_f) % repr_to_biguint::<E::Fr>(&E::Fr::char()));
            assert_eq!(a_base, a.base_field_limb.get_value().unwrap());
    
            // let (result, (a, _)) = a.square_with_addition_chain(&mut cs, vec![]).unwrap();

            let (result, a) = a.square(&mut cs).unwrap();

            assert!(cs.is_satisfied());

            let mut m = a_f;
            m.square();

            assert_eq!(result.value.unwrap(), m);

            assert_eq!(result.get_value().unwrap(), fe_to_biguint(&m));

            // let mut ab_in_base_field = a_base;
            // ab_in_base_field.mul_assign(&b_base);

            // assert_eq!(result.base_field_limb.get_value().unwrap(), ab_in_base_field);

            if i == 0 {
                let a = a.reduce_if_necessary(&mut cs).unwrap();
                let base = cs.n();
                use std::sync::atomic::Ordering;
                let k = super::super::RANGE_GATES_COUNTER.load(Ordering::SeqCst);
                let _ = a.square_with_addition_chain(&mut cs, vec![]).unwrap();
                let k = super::super::RANGE_GATES_COUNTER.load(Ordering::SeqCst) - k;
                println!("Single squaring taken {} gates", cs.n() - base);
                println!("Range checks take {} gates", k);
            }
        }
    }

    fn test_add_on_random_witnesses<E: Engine, F: PrimeField, P: PlonkConstraintSystemParams<E>, I: Fn() -> TrivialAssembly::<E, P, Width4MainGateWithDNext>>(
        params: &RnsParameters<E, F>,
        init: &I
    ){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for i in 0..100 {
            let mut cs = init();

            let a_f: F = rng.gen();
            let b_f: F = rng.gen();
            let a = FieldElement::new_allocated(
                &mut cs, 
                Some(a_f), 
                &params
            ).unwrap();

            let b = FieldElement::new_allocated(
                &mut cs, 
                Some(b_f),
                &params
            ).unwrap();

            let a_base = biguint_to_fe::<E::Fr>(fe_to_biguint(&a_f) % repr_to_biguint::<E::Fr>(&E::Fr::char()));
            let b_base = biguint_to_fe::<E::Fr>(fe_to_biguint(&b_f) % repr_to_biguint::<E::Fr>(&E::Fr::char()));

            assert_eq!(a_base, a.base_field_limb.get_value().unwrap());
            assert_eq!(b_base, b.base_field_limb.get_value().unwrap());
    
            let (result, (a, b)) = a.add(&mut cs, b).unwrap();

            assert!(cs.is_satisfied());

            let mut m = a_f;
            m.add_assign(&b_f);

            let res = result.get_value().unwrap() % repr_to_biguint::<F>(&F::char());
            assert_eq!(res, fe_to_biguint(&m));

            assert_eq!(result.value.unwrap(), m);

            // let mut ab_in_base_field = a_base;
            // ab_in_base_field.add_assign(&b_base);

            // assert_eq!(result.base_field_limb.get_value().unwrap(), ab_in_base_field);

            if i == 0 {
                let t0 = a.reduce_if_necessary(&mut cs).unwrap();
                let t1 = result.reduce_if_necessary(&mut cs).unwrap();
                assert!(t0.needs_reduction() == false);
                assert!(t1.needs_reduction() == false);
                let base = cs.n();
                let _ = t0.add(&mut cs, t1).unwrap();
                println!("Single addition taken {} gates", cs.n() - base);
            }
        }
    }


    fn test_long_addition_chain_on_random_witnesses<E: Engine, F: PrimeField, P: PlonkConstraintSystemParams<E>, I: Fn() -> TrivialAssembly::<E, P, Width4MainGateWithDNext>>(
        params: &RnsParameters<E, F>,
        init: &I
    ){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for i in 0..10 {
            let mut cs = init();

            let a_f: F = rng.gen();
            let b_f: F = rng.gen();
            let a = FieldElement::new_allocated(
                &mut cs, 
                Some(a_f), 
                &params
            ).unwrap();

            let mut t = a;

            for _ in 0..100 {
                let (tt, _) = t.clone().add(&mut cs, t).unwrap();
                t = tt;
            }

            let another = FieldElement::new_allocated(
                &mut cs, 
                t.get_field_value(), 
                &params
            ).unwrap();

            let _ = FieldElement::enforce_equal(&mut cs, another, t).unwrap();

            assert!(cs.is_satisfied());
        }
    }

    fn test_long_subtraction_chain_on_random_witnesses<E: Engine, F: PrimeField, P: PlonkConstraintSystemParams<E>, I: Fn() -> TrivialAssembly::<E, P, Width4MainGateWithDNext>>(
        params: &RnsParameters<E, F>,
        init: &I
    ){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for i in 0..10 {
            let mut cs = init();

            let a_f: F = rng.gen();
            let b_f: F = rng.gen();
            let a = FieldElement::new_allocated(
                &mut cs, 
                Some(a_f), 
                &params
            ).unwrap();

            let mut t = a;

            for _ in 0..100 {
                let (tt, _) = t.clone().sub(&mut cs, t).unwrap();
                t = tt;
            }

            let another = FieldElement::new_allocated(
                &mut cs, 
                t.get_field_value(), 
                &params
            ).unwrap();

            let _ = FieldElement::enforce_equal(&mut cs, another, t).unwrap();

            assert!(cs.is_satisfied());
        }
    }

    fn test_long_negation_chain_on_random_witnesses<E: Engine, F: PrimeField, P: PlonkConstraintSystemParams<E>, I: Fn() -> TrivialAssembly::<E, P, Width4MainGateWithDNext>>(
        params: &RnsParameters<E, F>,
        init: &I
    ){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for i in 0..10 {
            let mut cs = init();

            let a_f: F = rng.gen();
            let b_f: F = rng.gen();
            let a = FieldElement::new_allocated(
                &mut cs, 
                Some(a_f), 
                &params
            ).unwrap();

            let mut t = a;

            for _ in 0..100 {
                let (tt, _) = t.negated(&mut cs).unwrap();
                t = tt;
            }

            let another = FieldElement::new_allocated(
                &mut cs, 
                t.get_field_value(), 
                &params
            ).unwrap();

            let _ = FieldElement::enforce_equal(&mut cs, another, t).unwrap();

            assert!(cs.is_satisfied());
        }
    }

    fn test_sub_on_random_witnesses<E: Engine, F: PrimeField, P: PlonkConstraintSystemParams<E>, I: Fn() -> TrivialAssembly::<E, P, Width4MainGateWithDNext>>(
        params: &RnsParameters<E, F>,
        init: &I
    ){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for i in 0..100 {
            let mut cs = init();

            let a_f: F = rng.gen();
            let b_f: F = rng.gen();
            let a = FieldElement::new_allocated(
                &mut cs, 
                Some(a_f), 
                &params
            ).unwrap();

            let b = FieldElement::new_allocated(
                &mut cs, 
                Some(b_f),
                &params
            ).unwrap();

            let a_base = biguint_to_fe::<E::Fr>(fe_to_biguint(&a_f) % repr_to_biguint::<E::Fr>(&E::Fr::char()));
            let b_base = biguint_to_fe::<E::Fr>(fe_to_biguint(&b_f) % repr_to_biguint::<E::Fr>(&E::Fr::char()));

            assert_eq!(a_base, a.base_field_limb.get_value().unwrap());
            assert_eq!(b_base, b.base_field_limb.get_value().unwrap());
    
            let (result, (a, b)) = a.sub(&mut cs, b).unwrap();

            assert!(cs.is_satisfied());

            let mut m = a_f;
            m.sub_assign(&b_f);

            let res = result.get_value().unwrap() % repr_to_biguint::<F>(&F::char());
            assert_eq!(res, fe_to_biguint(&m));

            assert_eq!(result.value.unwrap(), m);

            let (rr, (b, a)) = b.sub(&mut cs, a).unwrap();

            let (rrr, rr) = rr.negated(&mut cs).unwrap();

            let _ = FieldElement::enforce_equal(&mut cs, rrr.clone(), result.clone()).unwrap();

            let (rrrr, rrr) = rrr.negated(&mut cs).unwrap();

            let _ = FieldElement::enforce_equal(&mut cs, rrrr, rr).unwrap();

            if i == 0 {
                let t0 = a.reduce_if_necessary(&mut cs).unwrap();
                let t1 = result.reduce_if_necessary(&mut cs).unwrap();
                let base = cs.n();
                let _ = t0.sub(&mut cs, t1).unwrap();
                println!("Single subtraction taken {} gates", cs.n() - base);
            }
        }
    }

    fn test_select_on_random_witnesses<E: Engine, F: PrimeField, P: PlonkConstraintSystemParams<E>, I: Fn() -> TrivialAssembly::<E, P, Width4MainGateWithDNext>>(
        params: &RnsParameters<E, F>,
        init: &I
    ){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for i in 0..100 {
            let mut cs = init();

            let flag: bool = rng.gen();

            use crate::plonk::circuit::boolean::AllocatedBit;

            let bit = AllocatedBit::alloc(
                &mut cs,
                Some(flag)
            ).unwrap();

            let bit = Boolean::Not(bit);
            // let bit = Boolean::Is(bit);

            let a_f: F = rng.gen();
            let b_f: F = rng.gen();
            let a = FieldElement::new_allocated(
                &mut cs, 
                Some(a_f), 
                &params
            ).unwrap();

            let b = FieldElement::new_allocated(
                &mut cs, 
                Some(b_f),
                &params
            ).unwrap();

            let a_base = biguint_to_fe::<E::Fr>(fe_to_biguint(&a_f) % repr_to_biguint::<E::Fr>(&E::Fr::char()));
            let b_base = biguint_to_fe::<E::Fr>(fe_to_biguint(&b_f) % repr_to_biguint::<E::Fr>(&E::Fr::char()));

            assert_eq!(a_base, a.base_field_limb.get_value().unwrap());
            assert_eq!(b_base, b.base_field_limb.get_value().unwrap());
    
            let (result, (a, b)) = FieldElement::select(&mut cs, &bit, a, b).unwrap();

            assert!(cs.is_satisfied());

            let m = if !flag {
                a_f
            }  else {
                b_f
            };

            let res = result.get_value().unwrap() % repr_to_biguint::<F>(&F::char());
            assert_eq!(res, fe_to_biguint(&m));

            assert_eq!(result.value.unwrap(), m);

            if i == 0 {
                let t0 = a.reduce_if_necessary(&mut cs).unwrap();
                let t1 = result.reduce_if_necessary(&mut cs).unwrap();
                let base = cs.n();
                let _ = FieldElement::select(&mut cs, &bit, t0, t1).unwrap();
                println!("Single selection taken {} gates", cs.n() - base);
            }
        }
    }

    fn test_conditional_negation_on_random_witnesses<E: Engine, F: PrimeField, P: PlonkConstraintSystemParams<E>, I: Fn() -> TrivialAssembly::<E, P, Width4MainGateWithDNext>>(
        params: &RnsParameters<E, F>,
        init: &I
    ){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for i in 0..100 {
            let mut cs = init();

            let flag: bool = rng.gen();

            use crate::plonk::circuit::boolean::AllocatedBit;

            let bit = AllocatedBit::alloc(
                &mut cs,
                Some(flag)
            ).unwrap();

            let bit = Boolean::Not(bit);
            // let bit = Boolean::Is(bit);

            let a_f: F = rng.gen();
            let a = FieldElement::new_allocated(
                &mut cs, 
                Some(a_f), 
                &params
            ).unwrap();

            let a_base = biguint_to_fe::<E::Fr>(fe_to_biguint(&a_f) % repr_to_biguint::<E::Fr>(&E::Fr::char()));

            assert_eq!(a_base, a.base_field_limb.get_value().unwrap());

            let (result, (a, minus_a)) = FieldElement::conditional_negation(&mut cs, &bit, a).unwrap();

            let mut minus_a_f = a_f;
            minus_a_f.negate();

            assert_eq!(minus_a.get_field_value().unwrap(), minus_a_f);
            assert_eq!(a.get_field_value().unwrap(), a_f);

            assert_eq!(minus_a.get_value().unwrap() % repr_to_biguint::<F>(&F::char()), fe_to_biguint(&minus_a_f));
            assert_eq!(a.get_value().unwrap() % repr_to_biguint::<F>(&F::char()), fe_to_biguint(&a_f));

            assert!(cs.is_satisfied());

            let m = if flag {
                a_f
            }  else {
                minus_a_f
            };

            let res = result.get_value().unwrap() % repr_to_biguint::<F>(&F::char());
            assert_eq!(res, fe_to_biguint(&m));

            assert_eq!(result.value.unwrap(), m);

            if i == 0 {
                let t0 = a.reduce_if_necessary(&mut cs).unwrap();
                let base = cs.n();
                let _ = FieldElement::conditional_negation(&mut cs, &bit, t0).unwrap();
                println!("Conditional negation taken {} gates", cs.n() - base);
            }
        }
    }

    fn test_inv_mul_on_random_witnesses<E: Engine, F: PrimeField, P: PlonkConstraintSystemParams<E>, I: Fn() -> TrivialAssembly::<E, P, Width4MainGateWithDNext>>(
        params: &RnsParameters<E, F>,
        init: &I
    ){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for i in 0..100 {
            let mut cs = init();

            let a_f: F = rng.gen();
            let b_f: F = rng.gen();
            let a = FieldElement::new_allocated(
                &mut cs, 
                Some(a_f), 
                &params
            ).unwrap();

            let a_base = biguint_to_fe::<E::Fr>(fe_to_biguint(&a_f) % repr_to_biguint::<E::Fr>(&E::Fr::char()));
            assert_eq!(a_base, a.base_field_limb.get_value().unwrap());

            let b = FieldElement::new_allocated(
                &mut cs, 
                Some(b_f),
                &params
            ).unwrap();

            let b_base = biguint_to_fe::<E::Fr>(fe_to_biguint(&b_f) % repr_to_biguint::<E::Fr>(&E::Fr::char()));
            assert_eq!(b_base, b.base_field_limb.get_value().unwrap());
    
            let (result, (a, b)) = a.div(&mut cs, b).unwrap();

            assert!(cs.is_satisfied());

            let mut m = b_f.inverse().unwrap();
            m.mul_assign(&a_f);

            assert_eq!(result.value.unwrap(), m);

            assert_eq!(result.get_value().unwrap(), fe_to_biguint(&m));

            // let mut ab_in_base_field = a_base;
            // ab_in_base_field.mul_assign(&b_base);

            // assert_eq!(result.base_field_limb.get_value().unwrap(), ab_in_base_field);

            // if i == 0 {
            //     let a = a.reduce_if_necessary(&mut cs).unwrap();
            //     let b = b.reduce_if_necessary(&mut cs).unwrap();
            //     let base = cs.n();
            //     use std::sync::atomic::Ordering;
            //     let k = super::super::RANGE_GATES_COUNTER.load(Ordering::SeqCst);
            //     let _ = result.mul(&mut cs, &result).unwrap();
            //     let k = super::super::RANGE_GATES_COUNTER.load(Ordering::SeqCst) - k;
            //     println!("Single multiplication taken {} gates", cs.n() - base);
            //     println!("Range checks take {} gates", k);
            // }
        }
    }

    #[test]
    fn test_rns_params_for_advanced_strategies() {
        type E = crate::bellman::pairing::bn256::Bn256;
        type Fr = crate::bellman::pairing::bn256::Fr;
        type Fq = crate::bellman::pairing::bn256::Fq;

        use crate::bellman::plonk::better_better_cs::cs::*;

        let mut cs = TrivialAssembly::<E, Width4WithCustomGates, Width4MainGateWithDNext>::new();

        let over = vec![PolyIdentifier::VariablesPolynomial(0), PolyIdentifier::VariablesPolynomial(1), PolyIdentifier::VariablesPolynomial(2)];
        let table = MultiTableApplication::<E>::new_range_table_of_width_3(16, over).unwrap();

        cs.add_multitable(table).unwrap();

        let strategies = get_range_constraint_info(&cs);

        let params = RnsParameters::<E, Fq>::new_for_field_with_strategy(
            96, 
            110,
            3,
            strategies[0],
            false
        );

        println!("Max representable = {}, with {} bits", params.max_representable_value().to_str_radix(16), params.max_representable_value().bits());
    }

    #[test]
    #[should_panic(expected = "limb size is not a multiple of range check quant")]
    fn test_rns_params_for_advanced_strategies_with_mismatched_parameters() {
        type E = crate::bellman::pairing::bn256::Bn256;
        type Fr = crate::bellman::pairing::bn256::Fr;
        type Fq = crate::bellman::pairing::bn256::Fq;

        use crate::bellman::plonk::better_better_cs::cs::*;

        let mut cs = TrivialAssembly::<E, Width4WithCustomGates, Width4MainGateWithDNext>::new();

        let over = vec![PolyIdentifier::VariablesPolynomial(0), PolyIdentifier::VariablesPolynomial(1), PolyIdentifier::VariablesPolynomial(2)];
        let table = MultiTableApplication::<E>::new_range_table_of_width_3(16, over).unwrap();

        cs.add_multitable(table).unwrap();

        let strategies = get_range_constraint_info(&cs);

        let params = RnsParameters::<E, Fq>::new_for_field_with_strategy(
            68, 
            110,
            4,
            strategies[0],
            false
        );
    }

    // #[test]
    // fn test_addition_chain_1_inv_mul_on_random_witnesses(){
    //     use rand::{XorShiftRng, SeedableRng, Rng};
    //     let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    //     let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

    //     println!("Max representable = {}, with {} bits", params.max_representable_value().to_str_radix(16), params.max_representable_value().bits());

    //     for i in 0..100 {
    //         let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

    //         let a_f0: Fq = rng.gen();

    //         let a_f = a_f0;

    //         let b_f: Fq = rng.gen();
    //         let a_0 = FieldElement::new_allocated(
    //             &mut cs, 
    //             Some(a_f0), 
    //             &params
    //         ).unwrap();

    //         let b = FieldElement::new_allocated(
    //             &mut cs, 
    //             Some(b_f),
    //             &params
    //         ).unwrap();

    //         let mut m = b_f.inverse().unwrap();
    //         m.mul_assign(&a_f);

    //         let (result, (_, b)) = FieldElement::div_from_addition_chain(&mut cs, vec![a_0], b).unwrap();

    //         assert!(cs.is_satisfied());

    //         assert_eq!(result.value.unwrap(), m);

    //         assert_eq!(result.get_value().unwrap(), fe_to_biguint(&m));

    //         // let mut ab_in_base_field = a_base;
    //         // ab_in_base_field.mul_assign(&b_base);

    //         // assert_eq!(result.base_field_limb.get_value().unwrap(), ab_in_base_field);

    //         // if i == 0 {
    //         //     let a = a.reduce_if_necessary(&mut cs).unwrap();
    //         //     let b = b.reduce_if_necessary(&mut cs).unwrap();
    //         //     let base = cs.n();
    //         //     use std::sync::atomic::Ordering;
    //         //     let k = super::super::RANGE_GATES_COUNTER.load(Ordering::SeqCst);
    //         //     let _ = result.mul(&mut cs, &result).unwrap();
    //         //     let k = super::super::RANGE_GATES_COUNTER.load(Ordering::SeqCst) - k;
    //         //     println!("Single multiplication taken {} gates", cs.n() - base);
    //         //     println!("Range checks take {} gates", k);
    //         // }
    //     }
    // }


    // #[test]
    // fn test_addition_chain_1_inv_mul_semi_constant_on_random_witnesses(){
    //     use rand::{XorShiftRng, SeedableRng, Rng};
    //     let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    //     let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

    //     println!("Max representable = {}, with {} bits", params.max_representable_value().to_str_radix(16), params.max_representable_value().bits());

    //     for i in 0..100 {
    //         let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

    //         let a_f0: Fq = rng.gen();

    //         let a_f = a_f0;

    //         let b_f: Fq = rng.gen();
    //         let a_0 = FieldElement::new_constant(
    //             a_f0, 
    //             &params
    //         );

    //         let b = FieldElement::new_allocated(
    //             &mut cs, 
    //             Some(b_f),
    //             &params
    //         ).unwrap();

    //         let mut m = b_f.inverse().unwrap();
    //         m.mul_assign(&a_f);

    //         let (result, (_, b)) = FieldElement::div_from_addition_chain(&mut cs, vec![a_0], b).unwrap();

    //         assert!(cs.is_satisfied());

    //         assert_eq!(result.value.unwrap(), m);

    //         assert_eq!(result.get_value().unwrap(), fe_to_biguint(&m));

    //         // let mut ab_in_base_field = a_base;
    //         // ab_in_base_field.mul_assign(&b_base);

    //         // assert_eq!(result.base_field_limb.get_value().unwrap(), ab_in_base_field);

    //         // if i == 0 {
    //         //     let a = a.reduce_if_necessary(&mut cs).unwrap();
    //         //     let b = b.reduce_if_necessary(&mut cs).unwrap();
    //         //     let base = cs.n();
    //         //     use std::sync::atomic::Ordering;
    //         //     let k = super::super::RANGE_GATES_COUNTER.load(Ordering::SeqCst);
    //         //     let _ = result.mul(&mut cs, &result).unwrap();
    //         //     let k = super::super::RANGE_GATES_COUNTER.load(Ordering::SeqCst) - k;
    //         //     println!("Single multiplication taken {} gates", cs.n() - base);
    //         //     println!("Range checks take {} gates", k);
    //         // }
    //     }
    // }

    // #[test]
    // fn test_addition_chain_2_inv_mul_on_random_witnesses(){
    //     use rand::{XorShiftRng, SeedableRng, Rng};
    //     let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    //     let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

    //     println!("Max representable = {}, with {} bits", params.max_representable_value().to_str_radix(16), params.max_representable_value().bits());

    //     for i in 0..100 {
    //         let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

    //         let a_f0: Fq = rng.gen();
    //         let a_f1: Fq = rng.gen();

    //         let mut a_f = a_f0;
    //         a_f.add_assign(&a_f1);

    //         let b_f: Fq = rng.gen();
    //         let a_0 = FieldElement::new_allocated(
    //             &mut cs, 
    //             Some(a_f0), 
    //             &params
    //         ).unwrap();

    //         let a_1 = FieldElement::new_allocated(
    //             &mut cs, 
    //             Some(a_f1), 
    //             &params
    //         ).unwrap();

    //         let b = FieldElement::new_allocated(
    //             &mut cs, 
    //             Some(b_f),
    //             &params
    //         ).unwrap();

    //         let mut m = b_f.inverse().unwrap();
    //         m.mul_assign(&a_f);
    
    //         let (result, (_, b)) = FieldElement::div_from_addition_chain(&mut cs, vec![a_0, a_1], b).unwrap();

    //         assert!(cs.is_satisfied());

    //         assert_eq!(result.value.unwrap(), m);

    //         assert_eq!(result.get_value().unwrap(), fe_to_biguint(&m));

    //         // let mut ab_in_base_field = a_base;
    //         // ab_in_base_field.mul_assign(&b_base);

    //         // assert_eq!(result.base_field_limb.get_value().unwrap(), ab_in_base_field);

    //         // if i == 0 {
    //         //     let a = a.reduce_if_necessary(&mut cs).unwrap();
    //         //     let b = b.reduce_if_necessary(&mut cs).unwrap();
    //         //     let base = cs.n();
    //         //     use std::sync::atomic::Ordering;
    //         //     let k = super::super::RANGE_GATES_COUNTER.load(Ordering::SeqCst);
    //         //     let _ = result.mul(&mut cs, &result).unwrap();
    //         //     let k = super::super::RANGE_GATES_COUNTER.load(Ordering::SeqCst) - k;
    //         //     println!("Single multiplication taken {} gates", cs.n() - base);
    //         //     println!("Range checks take {} gates", k);
    //         // }
    //     }
    // }

    // #[test]
    // fn test_addition_chain_2_inv_mul_semi_constant_on_random_witnesses(){
    //     use rand::{XorShiftRng, SeedableRng, Rng};
    //     let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    //     let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

    //     println!("Max representable = {}, with {} bits", params.max_representable_value().to_str_radix(16), params.max_representable_value().bits());

    //     for i in 0..100 {
    //         let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

    //         let a_f0: Fq = rng.gen();
    //         let a_f1: Fq = rng.gen();

    //         let mut a_f = a_f0;
    //         a_f.add_assign(&a_f1);

    //         let b_f: Fq = rng.gen();
    //         let a_0 = FieldElement::new_allocated(
    //             &mut cs, 
    //             Some(a_f0), 
    //             &params
    //         ).unwrap();

    //         let a_1 = FieldElement::new_constant(
    //             a_f1, 
    //             &params
    //         );

    //         let b = FieldElement::new_allocated(
    //             &mut cs, 
    //             Some(b_f),
    //             &params
    //         ).unwrap();

    //         let mut m = b_f.inverse().unwrap();
    //         m.mul_assign(&a_f);
    
    //         let (result, (_, b)) = FieldElement::div_from_addition_chain(&mut cs, vec![a_0, a_1], b).unwrap();

    //         assert!(cs.is_satisfied());

    //         assert_eq!(result.value.unwrap(), m);

    //         assert_eq!(result.get_value().unwrap(), fe_to_biguint(&m));

    //         // let mut ab_in_base_field = a_base;
    //         // ab_in_base_field.mul_assign(&b_base);

    //         // assert_eq!(result.base_field_limb.get_value().unwrap(), ab_in_base_field);

    //         // if i == 0 {
    //         //     let a = a.reduce_if_necessary(&mut cs).unwrap();
    //         //     let b = b.reduce_if_necessary(&mut cs).unwrap();
    //         //     let base = cs.n();
    //         //     use std::sync::atomic::Ordering;
    //         //     let k = super::super::RANGE_GATES_COUNTER.load(Ordering::SeqCst);
    //         //     let _ = result.mul(&mut cs, &result).unwrap();
    //         //     let k = super::super::RANGE_GATES_COUNTER.load(Ordering::SeqCst) - k;
    //         //     println!("Single multiplication taken {} gates", cs.n() - base);
    //         //     println!("Range checks take {} gates", k);
    //         // }
    //     }
    // }

    // #[test]
    // fn test_addition_chain_2_inv_mul_non_normalized_on_random_witnesses(){
    //     use rand::{XorShiftRng, SeedableRng, Rng};
    //     let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    //     let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

    //     println!("Max representable = {}, with {} bits", params.max_representable_value().to_str_radix(16), params.max_representable_value().bits());

    //     for i in 0..100 {
    //         let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

    //         let a_f0: Fq = rng.gen();
    //         let a_f1: Fq = rng.gen();

    //         let mut a_f = a_f0;
    //         a_f.sub_assign(&a_f1);

    //         let b_f0: Fq = rng.gen();
    //         let b_f1: Fq = rng.gen();

    //         let mut b_f = b_f0;
    //         b_f.sub_assign(&b_f1);

    //         let a_0 = FieldElement::new_allocated(
    //             &mut cs, 
    //             Some(a_f0), 
    //             &params
    //         ).unwrap();

    //         let a_1 = FieldElement::new_allocated(
    //             &mut cs, 
    //             Some(a_f1), 
    //             &params
    //         ).unwrap();

    //         let (a_1, _) = a_1.negated(&mut cs).unwrap();

    //         let b_0 = FieldElement::new_allocated(
    //             &mut cs, 
    //             Some(b_f0),
    //             &params
    //         ).unwrap();

    //         let b_1 = FieldElement::new_allocated(
    //             &mut cs, 
    //             Some(b_f1),
    //             &params
    //         ).unwrap();

    //         let (b_1, _) = b_1.negated(&mut cs).unwrap();

    //         let (b, (b_0, b_1)) = b_0.add(&mut cs, b_1).unwrap();
    //         let (b, (_, b_1)) = b.add(&mut cs, b_1).unwrap();
    //         let (b, (_, b_1)) = b.add(&mut cs, b_1).unwrap();
    //         let (b, (_, b_1)) = b.add(&mut cs, b_1).unwrap();

    //         let mut m = b_f.inverse().unwrap();
    //         m.mul_assign(&a_f);
    
    //         let (result, _) = FieldElement::div_from_addition_chain(&mut cs, vec![a_0, a_1], b).unwrap();

    //         assert!(cs.is_satisfied());

    //         // assert_eq!(result.get_field_value().unwrap(), m);

    //         // assert_eq!(result.get_value().unwrap() % &params.represented_field_modulus, fe_to_biguint(&m));

    //         // assert_eq!(result.get_value().unwrap(), fe_to_biguint(&m));
    //     }
    // }


    // #[test]
    // fn test_addition_chain_2_inv_mul_non_normalized_semi_constant_on_random_witnesses(){
    //     use rand::{XorShiftRng, SeedableRng, Rng};
    //     let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    //     let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

    //     println!("Max representable = {}, with {} bits", params.max_representable_value().to_str_radix(16), params.max_representable_value().bits());

    //     for i in 0..100 {
    //         let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

    //         let a_f0: Fq = rng.gen();
    //         let a_f1: Fq = rng.gen();

    //         let mut a_f = a_f0;
    //         a_f.double();
    //         a_f.double();
    //         a_f.sub_assign(&a_f1);

    //         let b_f0: Fq = rng.gen();
    //         let b_f1: Fq = rng.gen();

    //         let mut b_f = b_f0;
    //         b_f.sub_assign(&b_f1);

    //         let a_0 = FieldElement::new_allocated(
    //             &mut cs, 
    //             Some(a_f0), 
    //             &params
    //         ).unwrap();

    //         let (a_0, _) = a_0.clone().add(&mut cs, a_0).unwrap();
    //         let (a_0, _) = a_0.clone().add(&mut cs, a_0).unwrap();

    //         let a_1 = FieldElement::new_constant(
    //             a_f1, 
    //             &params
    //         );

    //         let (a_1, _) = a_1.negated(&mut cs).unwrap();

    //         let b_0 = FieldElement::new_allocated(
    //             &mut cs, 
    //             Some(b_f0),
    //             &params
    //         ).unwrap();

    //         let b_1 = FieldElement::new_constant(
    //             b_f1,
    //             &params
    //         );

    //         let (b_1, _) = b_1.negated(&mut cs).unwrap();

    //         let (b, _) = b_0.add(&mut cs, b_1).unwrap();

    //         let mut m = b_f.inverse().unwrap();
    //         m.mul_assign(&a_f);
    
    //         let (result, (_, b)) = FieldElement::div_from_addition_chain(&mut cs, vec![a_0, a_1], b).unwrap();

    //         assert!(cs.is_satisfied());

    //         assert_eq!(result.get_field_value().unwrap(), m);

    //         assert_eq!(result.get_value().unwrap() % &params.represented_field_modulus, fe_to_biguint(&m));

    //         assert_eq!(result.get_value().unwrap(), fe_to_biguint(&m));
    //     }
    // }

    //  0*3           0*2           0*1           0*0
    //  1*2           1*1           1*0
    //  2*1           2*0
    //  3*0

}