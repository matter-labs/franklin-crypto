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
    Width4MainGateWithDNextEquation,
    MainGateEquation,
    GateEquationInternal,
    GateEquation,
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
use super::super::boolean::Boolean;
use crate::circuit::SomeField;

use super::*;
use super::bigint::*;
use num_bigint::BigUint;
use num_integer::Integer;

// Parameters of the representation
#[derive(Clone, Debug)]
pub struct RnsParameters<E: Engine, F: PrimeField>{
    // this is kind-of normal UintX limbs
    pub binary_limbs_params: LimbedRepresentationParameters<E>,
    pub num_binary_limbs: usize,
    pub binary_modulus: BigUint,
    // we can not multiply by power of modulus of our base field E,
    // so we keep only one single limb

    pub base_field_limb_params: LimbedRepresentationParameters<E>,
    pub num_base_field_limb: usize,
    // convenience
    pub base_field_modulus: BigUint,
    pub base_field_max_val: BigUint,
    pub binary_representation_max_value: BigUint,

    // modulus if the field that we represent
    // we know the modulus and how large will be limbs in the base case
    // of maximally filled distribution
    pub represented_field_modulus: BigUint,
    pub binary_limbs_bit_widths: Vec<usize>,
    pub binary_limbs_max_values: Vec<BigUint>,

    pub last_binary_limb_bit_width: usize,
    pub last_binary_limb_max_value: BigUint,

    // we do modular reductions, so we want to have these for convenience
    pub represented_field_modulus_negated_limbs_biguints: Vec<BigUint>,
    pub represented_field_modulus_negated_limbs: Vec<E::Fr>,

    // -modulus of represented field in base field
    pub represented_field_modulus_negated_in_base_field: E::Fr,

    pub limb_witness_size: usize,

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
        let binary_limbs_params = LimbedRepresentationParameters::new(limb_size, intermediate_limb_capacity);

        assert!(num_binary_limbs & 1 == 0);

        let base_field_limb_params = LimbedRepresentationParameters::new(F::NUM_BITS as usize, F::NUM_BITS as usize);
        let num_base_field_limb = 1;

        let base_field_modulus = repr_to_biguint::<E::Fr>(&E::Fr::char());
        let binary_modulus = BigUint::from(1u64) << (num_binary_limbs * limb_size);
        let binary_representation_max_value = binary_modulus.clone() - BigUint::from(1u64);

        let represented_field_modulus = repr_to_biguint::<F>(&F::char());

        let represented_modulus_negated_modulo_binary = binary_modulus.clone() - &represented_field_modulus;

        let mask = BigUint::from(1u64) << limb_size;

        let mut modulus_limbs_bit_widths = vec![];
        let mut modulus_limbs_chunks = vec![];

        let mut tmp = represented_field_modulus.clone();

        for _ in 0..num_binary_limbs {
            let chunk = tmp.clone() % &mask;
            modulus_limbs_bit_widths.push(chunk.bits());
            modulus_limbs_chunks.push(chunk.clone());
            tmp >>= limb_size;
        }

        let mut last_limb_bits = *modulus_limbs_bit_widths.last().unwrap();
        if last_limb_bits & 1 == 1 {
            last_limb_bits += 1;
        }
        let mut binary_limbs_bit_widths = vec![limb_size; num_binary_limbs - 1];
        binary_limbs_bit_widths.push(last_limb_bits);
        
        let mut binary_limbs_max_values = vec![binary_limbs_params.limb_max_value.clone(); num_binary_limbs - 1];
        binary_limbs_max_values.push((BigUint::from(1u64) << last_limb_bits) - BigUint::from(1u64));

        let mut tmp = represented_modulus_negated_modulo_binary.clone();

        let mut negated_modulus_chunks_bit_width = vec![];
        let mut negated_modulus_chunks = vec![];
        let mut represented_field_modulus_negated_limbs = vec![];

        for _ in 0..num_binary_limbs {
            let chunk = tmp.clone() % &mask;
            negated_modulus_chunks_bit_width.push(chunk.bits());
            negated_modulus_chunks.push(chunk.clone());
            let fe = biguint_to_fe::<E::Fr>(chunk);
            represented_field_modulus_negated_limbs.push(fe);
            tmp >>= limb_size;
        }

        let repr_modulus_negated = base_field_modulus.clone() - (represented_field_modulus.clone() % &base_field_modulus.clone());
        let repr_modulus_negated = biguint_to_fe(repr_modulus_negated);

        Self {
            binary_limbs_params,
            num_binary_limbs,
            binary_modulus,
            base_field_limb_params,
            num_base_field_limb,
            base_field_modulus: base_field_modulus.clone(),
            base_field_max_val: base_field_modulus - BigUint::from(1u64),
            binary_representation_max_value,
            represented_field_modulus,
            binary_limbs_bit_widths: binary_limbs_bit_widths.clone(),
            binary_limbs_max_values: binary_limbs_max_values.clone(),
            represented_field_modulus_negated_limbs_biguints : negated_modulus_chunks,
            represented_field_modulus_negated_limbs,
            limb_witness_size: 2,
            last_binary_limb_bit_width: binary_limbs_bit_widths.pop().unwrap(),
            last_binary_limb_max_value: binary_limbs_max_values.pop().unwrap(),
            represented_field_modulus_negated_in_base_field: repr_modulus_negated,
            _marker: std::marker::PhantomData
        }
    }
}

#[derive(Clone, Debug)]
pub struct FieldElement<'a, E: Engine, F: PrimeField>{
    // this is kind-of normal UintX limbs
    pub(crate) binary_limbs: Vec<Limb<E>>,
    // we can not multiply by power of modulus of our base field E,
    // so we keep only one single limb
    pub(crate) base_field_limb: Term<E>,

    pub(crate) representation_params: &'a RnsParameters<E, F>,
    pub(crate) value: Option<F>,
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
        write!(f, "Value from field limbs = {:?} ", self.base_field_limb.get_value())?;
        writeln!(f, "}}")
    }
}

fn value_to_limbs<E: Engine, F: PrimeField>(
    value: Option<F>,
    params: &RnsParameters<E, F>
) -> (Vec<Option<E::Fr>>, Option<E::Fr>) {
    let num_limbs = params.num_binary_limbs;

    match value {
        Some(value) => {
            let value_as_bigint = fe_to_biguint(&value);
            let binary_limb_values = split_into_fixed_number_of_limbs(
                value_as_bigint, 
                params.binary_limbs_params.limb_size_bits, 
                params.num_binary_limbs
            );
            assert_eq!(binary_limb_values.len(), params.num_binary_limbs);
    
            let base_limb = fe_to_biguint(&value) % &params.base_field_modulus;
            let base_limb = biguint_to_fe::<E::Fr>(base_limb);
    
            let binary_limbs: Vec<Option<E::Fr>> = binary_limb_values.into_iter().map(|el| Some(biguint_to_fe::<E::Fr>(el))).collect();
            assert_eq!(binary_limbs.len(), params.num_binary_limbs);

            return (binary_limbs, Some(base_limb));
        },
        None => {
            return (vec![None; num_limbs], None);
        }
    }
}

impl<'a, E: Engine, F: PrimeField> FieldElement<'a, E, F> {
    pub fn new_allocated<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        value: Option<F>,
        params: &'a RnsParameters<E, F>
    ) -> Result<Self, SynthesisError> {
        let (binary_limbs, base_limb) = value_to_limbs(value, params);

        let mut binary_limbs_allocated = Vec::with_capacity(binary_limbs.len());

        for ((l, &width), max_val) in binary_limbs.into_iter()
            .zip(params.binary_limbs_bit_widths.iter())
            .zip(params.binary_limbs_max_values.iter().cloned()) 
        {
            let a = AllocatedNum::alloc(cs, || {
                Ok(*l.get()?)
            })?;

            let _ = create_range_constraint_chain(cs, &a, width);
            let term = Term::from_allocated_num(a);

            let limb = Limb::<E>::new(
                term,
                max_val
            );

            binary_limbs_allocated.push(limb);
        }

        let a = AllocatedNum::alloc(cs, || {
            Ok(*base_limb.get()?)
        })?;

        let base_limb = Term::from_allocated_num(a);

        let new = Self {
            binary_limbs: binary_limbs_allocated,
            base_field_limb: base_limb,
            representation_params: params,
            value,
        };

        Ok(new)
    }

    pub fn from_double_size_limb_witnesses<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        witnesses: &[Num<E>],
        top_limb_may_overflow: bool,
        params: &'a RnsParameters<E, F>
    ) -> Result<Self, SynthesisError> {
        // println!("Creating field element from double limb witness");
        // for w in witnesses.iter() {
        //     println!("Double limb witness = {}", w.get_value().unwrap());
        // }

        assert!(params.num_binary_limbs == params.limb_witness_size * witnesses.len());

        let mut binary_limbs_allocated = Vec::with_capacity(params.num_binary_limbs);

        let mut base_field_lc = LinearCombination::<E>::zero();

        let mut shift_constant = params.binary_limbs_params.shift_left_by_limb_constant;
        shift_constant.square();

        let mut current_constant = E::Fr::one();

        let mut this_value = BigUint::from(0u64);
        let mut value_is_none = false;

        for (i, w) in witnesses.iter().enumerate() {
            match w {
                Num::Constant(value) => {
                    this_value += fe_to_biguint(value) << (i*2*params.binary_limbs_params.limb_size_bits);
                    let limb_values = split_into_fixed_width_limbs(fe_to_biguint(value), params.binary_limbs_params.limb_size_bits);
                    assert!(limb_values.len() == params.limb_witness_size);
                    for (j, l) in limb_values.into_iter().enumerate() {
                        let limb_idx = i*params.limb_witness_size + j;
                        let max_value = if limb_idx == params.num_binary_limbs && top_limb_may_overflow {
                            params.last_binary_limb_max_value.clone()
                        } else {
                            params.binary_limbs_params.limb_max_value.clone()
                        };

                        assert!(&l <= &max_value);

                        let term = Term::<E>::from_constant(biguint_to_fe(l));
                        let limb = Limb::<E>::new( 
                            term,
                            max_value
                        );

                        binary_limbs_allocated.push(limb);
                    }
                },
                Num::Variable(var) => {
                    let limb_values = if let Some(v) = var.get_value() {
                        let v = fe_to_biguint(&v);
                        this_value += v.clone() << (i*2*params.binary_limbs_params.limb_size_bits);

                        let limb_values = split_some_into_fixed_number_of_limbs(
                            Some(v), 
                            params.binary_limbs_params.limb_size_bits, 
                            params.limb_witness_size);

                        limb_values
                    } else {
                        value_is_none = true;

                        vec![None; params.limb_witness_size]
                    };

                    let expected_high_width = if (i+1)*params.limb_witness_size == params.num_binary_limbs {
                        params.last_binary_limb_bit_width
                    } else {
                        params.binary_limbs_params.limb_size_bits
                    };

                    let expected_high_max_value = if (i+1)*params.limb_witness_size == params.num_binary_limbs {
                        params.last_binary_limb_max_value.clone()
                    } else {
                        params.binary_limbs_params.limb_max_value.clone()
                    };

                    assert!(expected_high_width & 1 == 0);
                    // if expected_high_width & 1 == 1 {
                    //     expected_high_width += 1;
                    // }

                    let expected_width = expected_high_width + params.binary_limbs_params.limb_size_bits;
                    let chain = create_range_constraint_chain(cs, var, expected_width)?;
                    assert!(expected_width % chain.len() == 0);
                    let constrained_bits_per_element = expected_width / chain.len();
                    let half_idx = params.binary_limbs_params.limb_size_bits / constrained_bits_per_element - 1;
                    let low_limb_element = chain[half_idx].clone();

                    // println!("Low limb element = {}", low_limb_element.get_value().unwrap());

                    let low_term = Term::<E>::from_allocated_num(low_limb_element);

                    let low_limb = Limb::<E>::new( 
                        low_term.clone(),
                        params.binary_limbs_params.limb_max_value.clone(),
                    );

                    binary_limbs_allocated.push(low_limb);

                    let full_term = Term::<E>::from_allocated_num(var.clone());

                    let mut tmp = low_term;
                    tmp.negate();

                    let mut high_term = full_term.add(cs, &tmp)?;
                    high_term.scale(&params.binary_limbs_params.shift_right_by_limb_constant);

                    let high_term = high_term.collapse_into_num(cs)?;

                    let high_term = Term::<E>::from_num(high_term);

                    // println!("High limb element = {}", high_term.get_value().unwrap());

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
    ) -> Result<Self, SynthesisError> {
        let value = fe_to_biguint(&v);
        let binary_limb_values = split_into_fixed_width_limbs(value.clone(), params.binary_limbs_params.limb_size_bits);
        assert!(binary_limb_values.len() <= params.num_binary_limbs);
        let base_limb_value = value.clone() % &params.base_field_modulus;

        let base_limb = biguint_to_fe(base_limb_value.clone());

        let mut binary_limbs_allocated = Vec::with_capacity(binary_limb_values.len());
        for l in  binary_limb_values.into_iter()
        {
            let f = biguint_to_fe(l.clone());
            let term = Term::<E>::from_constant(f);
            let limb = Limb::<E>::new(
                term,
                l
            );

            binary_limbs_allocated.push(limb);
        }

        let zero_limb = Self::zero_limb();
        binary_limbs_allocated.resize(params.num_binary_limbs, zero_limb);

        let base_limb = Term::<E>::from_constant(base_limb);

        Ok(Self {
            binary_limbs: binary_limbs_allocated,
            base_field_limb: base_limb,
            representation_params: params,
            value: Some(v),
        })
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
    fn get_value(&self) -> Option<BigUint> {
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

    // return current value unreduced
    fn get_field_value(&self) -> Option<F> {
        self.value
    }

    // return maximum value based on maximum limb values
    fn get_max_value(&self) -> BigUint {
        let shift = self.representation_params.binary_limbs_params.limb_size_bits;

        let mut result = BigUint::from(0u64);

        for l in self.binary_limbs.iter().rev() {
            result <<= shift;
            result += l.max_value();
        }

        result
    }

    fn is_constant(&self) -> bool {
        for l in self.binary_limbs.iter() {
            if !l.is_constant() {
                return false;
            }
        }

        self.base_field_limb.is_constant()
    }

    pub fn negated<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS
    ) -> Result<(Self, Self), SynthesisError> {
        let (new, (_, this)) = Self::zero(&self.representation_params).sub(cs, self)?;

        Ok((new, this))
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
        // let mut needs_reduction = self.get_max_value() > self.representation_params.max_representable_value() * self.representation_params.max_representable_value();
        let max_limb_value = &self.representation_params.binary_limbs_params.limb_max_intermediate_value;
        for binary_limb in self.binary_limbs.iter() {
            needs_reduction = needs_reduction || &binary_limb.max_value() > max_limb_value;
        }

        needs_reduction
    }

    pub fn reduce_if_necessary<CS: ConstraintSystem<E>>(
        mut self,
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

    fn reduction_impl<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS
    ) -> Result<Self, SynthesisError> {
        // first perform actual reduction in the field that we try to represent
        let (q, rem) = if let Some(v) = self.get_value() {
            let (q, rem) = v.div_rem(&self.representation_params.represented_field_modulus);

            (Some(q), Some(rem))
        } else {
            (None, None)
        };
        

        let mut max_q_bits = (self.get_max_value() / &self.representation_params.represented_field_modulus).bits() + 1;
        if max_q_bits & 1 == 1 {
            max_q_bits += 1;
        }
        assert!(max_q_bits <= E::Fr::CAPACITY as usize, "for no quotient size can not overflow capacity");

        let q_fe = some_biguint_to_fe::<E::Fr>(&q);
        let q_represented_field_value = some_biguint_to_fe::<F>(&q);
       
        let q_as_field_repr = if max_q_bits <= self.representation_params.binary_limbs_params.limb_size_bits {
            let q_max_value = (BigUint::from(1u64) << max_q_bits) - BigUint::from(1u64);

            let allocated = AllocatedNum::alloc(
                cs, 
                || {
                    Ok(*q_fe.get()?)
                }
            )?;
    
            let _ = create_range_constraint_chain(cs, &allocated, max_q_bits)?;
            let term = Term::<E>::from_allocated_num(allocated);
            let q_limb = Limb::new(term.clone(), q_max_value);
    
            let q_empty_limb = Self::zero_limb();
    
            let mut q_new_binary_limbs = Vec::with_capacity(self.binary_limbs.len());
            q_new_binary_limbs.push(q_limb.clone());
            q_new_binary_limbs.resize(self.representation_params.num_binary_limbs, q_empty_limb);
    
            let q_base_field_term = term;
    
            let q_as_field_repr = Self{
                base_field_limb: q_base_field_term,
                binary_limbs: q_new_binary_limbs,
                representation_params: self.representation_params,
                value: q_represented_field_value
            };

            q_as_field_repr
        } else {
            // we need more limbs for quotient
            let mut num_limbs = max_q_bits / self.representation_params.binary_limbs_params.limb_size_bits;
            if max_q_bits % self.representation_params.binary_limbs_params.limb_size_bits != 0 {
                num_limbs += 1;
            }

            // let q_max_value = (BigUint::from(1u64) << max_q_bits) - BigUint::from(1u64);

            let allocated = AllocatedNum::alloc(
                cs, 
                || {
                    Ok(*q_fe.get()?)
                }
            )?;
    
            let chain = create_range_constraint_chain(cs, &allocated, max_q_bits)?;
            let term = Term::<E>::from_allocated_num(allocated);

            let mut q_new_binary_limbs = Vec::with_capacity(self.binary_limbs.len());

            assert!(max_q_bits % chain.len() == 0);
            let constraint_bits_per_step = max_q_bits / chain.len();

            let mut shift = 0;

            for l in 0..num_limbs {
                let bits = if max_q_bits >= self.representation_params.binary_limbs_params.limb_size_bits {
                    max_q_bits -= self.representation_params.binary_limbs_params.limb_size_bits;

                    self.representation_params.binary_limbs_params.limb_size_bits
                } else {
                    max_q_bits
                };

                let max_limb_value = (BigUint::from(1u64) << bits) - BigUint::from(1u64);

                let subvalue_index = bits / constraint_bits_per_step - 1;

                let allocated = chain[subvalue_index + shift].clone();
                let term = Term::<E>::from_allocated_num(allocated);
                let q_limb = Limb::new(term.clone(), max_limb_value);

                q_new_binary_limbs.push(q_limb);

                shift += subvalue_index + 1;
            }

            let q_empty_limb = Self::zero_limb();
            q_new_binary_limbs.resize(self.representation_params.num_binary_limbs, q_empty_limb);
    
            let q_base_field_term = term;
    
            let q_as_field_repr = Self{
                base_field_limb: q_base_field_term,
                binary_limbs: q_new_binary_limbs,
                representation_params: self.representation_params,
                value: q_represented_field_value
            };

            q_as_field_repr

        };

        assert!(max_q_bits <= self.representation_params.binary_limbs_params.limb_size_bits, 
            "during requction q has {} bits, limb size is {}", max_q_bits, self.representation_params.binary_limbs_params.limb_size_bits);
        

        // create remainder

        let r_fe = some_biguint_to_fe::<F>(&rem);

        let r_as_field_repr = Self::new_allocated(
            cs,
            r_fe,
            self.representation_params
        )?;

        // perform constraining by implementing multiplication
        // x = q*p + r

        let one = Self::one(self.representation_params);

        Self::constraint_fma_with_multiple_additions(
            cs,
            &self, 
            &one,
            &[],
            &q_as_field_repr, 
            &[r_as_field_repr.clone()],
        )?;

        Ok(r_as_field_repr)
    }

    fn slice_into_double_limb_witnesses<CS: ConstraintSystem<E>>(
        value: Option<BigUint>,
        cs: &mut CS,
        params: &RnsParameters<E, F>,
    ) -> Result<Vec<Num<E>>, SynthesisError> {
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

        // let mut new_value = this.value;
        // new_value.add_assign(&other.value);

        let new = Self {
            binary_limbs: new_binary_limbs,
            base_field_limb: new_base_limb,
            value: new_value,
            representation_params: params
        };

        Ok((new, (this, other)))
    }

    pub fn sub<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
        other: Self
    ) -> Result<(Self, (Self, Self)), SynthesisError> {
        let params = self.representation_params;

        let this = self.reduce_if_necessary(cs)?;
        let other = other.reduce_if_necessary(cs)?;

        // subtraction is a little more involved

        // first do the constrant propagation
        if this.is_constant() && other.is_constant() {
            let tmp = this.get_field_value().sub(&other.get_field_value());
            // let mut tmp = params.represented_field_modulus.clone() + this.get_value() - other.get_value();
            // tmp = tmp % & params.represented_field_modulus;

            let new = Self::new_constant(tmp.unwrap(), params)?;

            return Ok((new, (this, other)));
        }

        if other.is_constant() {
            let tmp = other.get_field_value().negate();
            // let mut tmp =  params.represented_field_modulus.clone() - other.get_value();
            // tmp = tmp % & params.represented_field_modulus;

            let other_negated =  Self::new_constant(tmp.unwrap(), params)?;

            // do the constant propagation in addition

            return this.add(cs, other_negated);
        }

        // keep track for potential borrows and subtract binary limbs

        // construct data on from what positions we would borrow

        let mut borrow_max_values = vec![];
        let mut borrow_bit_widths = vec![];

        let mut previous = None;

        for l in other.binary_limbs.iter() {
            let mut max_value = l.max_value();
            if let Some(previous_shift) = previous.take() {
                max_value += BigUint::from(1u64) << (previous_shift - params.binary_limbs_params.limb_size_bits);
            }

            let borrow_bits = std::cmp::max(params.binary_limbs_params.limb_size_bits, max_value.bits());

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

        loop {
            let slices = split_into_fixed_number_of_limbs(multiples.clone(), params.binary_limbs_params.limb_size_bits, params.num_binary_limbs);
            if slices.last().unwrap() <= borrow_max_values.last().unwrap() {
                multiples += &params.represented_field_modulus;
            } else {
                break;
            }
        }

        let multiple_slices = split_into_fixed_number_of_limbs(multiples.clone(), params.binary_limbs_params.limb_size_bits, params.num_binary_limbs);

        // create new limbs

        let mut previous = None;

        let last_idx = this.binary_limbs.len() - 1;

        let mut new_binary_limbs = vec![];

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

        let tmp = multiples % &params.base_field_modulus;
        let constant_as_fe = biguint_to_fe::<E::Fr>(tmp);

        let mut tmp = this.base_field_limb.clone();
        tmp.add_constant(&constant_as_fe);

        let mut other_negated = other.base_field_limb.clone();
        other_negated.negate();

        let new_base_limb = tmp.add(cs, &other_negated)?;

        let new_value = this.get_field_value().sub(&other.get_field_value());

        // let mut new_value = this.value;
        // new_value.sub_assign(&other.value);

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
            let new = Self::new_constant(r.unwrap(), params)?;

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

        let q_wit = Self::slice_into_double_limb_witnesses(q, cs, params)?;

        let q_elem = Self::from_double_size_limb_witnesses(
            cs, 
            &q_wit, 
            true, 
            params
        )?;

        let r_wit = Self::slice_into_double_limb_witnesses(r, cs, params)?;
    
        let r_elem = Self::from_double_size_limb_witnesses(
            cs, 
            &r_wit, 
            false, 
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

    pub fn fma_with_addition_chain<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
        to_mul: Self,
        to_add: Vec<Self>
    ) -> Result<(Self, (Self, Self, Vec<Self>)), SynthesisError> {
        let params = self.representation_params;

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
            let new = Self::new_constant(r, params)?;
            return Ok((new, (this, to_mul, to_add)));
        }

        let (q, r) = if value_is_none {
            (None, None)
        } else {
            (Some(q), Some(r))
        };

        let q_wit = Self::slice_into_double_limb_witnesses(q, cs, params)?;

        let q_elem = Self::from_double_size_limb_witnesses(
            cs, 
            &q_wit, 
            true, 
            params
        )?;

        let r_wit = Self::slice_into_double_limb_witnesses(r, cs, params)?;
    
        let r_elem = Self::from_double_size_limb_witnesses(
            cs, 
            &r_wit, 
            false, 
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

        // code here duplicated a little to avoid reduction mess

        let this = self.reduce_if_necessary(cs)?;
        let den = den.reduce_if_necessary(cs)?;

        if this.is_constant() && den.is_constant() {
            let mut tmp = den.get_field_value().unwrap().inverse().unwrap();
            tmp.mul_assign(&this.get_field_value().unwrap());

            let new = Self::new_constant(tmp, params)?;

            return Ok((new, (this, den)));
        }

        let (inv, result, q, rem) = match (this.get_value(), den.get_value()) {
            (Some(this), Some(den)) => {
                let inv = mod_inverse(&den, &params.represented_field_modulus);
                let result = this.clone() * &inv % &params.represented_field_modulus;

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

        let q_wit = Self::slice_into_double_limb_witnesses(q, cs, params)?;

        let q_elem = Self::from_double_size_limb_witnesses(
            cs, 
            &q_wit, 
            true, 
            params
        )?;

        let inv_wit = Self::slice_into_double_limb_witnesses(result, cs, params)?;
    
        let inv_wit = Self::from_double_size_limb_witnesses(
            cs, 
            &inv_wit, 
            false, 
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

    pub(crate) fn div_from_addition_chain_with_reduced_numerators<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        nums: Vec<Self>,
        den: Self
    ) -> Result<(Self, (Vec<Self>, Self)), SynthesisError> {
        let params = den.representation_params;

        // we do self/den = result mod p
        // so we constraint result * den = q * p + self

        let den = den.reduce_if_necessary(cs)?;

        let inv = if let Some(den) = den.get_value() {
            let inv = mod_inverse(&den, &params.represented_field_modulus);

            Some(inv)
        } else {
            None
        };

        let mut value_is_none = false;
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

        let (result, q, rem) = match (num_value, den.get_value(), inv.clone()) {
            (Some(num_value), Some(den), Some(inv)) => {
                let num_value = num_value % &params.represented_field_modulus;
                let result = num_value.clone() * &inv % &params.represented_field_modulus;
                let value = den * &result - num_value;
        
                let (q, rem) = value.div_rem(&params.represented_field_modulus);
        
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
            let new = Self::new_constant(v, params)?;
            return Ok((new, (reduced_nums, den)));
        }

        let q_wit = Self::slice_into_double_limb_witnesses(q, cs, params)?;

        let q_elem = Self::from_double_size_limb_witnesses(
            cs, 
            &q_wit, 
            true, 
            den.representation_params
        )?;

        let inv_wit = Self::slice_into_double_limb_witnesses(result, cs, den.representation_params)?;
    
        let inv_wit = Self::from_double_size_limb_witnesses(
            cs, 
            &inv_wit, 
            false, 
            den.representation_params
        )?;

        Self::constraint_fma_with_multiple_additions(
            cs, 
            &den,
            &inv_wit,
            &[],
            &q_elem,
            &reduced_nums,
        )?;

        Ok((inv_wit, (reduced_nums, den)))
    }


    // returns first if true and second if false
    fn select<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        flag: &Boolean,
        first: Self,
        second: Self
    ) -> Result<(Self, (Self, Self)), SynthesisError> {
        let first = first.reduce_if_necessary(cs)?;

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

        let mut minus_b = first.base_field_limb.clone();
        minus_b.negate();
        let a_minus_b = second.base_field_limb.add(cs, &minus_b)?;

        let new_base_limb = Term::<E>::fma(cs, &flag_as_term, &a_minus_b, &second.base_field_limb)?;

        let new_value = if flag.get_value().unwrap() {
        first.value
        } else {
            second.value
        };

        let new = Self {
            binary_limbs: new_binary_limbs,
            base_field_limb: new_base_limb,
            value: new_value,
            representation_params: first.representation_params
        };

        Ok((new, (first, second)))
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

        // now we need to process over additions and remainder
        let mut collapsed_limbs = vec![];
        let mut collapsed_max_values = vec![];
        for (components, max_values_components) in result_limbs.into_iter()
                                                    .zip(expected_binary_max_values.into_iter()) 
        {
            assert!(components.len() > 0);
            let r = if components.len() == 1 {
                components[0].clone()
            } else {
                let (base, other) = components.split_first().unwrap();
                let r = base.add_multiple(cs, &other)?;

                r
            };

            collapsed_limbs.push(r);

            let mut max_value = BigUint::from(0u64);
            for c in max_values_components.into_iter() {
                max_value += c;
            }

            collapsed_max_values.push(max_value);
        }

        // also add max value contributions from additions
        // we do not add max values from remainder cause we expect it to cancel exactly
        let mut double_limb_max_bits = vec![];
        for i in (0..target_limbs).step_by(2) {
            let mut max_value = BigUint::from(0u64);
            max_value += &collapsed_max_values[i];
            max_value += &collapsed_max_values[i+1] << params.binary_limbs_params.limb_size_bits;
            for a in addition_elements.iter() {
                max_value += a.binary_limbs[i].max_value();
                max_value += a.binary_limbs[i+1].max_value() << params.binary_limbs_params.limb_size_bits;
            }

            let mut max_bits = max_value.bits() + 1;
            if max_bits & 1 == 1 {
                // we expect to constraint by two bits only
                max_bits += 1;
            }

            double_limb_max_bits.push(max_bits);
        }

        let shift_right_one_limb_constant = params.binary_limbs_params.shift_right_by_limb_constant;
        let mut shift_right_two_limb_constant = shift_right_one_limb_constant;
        shift_right_two_limb_constant.square();

        let shift_left_one_limb_constant = params.binary_limbs_params.shift_left_by_limb_constant;
        let mut shift_left_two_limb_constant = shift_left_one_limb_constant;
        shift_left_two_limb_constant.square();

        // check that multiplications did not overflow
        // e.g that a[0] * b[0] - q[0] * p[0] - r[0] fits into two limbs max

        let mut minus_one = E::Fr::one();
        minus_one.negate();

        let mut double_limb_carries = vec![];

        let mut chunk_of_previous_carry = None;

        let last_idx = target_limbs - 1;

        for i in (0..target_limbs).step_by(2) {
            let mut contributions = vec![];

            let tmp = collapsed_limbs[i].clone();
            contributions.push(tmp);

            let mut tmp = collapsed_limbs[i+1].clone();
            tmp.scale(&shift_left_one_limb_constant);
            contributions.push(tmp);

            for result_remainder in result_remainder_decomposition.iter() {
                let mut tmp = result_remainder.binary_limbs[i].term.clone();
                tmp.negate();
                contributions.push(tmp);
    
                let mut tmp = result_remainder.binary_limbs[i+1].term.clone();
                tmp.scale(&shift_left_one_limb_constant);
                tmp.negate();
                contributions.push(tmp);
            }

            for addition_element in addition_elements.iter() {
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

            if i+1 != last_idx {
                chunk_of_previous_carry = Some(r.clone());
            };

            double_limb_carries.push(r);
        }

        assert!(chunk_of_previous_carry.is_none());

        assert_eq!(double_limb_carries.len(), double_limb_max_bits.len());

        let mut previous_chunk: Option<(Num<E>, usize)> = None;

        let last_idx = double_limb_carries.len() - 1;

        // now we have to take each "double carry" and propagate it into other
        for (idx, (r, max_bits)) in double_limb_carries.into_iter()
            .zip(double_limb_max_bits.into_iter())
            .enumerate() 
        {
            let this_carry_value = r.collapse_into_num(cs)?;

            assert!(max_bits >= 2*params.binary_limbs_params.limb_size_bits);

            let mut carry_max_bits = max_bits - 2*params.binary_limbs_params.limb_size_bits;
            if carry_max_bits & 1 == 1 {
                carry_max_bits += 1;
            }

            // TODO: Combine by more than two, write proper multipack + constraint function
            if let Some((previous_carry_value, previous_max_bits)) = previous_chunk.take() {
                // we have some bits to constraint from the previous step
                let mut shift_constant = E::Fr::one();
                for _ in 0..previous_max_bits {
                    shift_constant.double();
                }
                let mut this_combined_with_previous = Term::<E>::from_num(this_carry_value);
                let previous_term = Term::<E>::from_num(previous_carry_value.clone());
                this_combined_with_previous.scale(&shift_constant);
                let combined_carry_value = this_combined_with_previous.add(cs, &previous_term)?.collapse_into_num(cs)?;

                let max_bits_from_both = carry_max_bits + previous_max_bits;

                match combined_carry_value {
                    Num::Constant(val) => {
                        let f = fe_to_biguint(&val);
                        assert!(f.bits() <= max_bits);
                    },
                    Num::Variable(var) => {
                        let chain = create_range_constraint_chain(cs, &var, max_bits_from_both)?;
                        assert!(max_bits_from_both % chain.len() == 0);
                        let constraint_bits_per_step = max_bits_from_both / chain.len();
                        let idx_for_lower_part = previous_max_bits / constraint_bits_per_step - 1;

                        let low_part_in_chain = chain[idx_for_lower_part].clone();

                        let v = match previous_carry_value {
                            Num::Variable(p) => p,
                            _ => {unreachable!()}
                        };

                        low_part_in_chain.enforce_equal(cs, &v)?;
                    }
                }
            } else {
                if idx == last_idx {
                    // this is a last chunk, so we have to enforce right away
                    match this_carry_value {
                        Num::Constant(val) => {
                            let f = fe_to_biguint(&val);
                            assert!(f.bits() <= carry_max_bits);
                        },
                        Num::Variable(var) => {
                            let _ = create_range_constraint_chain(cs, &var, carry_max_bits)?;
                        }
                    }
                } else {
                    // combine with next
                    previous_chunk = Some((this_carry_value, carry_max_bits));
                }   
                
            }
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

    fn dirty_limb_addition<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        x: &Limb<E>,
        y: &Limb<E>,
    ) -> Result<Limb<E>, SynthesisError> {
        let new_max_value = x.max_value() + y.max_value();

        let new_term = x.term.add(cs, &y.term)?;

        let new = Limb::<E> {
            term: new_term,
            max_value: new_max_value
        };

        Ok(new)
    }

    fn dirty_three_limb_addition<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        x: &Limb<E>,
        y: &Limb<E>,
        z: &Limb<E>
    ) -> Result<Limb<E>, SynthesisError> {
        assert!(CS::Params::STATE_WIDTH >= 4);

        let new_max_value = x.max_value() + y.max_value() + z.max_value();

        let new_term = x.term.add_multiple(cs, &[y.term.clone(), z.term.clone()])?;

        let new = Limb::<E> {
            term: new_term,
            max_value: new_max_value
        };

        Ok(new)
    }

    fn dirty_limb_fma<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        x: &Limb<E>,
        y: &Limb<E>,
        z: &Limb<E>
    ) -> Result<Limb<E>, SynthesisError> {
        assert!(CS::Params::STATE_WIDTH >= 4);

        let new_max_value = x.max_value() * y.max_value() + z.max_value();

        let new_term = Term::<E>::fma(
            cs,
            &x.term,
            &y.term,
            &z.term
        )?;

        let new = Limb::<E> {
            term: new_term,
            max_value: new_max_value
        };

        Ok(new)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::bellman::pairing::bn256::{Fq, Bn256, Fr};

    #[test]
    fn test_constant_propagation() {
        let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNextEquation>::new();

        let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

        let a = Fq::from_str("1234").unwrap();
        let b = Fq::from_str("5678").unwrap();

        let a = FieldElement::new_constant(a, &params).unwrap();
        let b = FieldElement::new_constant(b, &params).unwrap();

        let (result, (a, b)) = a.mul(&mut cs, b).unwrap();

        assert_eq!(result.get_value().unwrap(), BigUint::from(1234u64) * BigUint::from(5678u64));
    }

    #[test]
    fn test_mul_on_random_witnesses(){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

        for i in 0..100 {
            let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNextEquation>::new();

            let a_f: Fq = rng.gen();
            let b_f: Fq = rng.gen();
            let a = FieldElement::new_allocated(
                &mut cs, 
                Some(a_f), 
                &params
            ).unwrap();

            let a_base = biguint_to_fe::<Fr>(fe_to_biguint(&a_f) % repr_to_biguint::<Fr>(&Fr::char()));
            assert_eq!(a_base, a.base_field_limb.get_value().unwrap());

            let b = FieldElement::new_allocated(
                &mut cs, 
                Some(b_f),
                &params
            ).unwrap();

            let b_base = biguint_to_fe::<Fr>(fe_to_biguint(&b_f) % repr_to_biguint::<Fr>(&Fr::char()));
            assert_eq!(b_base, b.base_field_limb.get_value().unwrap());
    
            let (result, (a, b)) = a.mul(&mut cs, b).unwrap();

            assert!(cs.is_satisfied());

            let mut m = a_f;
            m.mul_assign(&b_f);

            assert_eq!(result.value.unwrap(), m);

            assert_eq!(result.get_value().unwrap(), fe_to_biguint(&m));

            // let mut ab_in_base_field = a_base;
            // ab_in_base_field.mul_assign(&b_base);

            // assert_eq!(result.base_field_limb.get_value().unwrap(), ab_in_base_field);

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

    #[test]
    fn test_bls12_mul_on_random_witnesses(){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        use crate::bellman::pairing::bls12_381::{Bls12, Fr, Fq};
        // let params = RnsParameters::<Bls12, Fq>::new_for_field(68, 110, 8);
        let params = RnsParameters::<Bls12, Fq>::new_for_field(88, 120, 6);

        println!("Max representable = {}, with {} bits", params.max_representable_value().to_str_radix(16), params.max_representable_value().bits());

        for i in 0..100 {
            let mut cs = TrivialAssembly::<Bls12, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNextEquation>::new();

            let a_f: Fq = rng.gen();
            let b_f: Fq = rng.gen();
            let a = FieldElement::new_allocated(
                &mut cs, 
                Some(a_f), 
                &params
            ).unwrap();

            let a_base = biguint_to_fe::<Fr>(fe_to_biguint(&a_f) % repr_to_biguint::<Fr>(&Fr::char()));
            assert_eq!(a_base, a.base_field_limb.get_value().unwrap());

            let b = FieldElement::new_allocated(
                &mut cs, 
                Some(b_f),
                &params
            ).unwrap();

            let b_base = biguint_to_fe::<Fr>(fe_to_biguint(&b_f) % repr_to_biguint::<Fr>(&Fr::char()));
            assert_eq!(b_base, b.base_field_limb.get_value().unwrap());
    
            let (result, (a, b)) = a.mul(&mut cs, b).unwrap();

            assert!(cs.is_satisfied());

            let mut m = a_f;
            m.mul_assign(&b_f);

            assert_eq!(result.value.unwrap(), m);

            assert_eq!(result.get_value().unwrap(), fe_to_biguint(&m));

            // let mut ab_in_base_field = a_base;
            // ab_in_base_field.mul_assign(&b_base);

            // assert_eq!(result.base_field_limb.get_value().unwrap(), ab_in_base_field);

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

    #[test]
    fn test_add_on_random_witnesses(){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);
        println!("Representing field for modulus {}", Fq::char());

        for i in 0..100 {
            let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNextEquation>::new();

            let a_f: Fq = rng.gen();
            let b_f: Fq = rng.gen();
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

            let a_base = biguint_to_fe::<Fr>(fe_to_biguint(&a_f) % repr_to_biguint::<Fr>(&Fr::char()));
            let b_base = biguint_to_fe::<Fr>(fe_to_biguint(&b_f) % repr_to_biguint::<Fr>(&Fr::char()));

            assert_eq!(a_base, a.base_field_limb.get_value().unwrap());
            assert_eq!(b_base, b.base_field_limb.get_value().unwrap());
    
            let (result, (a, b)) = a.add(&mut cs, b).unwrap();

            assert!(cs.is_satisfied());

            let mut m = a_f;
            m.add_assign(&b_f);

            let res = result.get_value().unwrap() % repr_to_biguint::<Fq>(&Fq::char());
            assert_eq!(res, fe_to_biguint(&m));

            assert_eq!(result.value.unwrap(), m);

            // let mut ab_in_base_field = a_base;
            // ab_in_base_field.add_assign(&b_base);

            // assert_eq!(result.base_field_limb.get_value().unwrap(), ab_in_base_field);

            if i == 0 {
                let t0 = a.reduce_if_necessary(&mut cs).unwrap();
                let t1 = result.reduce_if_necessary(&mut cs).unwrap();
                let base = cs.n();
                let _ = t0.add(&mut cs, t1).unwrap();
                println!("Single addition taken {} gates", cs.n() - base);
            }
        }
    }

    #[test]
    fn test_sub_on_random_witnesses(){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);
        println!("Representing field for modulus {}", Fq::char());

        for i in 0..100 {
            let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNextEquation>::new();

            let a_f: Fq = rng.gen();
            let b_f: Fq = rng.gen();
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

            let a_base = biguint_to_fe::<Fr>(fe_to_biguint(&a_f) % repr_to_biguint::<Fr>(&Fr::char()));
            let b_base = biguint_to_fe::<Fr>(fe_to_biguint(&b_f) % repr_to_biguint::<Fr>(&Fr::char()));

            assert_eq!(a_base, a.base_field_limb.get_value().unwrap());
            assert_eq!(b_base, b.base_field_limb.get_value().unwrap());
    
            let (result, (a, b)) = a.sub(&mut cs, b).unwrap();

            assert!(cs.is_satisfied());

            let mut m = a_f;
            m.sub_assign(&b_f);

            let res = result.get_value().unwrap() % repr_to_biguint::<Fq>(&Fq::char());
            assert_eq!(res, fe_to_biguint(&m));

            assert_eq!(result.value.unwrap(), m);

            if i == 0 {
                let t0 = a.reduce_if_necessary(&mut cs).unwrap();
                let t1 = result.reduce_if_necessary(&mut cs).unwrap();
                let base = cs.n();
                let _ = t0.sub(&mut cs, t1).unwrap();
                println!("Single subtraction taken {} gates", cs.n() - base);
            }
        }
    }

    #[test]
    fn test_select_on_random_witnesses(){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);
        println!("Representing field for modulus {}", Fq::char());

        for i in 0..100 {
            let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNextEquation>::new();

            let flag: bool = rng.gen();

            use crate::plonk::circuit::boolean::AllocatedBit;

            let bit = AllocatedBit::alloc(
                &mut cs,
                Some(flag)
            ).unwrap();

            let bit = Boolean::Not(bit);
            // let bit = Boolean::Is(bit);

            let a_f: Fq = rng.gen();
            let b_f: Fq = rng.gen();
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

            let a_base = biguint_to_fe::<Fr>(fe_to_biguint(&a_f) % repr_to_biguint::<Fr>(&Fr::char()));
            let b_base = biguint_to_fe::<Fr>(fe_to_biguint(&b_f) % repr_to_biguint::<Fr>(&Fr::char()));

            assert_eq!(a_base, a.base_field_limb.get_value().unwrap());
            assert_eq!(b_base, b.base_field_limb.get_value().unwrap());
    
            let (result, (a, b)) = FieldElement::select(&mut cs, &bit, a, b).unwrap();

            assert!(cs.is_satisfied());

            let m = if !flag {
                a_f
            }  else {
                b_f
            };

            let res = result.get_value().unwrap() % repr_to_biguint::<Fq>(&Fq::char());
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

    #[test]
    fn test_inv_mul_on_random_witnesses(){
        use rand::{XorShiftRng, SeedableRng, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

        println!("Max representable = {}, with {} bits", params.max_representable_value().to_str_radix(16), params.max_representable_value().bits());

        for i in 0..100 {
            let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNextEquation>::new();

            let a_f: Fq = rng.gen();
            let b_f: Fq = rng.gen();
            let a = FieldElement::new_allocated(
                &mut cs, 
                Some(a_f), 
                &params
            ).unwrap();

            let a_base = biguint_to_fe::<Fr>(fe_to_biguint(&a_f) % repr_to_biguint::<Fr>(&Fr::char()));
            assert_eq!(a_base, a.base_field_limb.get_value().unwrap());

            let b = FieldElement::new_allocated(
                &mut cs, 
                Some(b_f),
                &params
            ).unwrap();

            let b_base = biguint_to_fe::<Fr>(fe_to_biguint(&b_f) % repr_to_biguint::<Fr>(&Fr::char()));
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


}