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
    // pub represented_field_modulus_limbs: Vec<E::Fr>,
    pub represented_field_modulus_negated_limbs: Vec<E::Fr>,

    pub limb_witness_size: usize,

    pub (crate) _marker: std::marker::PhantomData<F>
}

impl<'a, E: Engine, F: PrimeField> RnsParameters<E, F>{
    pub fn max_representable_value(&self) -> BigUint {
        let tmp = self.base_field_modulus.clone() * &self.binary_representation_max_value;
        debug_assert!(&tmp.sqrt() >= &self.represented_field_modulus);

        println!("Max can represent {} bits up to {}", tmp.bits(), tmp.sqrt().to_str_radix(16));

        tmp.sqrt()
    }

    pub fn new_for_field(limb_size: usize, intermediate_limb_capacity: usize) -> Self {
        let binary_limbs_params = LimbedRepresentationParameters::new(limb_size, intermediate_limb_capacity);
        let mut num_binary_limbs = F::NUM_BITS as usize / limb_size;
        if F::NUM_BITS as usize % limb_size != 0 {
            num_binary_limbs += 1;
        }
        let base_field_limb_params = LimbedRepresentationParameters::new(F::NUM_BITS as usize, F::NUM_BITS as usize);
        let num_base_field_limb = 1;

        let base_field_modulus = repr_to_biguint::<E::Fr>(&E::Fr::char());
        let binary_modulus = BigUint::from(1u64) << (num_binary_limbs * limb_size);
        let binary_representation_max_value = binary_modulus.clone() - BigUint::from(1u64);

        let represented_field_modulus = repr_to_biguint::<F>(&F::char());
        let binary_limbs_bit_widths = vec![limb_size; num_binary_limbs];
        let binary_limbs_max_values = vec![binary_limbs_params.limb_max_value.clone(); num_binary_limbs];

        // let mut represented_field_modulus_limbs = vec![];
        let mut represented_field_modulus_negated_limbs = vec![];

        let represented_modulus_negated_modulo_binary = binary_modulus.clone() - &represented_field_modulus;
        println!("Represented modulus negated = {}", represented_modulus_negated_modulo_binary.to_str_radix(16));

        let mask = BigUint::from(1u64) << limb_size;
        let mut tmp = represented_modulus_negated_modulo_binary.clone();

        let mut bit_width = vec![];
        let mut modulus_chunks = vec![];
        for _ in 0..num_binary_limbs {
            let chunk = tmp.clone() % &mask;
            bit_width.push(chunk.bits());
            modulus_chunks.push(chunk.clone());
            let fe = biguint_to_fe::<E::Fr>(chunk);
            represented_field_modulus_negated_limbs.push(fe);
            tmp >>= limb_size;
        }

        Self {
            binary_limbs_params,
            num_binary_limbs,
            binary_modulus,
            base_field_limb_params,
            num_base_field_limb,
            base_field_modulus,
            binary_representation_max_value,
            represented_field_modulus,
            binary_limbs_bit_widths,
            binary_limbs_max_values,
            represented_field_modulus_negated_limbs,
            limb_witness_size: 2,
            last_binary_limb_bit_width: bit_width.pop().unwrap(),
            last_binary_limb_max_value: modulus_chunks.pop().unwrap(),
            _marker: std::marker::PhantomData
        }
    }
}

#[derive(Clone, Debug)]
pub struct FieldElement<'a, E: Engine, F: PrimeField>{
    // this is kind-of normal UintX limbs
    binary_limbs: Vec<Limb<E>>,
    // we can not multiply by power of modulus of our base field E,
    // so we keep only one single limb
    base_field_limb: Limb<E>,

    representation_params: &'a RnsParameters<E, F>,
    value: F,
    may_need_reduction: bool
}

fn required_u16_limbs<F: PrimeField>() -> usize {
    let limbs = (F::NUM_BITS + 16) / 16;

    limbs as usize
}

fn field_into_le_limbs<F: PrimeField>(el: &F) -> Vec<u16> {
    let required = required_u16_limbs::<F>();
    let mut result = Vec::with_capacity(required);

    let repr = el.into_raw_repr();

    for &limb in repr.as_ref().iter() {
        for i in 0..4 {
            let l = (limb >> (16*i)) as u16;
            result.push(l);

            if result.len() == required {
                break;
            }
        }
    }

    result
}

impl<'a, E: Engine, F: PrimeField> FieldElement<'a, E, F> {
    pub fn new_allocated<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        value: F,
        params: &'a RnsParameters<E, F>
    ) -> Result<Self, SynthesisError> {
        let value_as_biging = fe_to_biguint(&value);
        let binary_limb_values = split_into_fixed_number_of_limbs(value_as_biging, params.binary_limbs_params.limb_size_bits, params.num_binary_limbs);
        assert_eq!(binary_limb_values.len(), params.num_binary_limbs);

        let base_limb = fe_to_raw_biguint(&value) % &params.base_field_modulus;

        let binary_limbs: Vec<_> = binary_limb_values.into_iter().map(|el| biguint_to_fe(el)).collect();
        assert_eq!(binary_limbs.len(), params.num_binary_limbs);
        let base_limb = biguint_to_fe(base_limb);

        let mut binary_limbs_allocated = Vec::with_capacity(binary_limbs.len());

        for ((l, width), max_val) in binary_limbs.into_iter()
            .zip(params.binary_limbs_bit_widths.iter())
            .zip(params.binary_limbs_max_values.iter()) 
        {
            let a = AllocatedLimb::alloc(cs, l)?;
            let limb_type = LimbType::Variable(a);
            let limb = Limb::<E>::new_from_type(
                limb_type,
                max_val.clone(),
                *width
            );

            binary_limbs_allocated.push(limb);
        }

        let limb_type = LimbType::Variable(AllocatedLimb::alloc(cs, base_limb)?);
        let base_limb = Limb::<E>::new_from_type(
            limb_type,
            params.base_field_modulus.clone(),
            params.base_field_modulus.bits()
        );

        let new = Self {
            binary_limbs: binary_limbs_allocated,
            base_field_limb: base_limb,
            representation_params: params,
            value,
            may_need_reduction: false,
        };

        println!("Max value = {:?}", new.get_max_value().to_str_radix(16));

        Ok(new)
    }

    pub fn from_double_size_limb_witnesses<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        witnesses: &[Num<E>],
        top_limb_may_overflow: bool,
        params: &'a RnsParameters<E, F>
    ) -> Result<Self, SynthesisError> {
        assert!(params.num_binary_limbs == params.limb_witness_size * witnesses.len());

        let mut binary_limbs_allocated = Vec::with_capacity(params.num_binary_limbs);

        let mut base_field_lc = LinearCombination::<E>::zero();

        let mut shift_constant = params.binary_limbs_params.shift_left_by_limb_constant;
        shift_constant.square();

        let mut current_constant = E::Fr::one();

        let mut this_value = BigUint::from(0u64);

        for (i, w) in witnesses.iter().enumerate() {
            match w {
                Num::Constant(value) => {
                    this_value += fe_to_biguint(value) << (i*2*params.binary_limbs_params.limb_size_bits);
                    let limb_values = split_into_fixed_width_limbs(fe_to_biguint(value), params.binary_limbs_params.limb_size_bits);
                    assert!(limb_values.len() == params.limb_witness_size);
                    for (j, l) in limb_values.into_iter().enumerate() {
                        let limb_idx = i*params.limb_witness_size + j;

                        let limb_type = LimbType::Constant(biguint_to_fe(l));
                        let width = if limb_idx == params.num_binary_limbs && top_limb_may_overflow {
                            params.last_binary_limb_bit_width
                        } else {
                            params.binary_limbs_params.limb_size_bits
                        };

                        let max_value = if limb_idx == params.num_binary_limbs && top_limb_may_overflow {
                            params.last_binary_limb_max_value.clone()
                        } else {
                            params.binary_limbs_params.limb_max_value.clone()
                        };
                        let limb = Limb::<E>::new_from_type( 
                            limb_type,
                            max_value,
                            width
                        );

                        binary_limbs_allocated.push(limb);
                    }
                },
                Num::Variable(var) => {
                    let v = var.get_value().unwrap();
                    this_value += fe_to_biguint(&v) << (i*2*params.binary_limbs_params.limb_size_bits);
                    let limb_values = split_into_fixed_width_limbs(fe_to_biguint(&v), params.binary_limbs_params.limb_size_bits);
                    assert!(limb_values.len() == params.limb_witness_size);

                    let expected_high_width = if (i+1)*params.limb_witness_size == params.num_binary_limbs {
                        (params.limb_witness_size - 1) * params.binary_limbs_params.limb_size_bits + params.last_binary_limb_bit_width
                    } else {
                        params.limb_witness_size * params.binary_limbs_params.limb_size_bits
                    };

                    let expected_high_max_value = if (i+1)*params.limb_witness_size == params.num_binary_limbs{
                        params.last_binary_limb_max_value.clone()
                    } else {
                        params.binary_limbs_params.limb_max_value.clone()
                    };

                    let expected_width = expected_high_width + params.binary_limbs_params.limb_size_bits;
                    let chain = create_range_constraint_chain(cs, var, expected_width)?;
                    assert!(expected_width % chain.len() == 0);
                    let constrained_bits_per_element = expected_width / chain.len();
                    let half_idx = params.binary_limbs_params.limb_size_bits / constrained_bits_per_element;
                    let low_limb_element = chain[half_idx].clone();

                    let a = AllocatedLimb::<E> { 
                        value: low_limb_element.get_value().unwrap(),
                        variable: low_limb_element.get_variable()
                    };

                    let limb_type = LimbType::Variable(a);

                    let limb = Limb::<E>::new_from_type( 
                        limb_type,
                        params.binary_limbs_params.limb_max_value.clone(),
                        params.binary_limbs_params.limb_size_bits
                    );

                    binary_limbs_allocated.push(limb);

                    let mut new_var_value = v;
                    new_var_value.sub_assign(&low_limb_element.get_value().unwrap());
                    new_var_value.mul_assign(&params.binary_limbs_params.shift_right_by_limb_constant);

                    let high_limb = AllocatedNum::alloc(
                        cs, 
                        || {
                            Ok(new_var_value)
                        }
                    )?;

                    let a = AllocatedLimb::<E> { 
                        value: high_limb.get_value().unwrap(),
                        variable: high_limb.get_variable()
                    };

                    let limb_type = LimbType::Variable(a);

                    let limb = Limb::<E>::new_from_type( 
                        limb_type,
                        expected_high_max_value,
                        expected_high_width
                    );

                    binary_limbs_allocated.push(limb);
                }
            }

            base_field_lc.add_assign_number_with_coeff(w, current_constant);
            current_constant.mul_assign(&shift_constant);
        }

        let base_field_limb_num = base_field_lc.into_num(cs)?;

        let base_field_limb = match base_field_limb_num {
            Num::Constant(value) => {
                let limb_type = LimbType::Constant(value);
                let limb = Limb::<E>::new_from_type( 
                    limb_type,
                    params.base_field_limb_params.limb_max_value.clone(),
                    params.base_field_limb_params.limb_size_bits
                );

                limb
            },
            Num::Variable(var) => {
                let a = AllocatedLimb::<E> { 
                    value: var.get_value().unwrap(),
                    variable: var.get_variable()
                };

                let limb_type = LimbType::Variable(a);
                let limb = Limb::<E>::new_from_type( 
                    limb_type,
                    params.base_field_limb_params.limb_max_value.clone(),
                    params.base_field_limb_params.limb_size_bits
                );

                limb
            }
        };

        let this_value = biguint_to_fe::<F>(this_value);

        Ok(Self {
            binary_limbs: binary_limbs_allocated,
            base_field_limb: base_field_limb,
            representation_params: params,
            value: this_value,
            may_need_reduction: false,
        })
    }

    pub fn new_constant(
        value: BigUint,
        params: &'a RnsParameters<E, F>
    ) -> Result<Self, SynthesisError> {
        let binary_limb_values = split_into_fixed_width_limbs(value.clone(), params.binary_limbs_params.limb_size_bits);
        assert!(binary_limb_values.len() <= params.num_binary_limbs);
        let base_limb = value.clone() % &params.base_field_modulus;

        let binary_limbs: Vec<_> = binary_limb_values.into_iter().map(|el| biguint_to_fe(el)).collect();
        let base_limb = biguint_to_fe(base_limb);

        let mut binary_limbs_allocated = Vec::with_capacity(binary_limbs.len());
        for ((l, width), max_val) in binary_limbs.into_iter()
            .zip(params.binary_limbs_bit_widths.iter())
            .zip(params.binary_limbs_max_values.iter()) 
        {
            let limb_type = LimbType::Constant(l);
            let limb = Limb::<E>::new_from_type(
                limb_type,
                max_val.clone(),
                *width
            );

            binary_limbs_allocated.push(limb);
        }

        let zero_limb = Self::zero_limb();
        binary_limbs_allocated.resize(params.num_binary_limbs, zero_limb);

        let base_limb = Limb::<E>::new_from_type(
            LimbType::Constant(base_limb),
            params.base_field_modulus.clone(),
            params.base_field_modulus.bits()
        );

        let val = biguint_to_fe(value);

        Ok(Self {
            binary_limbs: binary_limbs_allocated,
            base_field_limb: base_limb,
            representation_params: params,
            value: val,
            may_need_reduction: false,
        })
    }

    fn zero_limb() -> Limb<E> {
        let l = LimbType::Constant(E::Fr::zero());
        let limb = Limb::<E>::new_from_type(
            l,
            BigUint::from(0u64),
            0
        );

        limb
    }

    fn one_limb() -> Limb<E> {
        let one_limb = LimbType::Constant(E::Fr::one());
        let limb = Limb::<E>::new_from_type(
            one_limb,
            BigUint::from(1u64),
            1
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
            base_field_limb: zero_limb,
            representation_params: params,
            value: F::zero(),
            may_need_reduction: false,
        }
    }

    pub fn one(
        params: &'a RnsParameters<E, F>
    ) -> Self {
        let one_limb = Self::one_limb();
        let zero_limb = Self::zero_limb();

        let mut binary_limbs = Vec::with_capacity(params.num_binary_limbs);
        binary_limbs.push(one_limb.clone());
        binary_limbs.resize(params.num_binary_limbs, zero_limb.clone());
    
        Self {
            binary_limbs: binary_limbs,
            base_field_limb: one_limb,
            representation_params: params,
            value: F::one(),
            may_need_reduction: false,
        }
    }

    // return current value unreduced
    fn get_value(&self) -> BigUint {
        let shift = self.representation_params.binary_limbs_params.limb_size_bits;

        let mut result = BigUint::from(0u64);

        for l in self.binary_limbs.iter().rev() {
            result <<= shift;
            result += l.get_value();
        }

        result
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
            match l.limb_type {
                LimbType::Variable(..) => {
                    return false;
                }
                _ => {}
            }
        }

        match &self.base_field_limb.limb_type {
            LimbType::Variable(..) => {
                return false;
            }
            _ => {}
        }

        true
    }

    pub fn reduce_if_necessary<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS
    ) -> Result<Self, SynthesisError> {
        if self.is_constant() {
            let value = self.get_value() % &self.representation_params.represented_field_modulus;
            return Self::new_constant(value, self.representation_params);
        }

        // let's see if we ever need to reduce individual limbs into the default ranges
        println!("Self value = {}", self.get_max_value().to_str_radix(16));
        println!("Max representable = {}", self.representation_params.max_representable_value().to_str_radix(16));
        // first trivial check
        let mut needs_reduction = self.get_max_value() > self.representation_params.max_representable_value();
        println!("Needs reduction = {}", needs_reduction);
        let max_limb_value = &self.representation_params.binary_limbs_params.limb_max_intermediate_value;
        for binary_limb in self.binary_limbs.iter() {
            needs_reduction = needs_reduction || &binary_limb.get_value() > max_limb_value;
        }
        
        if needs_reduction {
            return self.reduction_impl(cs);
        }

        Ok(self.clone())
    }

    fn reduction_impl<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS
    ) -> Result<Self, SynthesisError> {
        // first perform actual reduction in the field that we try to represent
        let (q, rem) = self.get_value().div_rem(&self.representation_params.represented_field_modulus);
        let q_fe = biguint_to_fe::<F>(q.clone());
        // calculate metaparaters for later on

        let max_q_bits = (self.get_max_value() / &self.representation_params.represented_field_modulus).bits() + 1;
        assert!(max_q_bits <= self.representation_params.binary_limbs_params.limb_intermediate_value_capacity);

        let limb = AllocatedLimb::alloc_with_bit_limit(cs, q, max_q_bits)?;
        let max_value = BigUint::from(1u64) << max_q_bits;
        let q_limb = Limb::<E>::new_from_type(
            LimbType::Variable(limb),
            max_value,
            max_q_bits
        );

        // other limbs are zeroes
        let q_empty_limb = Limb::<E>::new_from_type(
            LimbType::Constant(E::Fr::zero()),
            BigUint::from(0u64),
            0,
        );

        let mut q_new_binary_limbs = Vec::with_capacity(self.binary_limbs.len());
        q_new_binary_limbs.push(q_limb.clone());
        q_new_binary_limbs.resize(self.binary_limbs.len(), q_empty_limb);

        let q_base_field_limb = q_limb;

        let q_as_field_repr = Self {
            binary_limbs: q_new_binary_limbs,
            base_field_limb: q_base_field_limb,
            representation_params: self.representation_params,
            value: q_fe,
            may_need_reduction: false,
        };

        println!("Quotient value = {}", q_as_field_repr.get_value().to_str_radix(16));

        // create remainder

        let r_fe = biguint_to_fe::<F>(rem);

        let r_as_field_repr = Self::new_allocated(
            cs,
            r_fe,
            self.representation_params
        )?;

        println!("remainder value = {}", r_as_field_repr.get_value().to_str_radix(16));

        // perform constraining by implementing multiplication
        // x = q*p + r

        let one = Self::one(self.representation_params);
        println!("One = {}", one.get_value().to_str_radix(16));
        println!("One max = {}", one.get_max_value().to_str_radix(16));

        Self::constraint_fma_with_multiple_additions(
            cs,
            &self, 
            &one,
            &[],
            &q_as_field_repr, 
            &r_as_field_repr,
            self.representation_params
        )?;

        Ok(r_as_field_repr)
    }

    fn slice_into_double_limb_witnesses<CS: ConstraintSystem<E>>(
        value: BigUint,
        cs: &mut CS,
        params: &RnsParameters<E, F>,
    ) -> Result<Vec<Num<E>>, SynthesisError> {
        let num_witness = params.num_binary_limbs / 2;
        let witness_limbs = split_into_fixed_number_of_limbs(value, params.binary_limbs_params.limb_size_bits * 2, num_witness);

        let mut witnesses = vec![];
        for l in witness_limbs.into_iter() {
            let v = biguint_to_fe::<E::Fr>(l);
            let w = AllocatedNum::alloc(cs, 
            || {
                Ok(v)
            })?;

            witnesses.push(Num::Variable(w));
        }

        Ok(witnesses)
    }

    pub fn mul<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        other: &Self
    ) -> Result<Self, SynthesisError> {
        let this = self.reduce_if_necessary(cs)?;
        let other = other.reduce_if_necessary(cs)?;

        let value = this.get_value() * other.get_value();
        let (q, r) = value.div_rem(&self.representation_params.represented_field_modulus);

        if this.is_constant() && other.is_constant() {
            return Self::new_constant(r, &*self.representation_params);
        }

        let q_wit = Self::slice_into_double_limb_witnesses(q, cs, &*self.representation_params)?;
    
        let q_elem = Self::from_double_size_limb_witnesses(
            cs, 
            &q_wit, 
            true, 
            self.representation_params
        )?;

        let r_wit = Self::slice_into_double_limb_witnesses(r, cs, &*self.representation_params)?;
    
        let r_elem = Self::from_double_size_limb_witnesses(
            cs, 
            &r_wit, 
            false, 
            self.representation_params
        )?;

        Self::constraint_fma_with_multiple_additions(
            cs, 
            &this,
            &other,
            &[],
            &q_elem,
            &r_elem,
            &*self.representation_params
        )?;

        Ok(r_elem)
    }

    fn constraint_fma_with_multiple_additions<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        mul_a: &Self,
        mul_b: &Self,
        addition_elements: &[Self],
        result_quotient: &Self,
        result_remainder: &Self,
        params: &RnsParameters<E, F>
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

        // we also should keep in mind that we work not just with "limb",
        // but in RNS, so we "wrap around", so if we have e.g. 2 limbs, then
        // combination like a{2} * b{1} will wrap and go into result{0}

        // each result limb will have uncollapsed set of intermediate limbs
        let mut result_limbs = vec![vec![]; params.num_binary_limbs];

        let target_limbs = params.num_binary_limbs;

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
                let mut q_limb = result_quotient.binary_limbs[i].clone();
                q_limb.scale(&params.represented_field_modulus_negated_limbs[j]);
                let tmp = Self::dirty_limb_fma(cs, &mul_a.binary_limbs[i], &mul_b.binary_limbs[j], &q_limb)?;

                result_limbs[target].push(tmp);
            }
        }

        // now we need to process over additions and remainder
        let mut collapsed_limbs = vec![];
        for (limb_idx, components) in result_limbs.into_iter().enumerate() {
            assert!(components.len() > 0);
            let r = Self::collapse_contributions(cs, components)?;
            println!("Collapsed limb value without remainder and additions = {}", r.get_value().to_str_radix(16));
            collapsed_limbs.push(r);
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

        let mut to_range_check = vec![];

        for t in 2..target_limbs {
            let mut contributions = vec![];
            for (shift, i) in ((t-2)..t).enumerate() {
                let c = if shift == 0 {
                    shift_right_two_limb_constant
                } else if shift == 1 {
                    shift_right_one_limb_constant
                } else {
                    unreachable!()
                };

                let mut tmp = collapsed_limbs[i].clone();
                println!("Limb {} = {}", i, tmp.get_value().to_str_radix(16));
                tmp.scale(&c);
                println!("Tmp shifted by {} = {}", 2-shift, tmp.get_value().to_str_radix(16));

                contributions.push(tmp);

                let mut tmp = result_remainder.binary_limbs[i].clone();
                println!("Remainder {} = {}", i, tmp.get_value().to_str_radix(16));
                tmp.scale(&c);
                tmp.unsafe_negate();
                println!("Tmp shifted by {} and negated = {}", 2-shift, tmp.get_value().to_str_radix(16));
                contributions.push(tmp);

                for addition_element in addition_elements.iter() {
                    let mut tmp = addition_element.binary_limbs[i].clone();
                    tmp.scale(&c);
                    println!("Tmp from addition shifted by {} = {}", 2-shift, tmp.get_value());
                    contributions.push(tmp);
                }
            }

            println!("Combining contributions for t = {}", t);
            // now collapse contributions
            let r = Self::collapse_contributions(cs, contributions)?;

            to_range_check.push(r);
        }

        // TODO: perform multipacking 
        for r in to_range_check.into_iter() {
            let expected_bits = r.max_bits();
            let value = r.collapse_into_num(cs)?;

            match value {
                Num::Constant(val) => {
                    let f = fe_to_biguint(&val);
                    assert!(f.bits() <= expected_bits);
                },
                Num::Variable(var) => {
                    constraint_num_bits(cs, var.get_variable(), expected_bits)?;
                }
            }
        }

        unimplemented!();
    }

    // TODO: Move such functionality into Num and LC
    fn dirty_limb_addition<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        x: &Limb<E>,
        y: &Limb<E>,
    ) -> Result<Limb<E>, SynthesisError> {
        let x_is_constant = x.is_constant();
        let y_is_constant = y.is_constant();

        match (x_is_constant, y_is_constant) {
            (true, true) => {
                let mut result = x.collapse_into_constant();
                result.add_assign(&y.collapse_into_constant());

                let limb = Limb::<E>::new_from_type(
                    LimbType::Constant(result),
                    fe_to_biguint(&result),
                    get_num_bits(&result)
                );

                return Ok(limb);
            },
            (false, true) | (true, false) => {
                let constant = if x_is_constant {
                    x.collapse_into_constant()
                } else {
                    y.collapse_into_constant()
                };

                let mut result = if x_is_constant {
                    y.clone()
                } else {
                    x.clone()
                };

                result.add_assign_constant(&constant);

                return Ok(result);
            },
            (false, false) => {
                let mut constant_term = x.constant_term;
                constant_term.add_assign(&y.constant_term);

                let mut new_var_value = x.get_field_value();
                new_var_value.add_assign(&y.get_field_value());

                let allocated_limb = AllocatedLimb::alloc(cs, new_var_value)?;

                let mut term = MainGateTerm::<E>::new();
                let t0 = ArithmeticTerm::from_variable_and_coeff(x.get_variable(), x.coeff);
                let t2 = ArithmeticTerm::from_variable_and_coeff(y.get_variable(), y.coeff);
                let c = ArithmeticTerm::constant(constant_term);
                let n = ArithmeticTerm::from_variable(allocated_limb.variable);

                term.add_assign(t0);
                term.add_assign(t2);
                term.add_assign(c);
                term.sub_assign(n);

                cs.allocate_main_gate(term)?;

                let mut max_bits = std::cmp::max(x.max_bits(), y.max_bits());
                max_bits += 1; // addition

                assert!(max_bits <= E::Fr::CAPACITY as usize);

                let max_value = x.max_value() + &y.max_value();

                let limb = Limb::new_from_type(
                    LimbType::Variable(allocated_limb), 
                    max_value, 
                    max_bits
                );

                return Ok(limb);
            }
        }
    }

    fn dirty_three_limb_addition<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        x: &Limb<E>,
        y: &Limb<E>,
        z: &Limb<E>
    ) -> Result<Limb<E>, SynthesisError> {
        assert!(CS::Params::STATE_WIDTH >= 4);

        let x_is_constant = x.is_constant();
        let y_is_constant = y.is_constant();
        let z_is_constant = z.is_constant();

        match (x_is_constant, y_is_constant, z_is_constant) {
            (true, true, true) => {
                let mut result = x.collapse_into_constant();
                result.add_assign(&y.collapse_into_constant());
                result.add_assign(&z.collapse_into_constant());

                let limb = Limb::<E>::new_from_type(
                    LimbType::Constant(result),
                    fe_to_biguint(&result),
                    get_num_bits(&result)
                );

                return Ok(limb);
            },
            (true, true, false) | (false, true, true) | (true, false, true)=> {
                let result = if !x_is_constant {
                    let mut value = y.collapse_into_constant();
                    value.add_assign(&z.collapse_into_constant());

                    let mut result = x.clone();
                    result.add_assign_constant(&value);

                    result
                } else if !y_is_constant {
                    let mut value = x.collapse_into_constant();
                    value.add_assign(&z.collapse_into_constant());

                    let mut result = y.clone();
                    result.add_assign_constant(&value);

                    result
                } else {
                    let mut value = x.collapse_into_constant();
                    value.add_assign(&y.collapse_into_constant());

                    let mut result = z.clone();
                    result.add_assign_constant(&value);

                    result
                };

                return Ok(result);
            },
            (true, false, false) | (false, true, false) | (false, false, true) => {
                let (a, b, value) = if x_is_constant {
                    (y, z, x.collapse_into_constant())
                } else if y_is_constant {
                    (x, z, y.collapse_into_constant())
                } else {
                    (x, y, z.collapse_into_constant())
                };

                let mut constant_value = a.constant_term;
                constant_value.add_assign(&b.constant_term);
                constant_value.add_assign(&value);

                let mut new_var_value = a.get_field_value();
                new_var_value.add_assign(&b.get_field_value());
                new_var_value.add_assign(&value);

                let allocated_limb = AllocatedLimb::alloc(cs, new_var_value)?;

                let mut term = MainGateTerm::<E>::new();
                let t0 = ArithmeticTerm::from_variable_and_coeff(a.get_variable(), a.coeff);
                let t1 = ArithmeticTerm::from_variable_and_coeff(b.get_variable(), b.coeff);
                let c = ArithmeticTerm::constant(constant_value);
                let n = ArithmeticTerm::from_variable(allocated_limb.variable);

                term.add_assign(t0);
                term.add_assign(t1);
                term.add_assign(c);
                term.sub_assign(n);

                cs.allocate_main_gate(term)?;

                let mut max_bits = std::cmp::max(a.max_bits(), b.max_bits());
                max_bits += 2; // two additions

                assert!(max_bits <= E::Fr::CAPACITY as usize);

                let max_value = a.max_value() + &b.max_value() + fe_to_biguint(&value);

                let limb = Limb::new_from_type(
                    LimbType::Variable(allocated_limb), 
                    max_value, 
                    max_bits
                );

                return Ok(limb);
            },

            (false, false, false) => {
                let mut constant_value = x.constant_term;
                constant_value.add_assign(&y.constant_term);
                constant_value.add_assign(&z.constant_term);

                let mut new_var_value = x.get_field_value();
                new_var_value.add_assign(&y.get_field_value());
                new_var_value.add_assign(&z.get_field_value());

                let allocated_limb = AllocatedLimb::alloc(cs, new_var_value)?;

                let mut term = MainGateTerm::<E>::new();
                let t0 = ArithmeticTerm::from_variable_and_coeff(x.get_variable(), x.coeff);
                let t1 = ArithmeticTerm::from_variable_and_coeff(y.get_variable(), y.coeff);
                let t2 = ArithmeticTerm::from_variable_and_coeff(z.get_variable(), z.coeff);
                let c = ArithmeticTerm::constant(constant_value);
                let n = ArithmeticTerm::from_variable(allocated_limb.variable);

                term.add_assign(t0);
                term.add_assign(t1);
                term.add_assign(t2);
                term.add_assign(c);
                term.sub_assign(n);

                cs.allocate_main_gate(term)?;

                let mut max_bits = std::cmp::max(x.max_bits(), y.max_bits());
                max_bits = std::cmp::max(max_bits, z.max_bits());
                max_bits += 2; // two additions

                assert!(max_bits <= E::Fr::CAPACITY as usize);

                let max_value = x.max_value() + &y.max_value() + &z.max_value();

                let limb = Limb::new_from_type(
                    LimbType::Variable(allocated_limb), 
                    max_value, 
                    max_bits
                );

                return Ok(limb);
            }
        }
    }

    // TODO: Move such functionality into Num and LC
    fn dirty_limb_fma<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        mul_x: &Limb<E>,
        mul_y: &Limb<E>,
        add_z: &Limb<E>
    ) -> Result<Limb<E>, SynthesisError> {
        let x_is_constant = mul_x.is_constant();
        let y_is_constant = mul_y.is_constant();
        let z_is_constant = add_z.is_constant();

        match (x_is_constant, y_is_constant, z_is_constant) {
            (true, true, true) => {
                let mut result = mul_x.collapse_into_constant();
                result.mul_assign(&mul_y.collapse_into_constant());
                result.add_assign(&add_z.collapse_into_constant());

                let limb = Limb::<E>::new_from_type(
                    LimbType::Constant(result),
                    fe_to_biguint(&result),
                    get_num_bits(&result)
                );

                return Ok(limb);
            },
            (true, true, false) => {
                let mut value = mul_x.collapse_into_constant();
                value.mul_assign(&mul_y.collapse_into_constant());

                let mut result = add_z.clone();
                result.add_assign_constant(&value);

                return Ok(result);
            },
            (true, false, true) | (false, true, true)=> {
                let additive_constant = add_z.collapse_into_constant();
                let multiplicative_constant = if x_is_constant {
                    mul_x.collapse_into_constant()
                } else {
                    mul_y.collapse_into_constant()
                };

                let mut result = if x_is_constant {
                    mul_y.clone()
                } else {
                    mul_x.clone()
                };

                result.scale(&multiplicative_constant);
                result.add_assign_constant(&additive_constant);

                return Ok(result);
            },
            (true, false, false) | (false, true, false) => {
                let multiplicative_constant = if x_is_constant {
                    mul_x.collapse_into_constant()
                } else {
                    mul_y.collapse_into_constant()
                };

                let mut tmp = if x_is_constant {
                    mul_y.clone()
                } else {
                    mul_x.clone()
                };

                tmp.scale(&multiplicative_constant);

                let mut constant_term = tmp.constant_term;
                constant_term.add_assign(&add_z.constant_term);

                let mut new_var_value = tmp.get_field_value();
                new_var_value.add_assign(&add_z.get_field_value());

                let allocated_limb = AllocatedLimb::alloc(cs, new_var_value)?;

                let mut term = MainGateTerm::<E>::new();
                let t0 = ArithmeticTerm::from_variable_and_coeff(tmp.get_variable(), tmp.coeff);
                let t2 = ArithmeticTerm::from_variable_and_coeff(add_z.get_variable(), add_z.coeff);
                let c = ArithmeticTerm::constant(constant_term);
                let n = ArithmeticTerm::from_variable(allocated_limb.variable);

                term.add_assign(t0);
                term.add_assign(t2);
                term.add_assign(c);
                term.sub_assign(n);

                cs.allocate_main_gate(term)?;

                let mut max_bits = std::cmp::max(tmp.max_bits(), add_z.max_bits());
                max_bits += 1; // addition

                assert!(max_bits <= E::Fr::CAPACITY as usize);

                let max_value = tmp.max_value() + &add_z.max_value();

                let limb = Limb::new_from_type(
                    LimbType::Variable(allocated_limb), 
                    max_value, 
                    max_bits
                );

                return Ok(limb);
            },
            (false, false, true) => {
                let mut mul_coeff = mul_x.coeff;
                mul_coeff.mul_assign(&mul_y.coeff);

                let mut x_coeff = mul_x.coeff;
                x_coeff.mul_assign(&mul_y.constant_term);

                let mut y_coeff = mul_y.coeff;
                y_coeff.mul_assign(&mul_x.constant_term);

                let mut constant_coeff = mul_x.constant_term;
                constant_coeff.add_assign(&mul_y.constant_term);
                constant_coeff.add_assign(&add_z.collapse_into_constant());

                let x_var = mul_x.get_variable();
                let y_var = mul_y.get_variable();

                let x_value = mul_x.get_field_value();
                let y_value = mul_y.get_field_value();
                let z_value = add_z.get_field_value();

                let mut new_value = x_value;
                new_value.mul_assign(&y_value);
                new_value.add_assign(&z_value);

                let allocated_limb = AllocatedLimb::alloc(cs, new_value)?;

                let mut term = MainGateTerm::<E>::new();
                let mul_term = ArithmeticTerm::<E>::from_variable_and_coeff(x_var, mul_coeff).mul_by_variable(y_var);
                let x_term = ArithmeticTerm::<E>::from_variable_and_coeff(x_var, x_coeff);
                let y_term = ArithmeticTerm::<E>::from_variable_and_coeff(y_var, y_coeff);
                let n_term = ArithmeticTerm::<E>::from_variable(allocated_limb.variable);
                let const_term = ArithmeticTerm::constant(constant_coeff);

                term.add_assign(mul_term);
                term.add_assign(x_term);
                term.add_assign(y_term);
                term.add_assign(const_term);
                term.sub_assign(n_term);

                let mut max_bits = std::cmp::max(mul_x.max_bits() * mul_y.max_bits(), add_z.max_bits());
                max_bits += 1;

                let max_value = (mul_x.max_value() * & mul_y.max_value()) + &add_z.max_value();

                let limb = Limb::new_from_type(
                    LimbType::Variable(allocated_limb), 
                    max_value, 
                    max_bits
                );

                return Ok(limb);
            },
            (false, false, false) => {
                // each limb is something like a*X + b
                // in this case we have do manually unroll it

                // a_0 * X * a_1 * Y + (a_0 * X * b_1 + a_1 * Y * b_0 + a_2 * Z) + (b_0 + b_1 + b_2)

                let mut mul_coeff = mul_x.coeff;
                mul_coeff.mul_assign(&mul_y.coeff);

                let mut x_coeff = mul_x.coeff;
                x_coeff.mul_assign(&mul_y.constant_term);

                let mut y_coeff = mul_y.coeff;
                y_coeff.mul_assign(&mul_x.constant_term);

                let mut constant_coeff = mul_x.constant_term;
                constant_coeff.add_assign(&mul_y.constant_term);
                constant_coeff.add_assign(&add_z.constant_term);

                let x_var = mul_x.get_variable();
                let y_var = mul_y.get_variable();
                let z_var = add_z.get_variable();

                let x_value = mul_x.get_field_value();
                let y_value = mul_y.get_field_value();
                let z_value = add_z.get_field_value();

                let mut new_value = x_value;
                new_value.mul_assign(&y_value);
                new_value.add_assign(&z_value);

                let allocated_limb = AllocatedLimb::alloc(cs, new_value)?;

                let mut term = MainGateTerm::<E>::new();
                let mul_term = ArithmeticTerm::<E>::from_variable_and_coeff(x_var, mul_coeff).mul_by_variable(y_var);
                let x_term = ArithmeticTerm::<E>::from_variable_and_coeff(x_var, x_coeff);
                let y_term = ArithmeticTerm::<E>::from_variable_and_coeff(y_var, y_coeff);
                let z_term = ArithmeticTerm::<E>::from_variable_and_coeff(z_var, add_z.coeff);
                let n_term = ArithmeticTerm::<E>::from_variable(allocated_limb.variable);
                let const_term = ArithmeticTerm::constant(constant_coeff);

                term.add_assign(mul_term);
                term.add_assign(x_term);
                term.add_assign(y_term);
                term.add_assign(z_term);
                term.add_assign(const_term);
                term.sub_assign(n_term);

                let mut max_bits = std::cmp::max(mul_x.max_bits() * mul_y.max_bits(), add_z.max_bits());
                max_bits += 1;

                let max_value = (mul_x.max_value() * & mul_y.max_value()) + &add_z.max_value();

                let limb = Limb::new_from_type(
                    LimbType::Variable(allocated_limb), 
                    max_value, 
                    max_bits
                );

                return Ok(limb);
            }
        }
    }

    fn collapse_contributions<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        components: Vec<Limb<E>>
    ) -> Result<Limb<E>, SynthesisError> {
        if components.len() == 1 {
            return Ok(components[0].clone());
        } else if components.len() & 1 == 0 {
            let len = components.len();
            let mut i = 0;
            let mut tmp = Self::dirty_limb_addition(cs, &components[i], &components[i+1])?;
            println!("tmp value = {}", tmp.get_value());
            println!("tmp value = {}, field value = {}", tmp.get_value(), tmp.get_field_value());
            i += 2;
            let rounds = (len / 2) - 1;
            for _ in 0..rounds {
                tmp = Self::dirty_three_limb_addition(cs, &tmp, &components[i], &components[i+1])?;
                println!("tmp value = {}, field value = {}", tmp.get_value(), tmp.get_field_value());
                i += 2;
            }
            
            return Ok(tmp);
        } else {
            let len = components.len();
            let mut i = 0;
            let mut tmp = Self::dirty_limb_addition(cs, &components[i], &components[i+1])?;
            println!("tmp value = {}, field value = {}", tmp.get_value(), tmp.get_field_value());
            i += 2;
            let rounds = (len-1) / 2 - 1;
            for _ in 0..rounds {
                tmp = Self::dirty_three_limb_addition(cs, &tmp, &components[i], &components[i+1])?;
                println!("tmp value = {}, field value = {}", tmp.get_value(), tmp.get_field_value());
                i += 2;
            }
            tmp = Self::dirty_limb_addition(cs, &tmp, &components[i])?;
            println!("tmp value = {}, field value = {}", tmp.get_value(), tmp.get_field_value());
            
            return Ok(tmp);
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::bellman::pairing::bn256::{Fq, Bn256, Fr};

    #[test]
    fn test_constant_propagation() {
        let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNextEquation>::new();

        let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110);

        let a = Fq::from_str("1234").unwrap();
        let b = Fq::from_str("5678").unwrap();

        let a = FieldElement::new_constant(BigUint::from(1234u64), &params).unwrap();
        println!("{}", a.get_value());
        println!("{}", a.get_max_value());
        let b = FieldElement::new_constant(BigUint::from(5678u64), &params).unwrap();

        let result = a.mul(&mut cs, &b).unwrap();

        assert_eq!(result.get_value(), BigUint::from(1234u64) * BigUint::from(5678u64));
    }

    #[test]
    fn test_witness_propagation() {
        let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNextEquation>::new();

        let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110);

        let a = Fq::from_str("1234").unwrap();
        let b = Fq::from_str("5678").unwrap();

        let a = FieldElement::new_allocated(
            &mut cs, 
            Fq::from_str("1234").unwrap(), 
            &params
        ).unwrap();
        let b = FieldElement::new_allocated(
            &mut cs, 
            Fq::from_str("5678").unwrap(), 
            &params
        ).unwrap();

        let result = a.mul(&mut cs, &b).unwrap();

        assert_eq!(result.get_value(), BigUint::from(1234u64) * BigUint::from(5678u64));
    }


}