use crate::bellman::pairing::{
    Engine,
    GenericCurveAffine,
    GenericCurveProjective
};

use crate::bellman::pairing::ff::{
    Field,
    PrimeField,
    PrimeFieldRepr,
    BitIterator,
    ScalarEngine
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
    TrivialAssembly,
    PlonkCsWidth4WithNextStepParams,
};

use super::super::allocated_num::{AllocatedNum, Num};
use super::super::linear_combination::LinearCombination;
use super::super::simple_term::Term;
use super::super::boolean::{Boolean, AllocatedBit};

use num_bigint::BigUint;
use num_integer::Integer;

use super::super::bigint::field::*;
use super::super::bigint::bigint::*;

use super::sw_affine::*;
use super::selection_table::*;

pub struct MultiexpTable<'a, E: Engine, G: GenericCurveAffine> where G::Base: PrimeField {
    width_four_tables: Vec<Vec<[SelectorTable<E, Term<E>>; 2]>>,
    width_three_table: Option<Vec<[SelectorTable<E, Term<E>>; 2]>>,
    width_two_table: Option<Vec<[SelectorTable<E, Term<E>>; 2]>>,
    width_one_elements: Option<[AffinePoint<'a, E, G>; 2]>,
    width_four_table_elements: Vec<Vec<AffinePoint<'a, E, G>>>,
    width_three_table_elements: Option<Vec<AffinePoint<'a, E, G>>>,
    width_two_table_elements: Option<Vec<AffinePoint<'a, E, G>>>,
    params: &'a RnsParameters<E, G::Base>,
    pub width: usize,
}

impl<'a, E: Engine, G: GenericCurveAffine> MultiexpTable<'a, E, G> where G::Base: PrimeField {
    #[track_caller]
    pub fn new<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        points: &[AffinePoint<'a, E, G>]
    ) -> Result<Self, SynthesisError> {
        let params = points[0].x.representation_params;

        let width = points.len();

        let num_width_four_tables = points.len() / 4;

        let mut remainder = points;

        let mut width_four_tables = Vec::with_capacity(num_width_four_tables);
        let mut width_four_table_elements = Vec::with_capacity(num_width_four_tables);
        for _ in 0..num_width_four_tables {
            let (chunk, other) = remainder.split_at(4);

            let (table, entries) = Self::make_width_four_table(cs, chunk)?;

            width_four_tables.push(table);
            width_four_table_elements.push(entries);

            remainder = other;
        }

        assert!(remainder.len() < 4);

        let mut width_three_table = None;
        let mut width_two_table = None;
        let mut single_bit_pair = None;

        let mut width_three_table_elements = None;
        let mut width_two_table_elements = None;

        match remainder.len() {
            0 => {},
            1 => {
                let mut point = remainder[0].clone();
                let (minus_y, y) = point.y.clone().negated(cs)?;
                point.y = y;

                let mut point_negated = point.clone();
                point_negated.y = minus_y;
                if let Some(v) = point_negated.value.as_mut() {
                    v.negate();
                }

                single_bit_pair = Some([point_negated, point]);
            },
            2 => {
                let (t, e) = Self::make_width_two_table(cs, remainder)?;
                width_two_table = Some(t);
                width_two_table_elements = Some(e);
            },
            3 => {
                let (t, e) = Self::make_width_three_table(cs, remainder)?;
                width_three_table = Some(t);
                width_three_table_elements = Some(e);
            },
            _ => {
                unreachable!()
            }
        };

        let table = Self {
            width_four_tables,
            width_three_table,
            width_two_table,
            width_one_elements: single_bit_pair,
            width_four_table_elements,
            width_three_table_elements,
            width_two_table_elements,
            params: params,
            width
        };

        Ok(table)
    }

    #[track_caller]
    fn make_width_four_table<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        chunk: &[AffinePoint<'a, E, G>]
    ) -> Result<(Vec<[SelectorTable< E, Term<E>>; 2]>, Vec<AffinePoint<'a, E, G>>), SynthesisError> {
        assert_eq!(chunk.len(), 4);
        // first we need to shuffle points themselves

        let mut limb_selection_tables = vec![];

        // combination between pairs
        let (tmp_0, (original_1, original_0)) = chunk[1].clone().add_unequal(cs, chunk[0].clone())?;
        let (tmp_1, _) = original_1.sub_unequal(cs, original_0)?;
        let (tmp_2, (original_3, original_2)) = chunk[3].clone().add_unequal(cs, chunk[2].clone())?;
        let (tmp_3, _) = original_3.sub_unequal(cs, original_2)?;

        // combinations of combinations of pairs

        let (entry_0, (tmp_2, tmp_0)) = tmp_2.add_unequal(cs, tmp_0)?;
        let (entry_1, (tmp_2, tmp_1)) = tmp_2.add_unequal(cs, tmp_1)?;

        let (entry_2, (tmp_2, tmp_1)) = tmp_2.sub_unequal(cs, tmp_1)?;
        let (entry_3, (_, tmp_0)) = tmp_2.sub_unequal(cs, tmp_0)?;

        let (entry_4, (tmp_3, tmp_0)) = tmp_3.add_unequal(cs, tmp_0)?;
        let (entry_5, (tmp_3, tmp_1)) = tmp_3.add_unequal(cs, tmp_1)?;

        let (entry_6, (tmp_3, _)) = tmp_3.sub_unequal(cs, tmp_1)?;
        let (entry_7, _) = tmp_3.sub_unequal(cs, tmp_0)?;

        let params = entry_0.x.representation_params;

        let entries = vec![
            entry_0, entry_1, entry_2, entry_3, entry_4, entry_5, entry_6, entry_7
        ];

        // now make individual lookup tables for each limb

        for limb_idx in 0..params.num_binary_limbs {
            let mut subentries_x = Vec::with_capacity(entries.len());
            let mut subentries_y = Vec::with_capacity(entries.len());
            for e in entries.iter() {
                let limb_x = e.x.binary_limbs[limb_idx].term.clone();
                subentries_x.push(limb_x);

                let limb_y = e.y.binary_limbs[limb_idx].term.clone();
                subentries_y.push(limb_y);
            }

            let limb_table_x = SelectorTable::new_from_entries(cs, &subentries_x)?;
            let limb_table_y = SelectorTable::new_from_entries(cs, &subentries_y)?;

            limb_selection_tables.push([limb_table_x, limb_table_y]);
        }

        Ok((limb_selection_tables, entries))
    }

    #[track_caller]
    fn make_width_three_table<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        chunk: &[AffinePoint<'a, E, G>]
    ) -> Result<(Vec<[SelectorTable< E, Term<E>>; 2]>, Vec<AffinePoint<'a, E, G>>), SynthesisError> {
        assert_eq!(chunk.len(), 3);
        // first we need to shuffle points themselves

        let mut limb_selection_tables = vec![];

        // combination between pairs
        let (tmp_0, (original_1, original_0)) = chunk[1].clone().add_unequal(cs, chunk[0].clone())?;
        let (tmp_1, _) = original_1.sub_unequal(cs, original_0)?;

        let original_2 = chunk[2].clone();

        // combinations of pairs and point 3

        let (entry_0, (original_2, tmp_0)) = original_2.add_unequal(cs, tmp_0)?;
        let (entry_1, (original_2, tmp_1)) = original_2.add_unequal(cs, tmp_1)?;

        let (entry_2, (original_2, _)) = original_2.sub_unequal(cs, tmp_1)?;
        let (entry_3, _) = original_2.sub_unequal(cs, tmp_0)?;

        let params = entry_0.x.representation_params;

        let entries = vec![
            entry_0, entry_1, entry_2, entry_3
        ];

        // now make individual lookup tables for each limb

        for limb_idx in 0..params.num_binary_limbs {
            let mut subentries_x = Vec::with_capacity(entries.len());
            let mut subentries_y = Vec::with_capacity(entries.len());
            for e in entries.iter() {
                let limb_x = e.x.binary_limbs[limb_idx].term.clone();
                subentries_x.push(limb_x);

                let limb_y = e.y.binary_limbs[limb_idx].term.clone();
                subentries_y.push(limb_y);
            }

            let limb_table_x = SelectorTable::new_from_entries(cs, &subentries_x)?;
            let limb_table_y = SelectorTable::new_from_entries(cs, &subentries_y)?;

            limb_selection_tables.push([limb_table_x, limb_table_y]);
        }

        Ok((limb_selection_tables, entries))
    }

    #[track_caller]
    fn make_width_two_table<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        chunk: &[AffinePoint<'a, E, G>]
    ) -> Result<(Vec<[SelectorTable< E, Term<E>>; 2]>, Vec<AffinePoint<'a, E, G>>), SynthesisError> {
        assert_eq!(chunk.len(), 2);
        // first we need to shuffle points themselves

        let mut limb_selection_tables = vec![];

        // combination between pairs
        let (entry_0, (original_1, original_0)) = chunk[1].clone().add_unequal(cs, chunk[0].clone())?;
        let (entry_1, _) = original_1.sub_unequal(cs, original_0)?;

        let params = entry_0.x.representation_params;

        let entries = vec![
            entry_0, entry_1
        ];

        // now make individual lookup tables for each limb

        for limb_idx in 0..params.num_binary_limbs {
            let mut subentries_x = Vec::with_capacity(entries.len());
            let mut subentries_y = Vec::with_capacity(entries.len());
            for e in entries.iter() {
                let limb_x = e.x.binary_limbs[limb_idx].term.clone();
                subentries_x.push(limb_x);

                let limb_y = e.y.binary_limbs[limb_idx].term.clone();
                subentries_y.push(limb_y);
            }

            let limb_table_x = SelectorTable::new_from_entries(cs, &subentries_x)?;
            let limb_table_y = SelectorTable::new_from_entries(cs, &subentries_y)?;

            limb_selection_tables.push([limb_table_x, limb_table_y]);
        }

        Ok((limb_selection_tables, entries))
    }

    fn select_from_table_two_to_four<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        tables: &Vec<[SelectorTable<E, Term<E>>; 2]>,
        bits: &[Boolean],
        params: &'a RnsParameters<E, G::Base>
    ) -> Result<AffinePoint<'a, E, G>, SynthesisError> {
        assert!(bits.len() >= 2);
        assert!(bits.len() <= 4);
        let negation_bit = bits.last().unwrap().clone();

        let mut selection_bits = Vec::with_capacity(bits.len() - 1);

        for i in (0..(bits.len()-1)).rev() {
            let bb = Boolean::xor(cs, &negation_bit, &bits[i])?;

            selection_bits.push(bb);
        }

        let mut selected_x_limb_terms = Vec::with_capacity(tables.len());
        let mut selected_y_limb_terms = Vec::with_capacity(tables.len());

        for limb_table in tables.iter() {
            let selected_x_term = limb_table[0].select(cs, &selection_bits)?;
            let selected_y_term = limb_table[1].select(cs, &selection_bits)?;

            selected_x_limb_terms.push(selected_x_term);
            selected_y_limb_terms.push(selected_y_term);
        }

        // now reconstruct limbs (add bit width) and base field term 

        let mut shift_constant = E::Fr::one();

        let mut x_limbs = Vec::with_capacity(tables.len());
        let mut y_limbs = Vec::with_capacity(tables.len());

        let mut x_base_chain = Vec::with_capacity(tables.len());
        let mut y_base_chain = Vec::with_capacity(tables.len());

        let mut x_value = BigUint::from(0u64);
        let mut y_value = BigUint::from(0u64);

        let mut value_is_none = false;

        for (limb_idx, ((x_term, y_term), max_value)) in selected_x_limb_terms.into_iter()
                                            .zip(selected_y_limb_terms.into_iter())
                                            .zip(params.binary_limbs_max_values.iter().cloned())
                                            .enumerate()
        {
            let x_limb = Limb::new(
                x_term.clone(),
                max_value.clone()
            );

            if let Some(v) = x_term.get_value() {
                x_value += fe_to_biguint(&v) << (params.binary_limbs_params.limb_size_bits * limb_idx); 
            } else {
                value_is_none = true;
            }

            let y_limb = Limb::new(
                y_term.clone(),
                max_value.clone()
            );

            if let Some(v) = y_term.get_value() {
                y_value += fe_to_biguint(&v) << (params.binary_limbs_params.limb_size_bits * limb_idx); 
            } else {
                value_is_none = true;
            }

            let mut x_base = x_term;
            x_base.scale(&shift_constant);

            let mut y_base = y_term;
            y_base.scale(&shift_constant);

            x_limbs.push(x_limb);
            y_limbs.push(y_limb);

            x_base_chain.push(x_base);
            y_base_chain.push(y_base);

            shift_constant.mul_assign(&params.binary_limbs_params.shift_left_by_limb_constant);
        }

        let (first, other) = x_base_chain.split_first().unwrap();
        let x_base = first.add_multiple(cs, other)?;

        let (first, other) = y_base_chain.split_first().unwrap();
        let y_base = first.add_multiple(cs, other)?;

        let (x, y, point_value) = if value_is_none {
            (None, None, None)
        } else {
            assert!(&x_value < &params.represented_field_modulus);
            assert!(&y_value < &params.represented_field_modulus);

            let x = biguint_to_fe::<G::Base>(x_value);
            let y = biguint_to_fe::<G::Base>(y_value);

            let point = G::from_xy_checked(x, y).unwrap();

            (Some(x), Some(y), Some(point))
        };

        let selected_x = FieldElement::<E, G::Base> {
            binary_limbs: x_limbs,
            base_field_limb: x_base,
            value: x,
            representation_params: params
        };

        let selected_y = FieldElement::<E, G::Base> {
            binary_limbs: y_limbs,
            base_field_limb: y_base,
            value: y,
            representation_params: params
        };

        let (negated_y, selected_y) = selected_y.negated(cs)?;

        let (final_y, _) = FieldElement::select(cs, &negation_bit, negated_y, selected_y)?;

        let point_value = match (point_value, negation_bit.get_value()) {
            (Some(mut val), Some(b)) => {
                if b {
                    val.negate();
                }

                Some(val)
            },
            _ => {
                None
            }
        };

        let point = AffinePoint::<_, _> {
            x: selected_x,
            y: final_y,
            value: point_value
        };

        Ok(point)
    }

    #[track_caller]
    pub fn make_base<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS
    ) -> Result<AffinePoint<'a, E, G>, SynthesisError> {
        let mut queries = vec![];
        for w_4 in self.width_four_table_elements.iter() {
            queries.push(w_4[0].clone());
        }
        if let Some(w_3) = self.width_three_table_elements.as_ref() {
            queries.push(w_3[0].clone());
        }
        if let Some(w_2) = self.width_two_table_elements.as_ref() {
            queries.push(w_2[0].clone());
        }
        if let Some(w_1) = self.width_one_elements.as_ref() {
            // keep in mind that we've swapped the points already!
            queries.push(w_1[1].clone());
        }

        let mut tmp: Vec<_> = queries.drain(0..1).collect();

        let mut base = tmp.pop().unwrap();

        for el in queries.into_iter() {
            let (b, _) = base.add_unequal(cs, el)?;
            base = b;
        }

        Ok(base)
    }

    #[track_caller]
    pub fn lookup_for_skewed_entries<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        bits: &[Boolean]
    ) -> Result<AffinePoint<'a, E, G>, SynthesisError> {
        let mut queries = vec![];

        assert!(self.width == bits.len());

        let mut remainder = bits;

        for w4 in self.width_four_tables.iter() {
            let (b, rest) = remainder.split_at(4);

            let q = Self::select_from_table_two_to_four(cs, w4, b, self.params)?;

            remainder = rest;
            queries.push(q);
        }

        assert!(remainder.len() < 4);

        match remainder.len() {
            0 => {},
            1 => {
                let w1 = self.width_one_elements.as_ref().unwrap();
                let (y, _) = FieldElement::select(cs, &remainder[0], w1[0].y.clone(), w1[1].y.clone())?;
                let x = w1[0].x.clone();

                let new_value = if let Some(b) = remainder[0].get_value() {
                    if b {
                        w1[0].get_value()
                    } else {
                        w1[1].get_value()
                    }
                } else {
                    None
                };

                let point = AffinePoint::<_, _> {
                    x: x,
                    y: y,
                    value: new_value
                };

                queries.push(point);
            },
            2 => {
                let w2 = self.width_two_table.as_ref().unwrap();
                let q = Self::select_from_table_two_to_four(cs, w2, remainder, self.params)?;
                queries.push(q);
            },
            3 => {
                let w3 = self.width_three_table.as_ref().unwrap();
                let q = Self::select_from_table_two_to_four(cs, w3, remainder, self.params)?;
                queries.push(q);
            },
            _ => {
                unreachable!()
            }
        };

        let mut tmp: Vec<_> = queries.drain(0..1).collect();

        let mut base = tmp.pop().unwrap();

        for el in queries.into_iter() {
            let (b, _) = base.add_unequal(cs, el)?;
            base = b;
        }

        Ok(base)
    }
}