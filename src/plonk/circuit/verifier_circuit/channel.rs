use crate::plonk::circuit::allocated_num::*;
use crate::plonk::circuit::linear_combination::*;
use crate::plonk::circuit::rescue::*;
use crate::rescue::*;

use crate::plonk::circuit::curve::sw_affine::AffinePoint;
use crate::plonk::circuit::bigint::field::*;
use crate::plonk::circuit::bigint::bigint::*;
use crate::plonk::circuit::verifier_circuit::affine_point_wrapper::WrappedAffinePoint;

use bellman::pairing::ff::{
    Field,
};

use bellman::pairing::{
    Engine,
};

use crate::bellman::{
    SynthesisError,
};

use crate::bellman::plonk::better_better_cs::cs::{
    ConstraintSystem,
};


pub trait ChannelGadget<E: Engine> {
    type Params;

    fn new(params: &Self::Params) -> Self;

    fn consume<CS: ConstraintSystem<E>>(&mut self, data: AllocatedNum<E>, cs: &mut CS) -> Result<(), SynthesisError>;

    fn consume_point<'a, CS: ConstraintSystem<E>, WP: WrappedAffinePoint<'a, E>>(
        &mut self, 
        cs: &mut CS,
        data: WP,
    ) -> Result<(), SynthesisError>;
    
    fn produce_challenge<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<AllocatedNum<E>, SynthesisError>;
}


pub struct RescueChannelGadget<E: RescueEngine> {
    state: StatefulRescueGadget<E>,
    params: E::Params,
}


impl<E: RescueEngine> ChannelGadget<E> for RescueChannelGadget<E>
where <<E as RescueEngine>::Params as RescueHashParams<E>>::SBox0: PlonkCsSBox<E>, 
    <<E as RescueEngine>::Params as RescueHashParams<E>>::SBox1: PlonkCsSBox<E>
{
    type Params = E::Params;

    fn new(channel_params: &Self::Params) -> Self {
        Self {
            state: StatefulRescueGadget::new(channel_params),
            params: channel_params.clone(),
        }
    }

    fn consume<CS: ConstraintSystem<E>>(&mut self, data: AllocatedNum<E>, cs: &mut CS) -> Result<(), SynthesisError> {  
        self.state.absorb_single_value(cs, Num::Variable(data), &self.params)?;
        // self.state.absorb(cs, &[data], &self.params)    

        Ok(())
    }

    fn consume_point<'a, CS: ConstraintSystem<E>, WP: WrappedAffinePoint<'a, E>>(
        &mut self, 
        cs: &mut CS,
        data: WP,
    ) -> Result<(), SynthesisError> {
        
        // // our strategy here is to consume x mod Pq and y mod Pq,
        // let x = data.get_point().x.base_field_limb.collapse_into_num(cs)?.get_variable();
        // let y = data.get_point().y.base_field_limb.collapse_into_num(cs)?.get_variable();
        // let zero = AllocatedNum::zero(cs);

        // let selected_x = AllocatedNum::conditionally_select(cs, &zero, &x, &data.get_zero_flag())?;
        // let selected_y = AllocatedNum::conditionally_select(cs, &zero, &y, &data.get_zero_flag())?;
        
        // self.state.absorb(cs, &[selected_x, selected_y], &self.params) 

        let params = data.get_point().x.representation_params;

        if params.can_allocate_from_double_limb_witness() {
            let mut num_witness = params.num_limbs_for_in_field_representation / 2;
            if params.num_limbs_for_in_field_representation % 2 != 0 {
                num_witness += 1;
            }

            let mut shift_constant = E::Fr::one();
            for _ in 0..params.binary_limbs_bit_widths[0] {
                shift_constant.double();
            }

            // we need to recalculate and reallocate

            let point = data.get_point();
            let x = &point.x;
            let y = &point.y;

            use crate::plonk::circuit::Assignment;

            let zero = AllocatedNum::zero(cs);

            for coord in vec![x, y] {
                let mut witnesses = vec![];

                for idx in 0..num_witness {
                    let low_idx = 2*idx;
                    let high_idx = 2*idx + 1;

                    let low_term = coord.binary_limbs[low_idx].term.clone();
                    let mut high_term = coord.binary_limbs[high_idx].term.clone();
                    high_term.scale(&shift_constant);

                    let wit = high_term.add(cs, &low_term)?.collapse_into_num(cs)?.get_variable();

                    witnesses.push(wit);
                }
                // let witness_limbs = split_some_into_fixed_number_of_limbs(
                //     coord.get_value(), 
                //     params.binary_limbs_params.limb_size_bits * 2, 
                //     num_witness
                // );
    

                // for l in witness_limbs.into_iter() {
                //     let v = some_biguint_to_fe::<E::Fr>(&l);
                //     let w = AllocatedNum::alloc(cs, 
                //     || {
                //         Ok(*v.get()?)
                //     })?;
    
                //     witnesses.push(w);
                // }

                for w in witnesses.into_iter() {
                    let selected = AllocatedNum::conditionally_select(cs, &zero, &w, &data.get_zero_flag())?;

                    self.consume(selected, cs)?;
                }
            }
        } else {
            let num_witness = params.num_limbs_for_in_field_representation;

            let zero = AllocatedNum::zero(cs);

            let point = data.get_point();

            let x = &point.x;
            let y = &point.y;

            for coord in vec![x, y] {
                for limb in coord.binary_limbs[..num_witness].iter() {
                    let l = limb.collapse_into_num(cs)?.get_variable();

                    let selected = AllocatedNum::conditionally_select(cs, &zero, &l, &data.get_zero_flag())?;

                    self.consume(selected, cs)?;
                }
            }
        }

        Ok(())
    }

    fn produce_challenge<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<AllocatedNum<E>, SynthesisError> {
        self.state.pad_if_necessary(&self.params)?;
        let temp = self.state.squeeze_out_single(cs, &self.params)?;

        temp.into_allocated_num(cs)
    }
}