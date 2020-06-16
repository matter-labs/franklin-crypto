use crate::plonk::circuit::allocated_num::*;
use crate::plonk::circuit::linear_combination::*;
use crate::plonk::circuit::rescue::*;
use crate::rescue::*;

use crate::plonk::circuit::curve::sw_affine::AffinePoint;
use crate::plonk::circuit::bigint::field::*;
use crate::plonk::circuit::verifier_circuit::affine_point_wrapper::WrappedAffinePoint;

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
        self.state.absorb(cs, &[data], &self.params)    
    }

    fn consume_point<'a, CS: ConstraintSystem<E>, WP: WrappedAffinePoint<'a, E>>(
        &mut self, 
        cs: &mut CS,
        data: WP,
    ) -> Result<(), SynthesisError> {
        
        // our strategy here is to consume x mod Pq and y mod Pq,
        let x = data.get_point().x.base_field_limb.collapse_into_num(cs)?.get_variable();
        let y = data.get_point().y.base_field_limb.collapse_into_num(cs)?.get_variable();
        let zero = AllocatedNum::zero(cs);

        let selected_x = AllocatedNum::conditionally_select(cs, &zero, &x, &data.get_zero_flag())?;
        let selected_y = AllocatedNum::conditionally_select(cs, &zero, &y, &data.get_zero_flag())?;
        
        self.state.absorb(cs, &[selected_x, selected_y], &self.params)   
    }

    fn produce_challenge<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<AllocatedNum<E>, SynthesisError> {
        let temp = self.state.squeeze_out_single(cs, &self.params)?;
        temp.into_allocated_num(cs)
    }
}