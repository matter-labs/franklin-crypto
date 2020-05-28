use crate::plonk::circuit::allocated_num::*;
use crate::plonk::circuit::linear_combination::*;
use crate::plonk::circuit::rescue::*;
use crate::rescue::*;

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
    fn produce_challenge<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<LinearCombination<E>, SynthesisError>;
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

    fn produce_challenge<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<LinearCombination<E>, SynthesisError> {
        self.state.squeeze_out_single(cs, &self.params)
    }
}