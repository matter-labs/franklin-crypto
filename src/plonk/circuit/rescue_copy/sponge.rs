use plonk::circuit::rescue_copy::{common::domain_strategy::DomainStrategy, traits::HashParams};
use crate::bellman::pairing::{
    Engine,
};
use crate::bellman::pairing::ff::{
    Field,
    PrimeField,
    PrimeFieldRepr,
    BitIterator
};
use plonk::circuit::rescue_copy::rescue::rescue_round_function;
use plonk::circuit::rescue_copy::poseidon::poseidon_round_function;
use plonk::circuit::rescue_copy::rescue_prime::rescue_prime::rescue_prime_round_function;
use std::convert::TryInto;

pub fn generic_hash<
    E: Engine,
    P: HashParams<E, RATE, WIDTH>,
    const RATE: usize,
    const WIDTH: usize,
    const LENGTH: usize,
>(
    params: &P,
    input: &[E::Fr; LENGTH],
    domain_strategy: Option<DomainStrategy>,
) -> [E::Fr; RATE] {
    GenericSponge::hash(input, params, domain_strategy)
}

#[derive(Clone)]
enum SpongeMode<E: Engine, const RATE: usize> {
    Absorb([Option<E::Fr>; RATE]),
    Squeeze([Option<E::Fr>; RATE]),
}

#[derive(Clone)]
pub struct GenericSponge<E: Engine, const RATE: usize, const WIDTH: usize> {
    state: [E::Fr; WIDTH],
    mode: SpongeMode<E, RATE>,
    domain_strategy: DomainStrategy,
}

impl<'a, E: Engine, const RATE: usize, const WIDTH: usize> GenericSponge<E, RATE, WIDTH> {
    pub fn new() -> Self {
        Self {
            state: [E::Fr::zero(); WIDTH],
            mode: SpongeMode::Absorb([None; RATE]),
            domain_strategy: DomainStrategy::CustomVariableLength,
        }
    }

    pub fn new_from_domain_strategy(domain_strategy: DomainStrategy) -> Self {
        match domain_strategy {
            DomainStrategy::CustomVariableLength | DomainStrategy::VariableLength => (),
            _ => panic!("only variable length domain strategies allowed"),
        }

        Self {
            state: [E::Fr::zero(); WIDTH],
            mode: SpongeMode::Absorb([None; RATE]),
            domain_strategy: domain_strategy,
        }
    }

    pub fn hash<P: HashParams<E, RATE, WIDTH>>(
        input: &[E::Fr],
        params: &P,
        domain_strategy: Option<DomainStrategy>,
    ) -> [E::Fr; RATE] {
        // init state
        let mut state = [E::Fr::zero(); WIDTH];

        let domain_strategy = domain_strategy.unwrap_or(DomainStrategy::CustomFixedLength);
        match domain_strategy {
            DomainStrategy::CustomFixedLength | DomainStrategy::FixedLength => (),
            _ => panic!("only fixed length domain strategies allowed"),
        }

        // specialize capacity
        let capacity_value = domain_strategy
            .compute_capacity::<E>(input.len(), RATE)
            .unwrap_or(E::Fr::zero());
        *state.last_mut().expect("last element") = capacity_value;

        // compute padding values
        let padding_values = domain_strategy.generate_padding_values::<E>(input.len(), RATE);

        // chain all values
        let mut padded_input = vec![];
        padded_input.extend_from_slice(input);
        padded_input.extend_from_slice(&padding_values);

        assert!(padded_input.len() % RATE == 0);

        // process each chunk of input
        for values in padded_input.chunks_exact(RATE) {
            absorb::<E, _, RATE, WIDTH>(
                &mut state,
                &values.try_into().expect("constant array"),
                params,
            );
        }
        // prepare output
        let mut output = [E::Fr::zero(); RATE];
        for (o, s) in output.iter_mut().zip(state[..RATE].iter()) {
            *o = *s;
        }

        output
    }

    pub fn absorb_multiple<P: HashParams<E, RATE, WIDTH>>(&mut self, input: &[E::Fr], params: &P) {
        // compute padding values        
        let padding_values = self.domain_strategy.generate_padding_values::<E>(input.len(), RATE);

        for inp in input.iter().chain(padding_values.iter()) {
            self.absorb(*inp, params)
        }
    }

    pub fn absorb<P: HashParams<E, RATE, WIDTH>>(&mut self, input: E::Fr, params: &P) {
        match self.mode {
            SpongeMode::Absorb(ref mut buf) => {
                // push value into buffer
                for el in buf.iter_mut() {
                    if el.is_none() {
                        // we still have empty room for values
                        *el = Some(input);
                        return;
                    }
                }

                // buffer is filled so unwrap them
                let mut unwrapped_buffer = [E::Fr::zero(); RATE];
                for (a, b) in unwrapped_buffer.iter_mut().zip(buf.iter_mut()) {
                    if let Some(val) = b {
                        *a = *val;
                        *b = None; // kind of resetting buffer
                    }
                }

                // here we can absorb values. run round function implicitly there
                absorb::<E, _, RATE, WIDTH>(&mut self.state, &mut unwrapped_buffer, params);

                // absorb value
                buf[0] = Some(input);
            }
            SpongeMode::Squeeze(_) => {
                // we don't need squeezed values so switching to absorbing mode is fine
                let mut buf = [None; RATE];
                buf[0] = Some(input);
                self.mode = SpongeMode::Absorb(buf)
            }
        }
    }

    pub fn pad_if_necessary(&mut self) {
        match self.mode {
            SpongeMode::Absorb(ref mut buf) => {
                let unwrapped_buffer_len = buf.iter().filter(|el| el.is_some()).count();
                // compute padding values                
                let padding_values =
                    self.domain_strategy.generate_padding_values::<E>(unwrapped_buffer_len, RATE);
                let mut padding_values_it = padding_values.iter().cloned();

                for b in buf {
                    if b.is_none() {
                        *b = padding_values_it.next()
                    }
                }
                assert!(padding_values_it.next().is_none());
            }
            SpongeMode::Squeeze(_) => (),
        }
    }

    pub fn squeeze<P: HashParams<E, RATE, WIDTH>>(&mut self, params: &P) -> Option<E::Fr> {
        loop {
            match self.mode {
                SpongeMode::Absorb(ref mut buf) => {
                    // buffer may not be filled fully so we may need padding.
                    let mut unwrapped_buffer = vec![];
                    for el in buf {
                        if let Some(value) = el {
                            unwrapped_buffer.push(*value);
                        }
                    }

                    if unwrapped_buffer.len() != RATE {
                        // processing buffer was done and we need padding
                        return None;
                    }

                    // make input array
                    let mut all_inputs = [E::Fr::zero(); RATE];
                    for (a, b) in all_inputs.iter_mut().zip(unwrapped_buffer) {
                        *a = b;
                    }

                    // permute state
                    absorb(&mut self.state, &all_inputs, params);

                    // push values into squeezing buffer for later squeezing
                    let mut squeeze_buffer = [None; RATE];
                    for (s, b) in self.state[..RATE].iter().zip(squeeze_buffer.iter_mut()) {
                        *b = Some(*s)
                    }

                    // we are switching squeezing mode so we can ignore to reset absorbing buffer
                    self.mode = SpongeMode::Squeeze(squeeze_buffer);
                }
                SpongeMode::Squeeze(ref mut buf) => {
                    for el in buf {
                        if let Some(value) = el.take() {
                            return Some(value);
                        }
                    }
                    return None;
                }
            };
        }
    }
}

fn absorb<E: Engine, P: HashParams<E, RATE, WIDTH>, const RATE: usize, const WIDTH: usize>(
    state: &mut [E::Fr; WIDTH],
    input: &[E::Fr; RATE],
    params: &P,
) {
    for (i, s) in input.iter().zip(state.iter_mut()) {
        s.add_assign(i);
    }
    generic_round_function(params, state);
}

pub fn generic_round_function<
    E: Engine,
    P: HashParams<E, RATE, WIDTH>,
    const RATE: usize,
    const WIDTH: usize,
>(
    params: &P,
    state: &mut [E::Fr; WIDTH],
) {
    match params.hash_family() {
        super::traits::HashFamily::Rescue => {
            rescue_round_function(params, state)
        }
        super::traits::HashFamily::Poseidon => {
            poseidon_round_function(params, state)
        }
        super::traits::HashFamily::RescuePrime => {
            rescue_prime_round_function(params, state)
        }
    }
}
