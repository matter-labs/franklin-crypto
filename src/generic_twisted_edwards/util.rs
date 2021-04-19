use super::edwards::*;
use bellman::{Engine, Field, PrimeField, PrimeFieldRepr};

pub fn scalar_to_radix_16<E: Engine, C: TwistedEdwardsCurveParams<E>>(scalar: &C::Fs) -> [i8; 64] {
    let mut buf = [0u8; 32];

    let repr = scalar.into_repr();
    repr.write_le(&mut buf[..]).unwrap();

    debug_assert!(buf[31] <= 127);

    let mut output = [0i8; 64];

    // Step 1: change radix.
    // Convert from radix 256 (bytes) to radix 16 (nibbles)
    #[inline(always)]
    fn bot_half(x: u8) -> u8 {
        (x >> 0) & 15
    }
    #[inline(always)]
    fn top_half(x: u8) -> u8 {
        (x >> 4) & 15
    }

    for i in 0..32 {
        output[2 * i] = bot_half(buf[i]) as i8;
        output[2 * i + 1] = top_half(buf[i]) as i8;
    }

    // Precondition note: since self[31] <= 127, output[63] <= 7

    // Step 2: recenter coefficients from [0,16) to [-8,8)
    for i in 0..63 {
        let carry = (output[i] + 8) >> 4;
        output[i] -= carry << 4;
        output[i + 1] += carry;
    }
    // Precondition note: output[63] is not recentered.  It
    // increases by carry <= 1.  Thus output[63] <= 8.

    output
}
