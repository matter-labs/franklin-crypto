use super::edwards::*;
use bellman::{Engine, Field, PrimeField, PrimeFieldRepr};

pub fn scalar_to_radix_16<E: Engine, C: TwistedEdwardsCurveParams<E>>(scalar: &C::Fs) -> Vec<i8> {
    let repr = scalar.into_repr();

    scalar_words_to_radix_16::<E, C, _>(&repr)
}

pub fn scalar_words_to_radix_16<E: Engine, C: TwistedEdwardsCurveParams<E>, S: AsRef<[u64]>>(scalar_words: &S) -> Vec<i8> {
    let as_ref = scalar_words.as_ref();
    let mut buf = Vec::with_capacity(as_ref.len() * 8);

    use byteorder::{ByteOrder, LittleEndian, WriteBytesExt};

    for w in as_ref.iter() {
        buf.write_u64::<LittleEndian>(*w).expect("must write u64 into Vec");
    }

    debug_assert!(*buf.last().expect("is some byte") <= 127);

    let mut output = vec![0i8; buf.len() * 2];

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

    for i in 0..buf.len() {
        output[2 * i] = bot_half(buf[i]) as i8;
        output[2 * i + 1] = top_half(buf[i]) as i8;
    }

    // Precondition note: since self[last] <= 127, output[last] <= 7

    // Step 2: recenter coefficients from [0,16) to [-8,8)
    for i in 0..output.len() {
        let carry = (output[i] + 8) >> 4;
        output[i] -= carry << 4;
        output[i + 1] += carry;
    }
    // Precondition note: output[63] is not recentered.  It
    // increases by carry <= 1.  Thus output[63] <= 8.

    output
}
