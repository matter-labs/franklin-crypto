use crate::bellman::pairing::ff::*;
use crate::bellman::pairing::ff::{PrimeField, PrimeFieldRepr};
use sha3::{digest::ExtendableOutput, digest::Update, digest::XofReader, Sha3XofReader, Shake128};

pub fn from_u64<F: PrimeField>(val: u64) -> F {
    F::from_repr(F::Repr::from(val)).unwrap()
}

fn from_limbs_with_error<F: PrimeField>(repr: &[u64]) -> Result<F, PrimeFieldDecodingError> {
    let mut tmp = F::Repr::default();
    tmp.as_mut().copy_from_slice(repr);
    F::from_repr(tmp)
}

pub fn field_element_from_shake<F: PrimeField>(reader: &mut Sha3XofReader) -> F {
    let bytes = f64::ceil(F::NUM_BITS as f64 / 8f64) as usize;
    let words = f64::ceil(bytes as f64 / 8f64) as usize;
    let mod_ = F::NUM_BITS % 8;
    let mask = if mod_ == 0 { 0xFF } else { (1u8 << mod_) - 1 };
    let mut buf = vec![0u8; bytes];
    let mut word_buf = vec![0u64; words];

    let len = buf.len();
    loop {
        reader.read(&mut buf);
        buf[len - 1] &= mask;
        for i in 0..words {
            let mut byte_array = [0u8; 8];
            for j in i * 8..std::cmp::min((i + 1) * 8, len) {
                byte_array[j - i * 8] = buf[j];
            }
            word_buf[i] = u64::from_le_bytes(byte_array);
        }
        let res = from_limbs_with_error::<F>(&word_buf);
        match res {
            Ok(el) => return el,
            _ => {}
        }
    }
}

#[inline(always)]
fn div_mod_word_by_short(hi: u64, lo: u64, y: u16) -> (u64, u64) {
    let t = ((hi as u128) << 64) + lo as u128;
    let q = (t / (y as u128)) as u64;
    let r = (t % (y as u128)) as u64;

    (q, r)
}

#[inline(always)]
pub fn divide_long_decomp<F: PrimeField>(
    a: &F::Repr,
    divisor: u16,
    offset: &mut usize,
) -> (F::Repr, u16) {
    let mut result = F::Repr::default();

    let a_ref = a.as_ref();
    let result_mut = result.as_mut();

    let len = a_ref.len();
    let mut start_index = len - *offset - 1;

    // optimize for decomposition
    if a_ref[start_index] == 0 {
        *offset += 1;
        start_index -= 1;
    }

    result_mut[start_index] = a_ref[start_index] / (divisor as u64);
    let mut r = a_ref[start_index] % (divisor as u64);

    result_mut
        .iter_mut()
        .zip(a_ref.iter())
        .rev()
        .skip(*offset + 1)
        .for_each(|(res, a_)| {
            let (q, m) = div_mod_word_by_short(r, *a_, divisor);
            *res = q;
            r = m;
        });

    (result, r as u16)
}

#[inline(always)]
pub fn divide_long<F: PrimeField>(a: &F::Repr, divisor: u16) -> (F::Repr, u16) {
    let mut result = F::Repr::default();

    let a_ref = a.as_ref();
    let result_mut = result.as_mut();

    let len = a_ref.len();

    result_mut[len - 1] = a_ref[len - 1] / (divisor as u64);
    let mut r = a.as_ref()[len - 1] % (divisor as u64);

    result_mut
        .iter_mut()
        .zip(a_ref.iter())
        .rev()
        .skip(1)
        .for_each(|(res, a_)| {
            let (q, m) = div_mod_word_by_short(r, *a_, divisor);
            *res = q;
            r = m;
        });

    (result, r as u16)
}

// -----------------------------------------------------------------------------
// Division with precomputation
//-----------------------------------------------------------------------------

pub const fn compute_normalized_divisor_and_reciproical(input: u16) -> (u64, u64) {
    let s = (input as u64).leading_zeros();
    let normalized_divisor = (input as u64) << s;
    let reciproical = u128::MAX / (normalized_divisor as u128) - (1u128 << 64);

    (normalized_divisor, reciproical as u64)
}

#[inline(always)]
const fn split(a: u128) -> (u64, u64) {
    ((a >> 64) as u64, a as u64)
}

#[inline(always)]
const fn div_mod_word_by_short_normalized(
    u1: u64,
    u0: u64,
    divisor: u64,
    recip: u64,
) -> (u64, u64) {
    let qq = (u1 as u128) * (recip as u128);
    let qq = qq + ((u1 as u128) << 64) + (u0 as u128);
    let (q1, q0) = split(qq);
    let mut q1 = q1.wrapping_add(1u64);
    let mut r = u0.wrapping_sub(q1.wrapping_mul(divisor));
    if r > q0 {
        q1 = q1.wrapping_sub(1u64);
        r = r.wrapping_add(divisor);
    }
    if r >= divisor {
        q1 = q1 + 1;
        r = r - divisor;
    }

    (q1, r)
}

#[inline(always)]
pub fn divide_long_using_recip<F: PrimeField>(
    a: &F::Repr,
    divisor: u64,
    recip: u64,
    norm_shift: u32,
) -> (F::Repr, u16) {
    let mut result = F::Repr::default();
    let (repr, mut limb) = full_shl::<F>(&a, norm_shift);

    result
        .as_mut()
        .iter_mut()
        .zip(repr.as_ref().iter())
        .rev()
        .for_each(|(r, rep)| {
            let (q, m) = div_mod_word_by_short_normalized(limb, *rep, divisor, recip);
            *r = q;
            limb = m;
        });

    (result, (limb >> norm_shift) as u16)
}

// -----------------------------------------------------------------------------

#[inline(always)]
pub fn add_single_word<F: PrimeField>(u: &F::Repr, w: u64) -> F::Repr {
    let mut res = F::Repr::default();

    let u_ref = u.as_ref();
    let res_mut = res.as_mut();

    let len = res_mut.len();

    let mut of = w;
    for index in 0..len - 1 {
        let (tmp, o) = u_ref[index].overflowing_add(of);
        res_mut[index] = tmp;
        of = o as u64;
    }

    res_mut[len - 1] = u_ref[len - 1].wrapping_add(of);
    res
}

// -----------------------------------------------------------------------------

#[inline(always)]
pub fn mul_by_single_word<F: PrimeField>(u: &F::Repr, w: u64) -> F::Repr {
    let mut res = F::Repr::default();

    let u_ref = u.as_ref();
    let res_mut = res.as_mut();

    let w_ = w as u128;

    let mut tmp = (u_ref[0] as u128) * w_;
    res_mut[0] = tmp as u64;
    res_mut
        .iter_mut()
        .zip(u_ref.iter())
        .skip(1)
        .for_each(|(r, u_)| {
            tmp = (*u_ as u128) * w_ + (tmp >> 64);
            *r = tmp as u64;
        });
    res
}

// -----------------------------------------------------------------------------

#[inline(always)]
pub fn full_shr<F: PrimeField>(u: &F::Repr, shift: u32) -> F::Repr {
    assert!(shift <= 64u32);
    let mut res = F::Repr::default();

    let u_ref = u.as_ref();
    let res_mut = res.as_mut();

    let len = res_mut.len();

    res_mut
        .iter_mut()
        .zip(u_ref.iter())
        .for_each(|(r, u_)| *r = *u_ >> shift);

    for index in 0..len - 1 {
        res_mut[index] |= u_ref[index + 1] << (64u32 - shift);
    }
    res
}

#[inline(always)]
pub fn full_shl<F: PrimeField>(u: &F::Repr, shift: u32) -> (F::Repr, u64) {
    assert!(shift <= 64u32);
    let mut res = F::Repr::default();

    let u_ref = u.as_ref();
    let res_mut = res.as_mut();

    let len = res_mut.len();

    for index in 0..len - 1 {
        res_mut[index + 1] = u_ref[index] >> (64u32 - shift);
    }

    res_mut.iter_mut().zip(u_ref.iter()).for_each(|(r, u_)| {
        *r |= *u_ << shift;
    });

    // adds a limb
    (res, u_ref[len - 1] >> (64u32 - shift))
}

#[inline(always)]
pub fn partial_shl<F: PrimeField>(u: &F::Repr, shift: u32) -> F::Repr {
    assert!(shift <= 64u32);
    let mut res = F::Repr::default();

    let u_ref = u.as_ref();
    let res_mut = res.as_mut();

    let len = res_mut.len();

    for index in 0..len - 1 {
        res_mut[index + 1] = u_ref[index] >> (64u32 - shift);
    }

    res_mut
        .iter_mut()
        .zip(u_ref.iter())
        .for_each(|(r, u_)| *r |= *u_ << shift);
    res
}
