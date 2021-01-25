use crate::bellman::pairing::ff::*;
use crate::bellman::SynthesisError;

pub fn u16_to_fe<F: PrimeField>(value: u16) -> F {
    u64_to_fe(value as u64)
}

pub fn u32_to_fe<F: PrimeField>(value: u32) -> F {
    u64_to_fe(value as u64)
}

pub fn u64_to_fe<F: PrimeField>(value: u64) -> F {
    let mut repr = F::Repr::default();
    repr.as_mut()[0] = value;

    F::from_repr(repr).unwrap()
}

pub fn u128_to_fe<F: PrimeField>(value: u128) -> F {
    let mut repr = F::Repr::default();
    repr.as_mut()[0] = value as u64;
    repr.as_mut()[1] = (value >> 64) as u64;

    F::from_repr(repr).unwrap()
}

pub fn u64_to_le_bits(value: u64, limit: Option<usize>) -> Vec<bool> {
    let limit = if let Some(limit) = limit {
        limit
    } else {
        64
    };

    let mut bits: Vec<bool> = BitIterator::new(&[value]).collect();
    bits.reverse();
    bits.truncate(limit);

    bits
}

pub fn fe_to_le_bits<F: PrimeField>(value: F, limit: Option<usize>) -> Vec<bool> {
    let limit = if let Some(limit) = limit {
        limit
    } else {
        F::NUM_BITS as usize
    };

    let mut bits: Vec<bool> = BitIterator::new(&value.into_repr()).collect();
    bits.reverse();
    bits.truncate(limit);

    bits
}
#[derive(Clone, Copy)]
struct ZeroPaddingBuffer<'a>(&'a [u8]);

impl<'a> std::io::Read for ZeroPaddingBuffer<'a> {
    fn read(&mut self, _buf: &mut [u8]) -> std::io::Result<usize> { unimplemented!() }
    fn read_vectored(&mut self, _bufs: &mut [std::io::IoSliceMut<'_>]) -> std::io::Result<usize> { unimplemented!( )}
    fn read_to_end(&mut self, _buf: &mut Vec<u8>) -> std::io::Result<usize> { unimplemented!() }
    fn read_to_string(&mut self, _buf: &mut String) -> std::io::Result<usize> { unimplemented!() }
    fn read_exact(&mut self, buf: &mut [u8]) -> std::io::Result<()> {
        let bytes_available = self.0.len();
        let len = buf.len();
        if bytes_available >= len {
            let (to_read, leftover) = self.0.split_at(len);
            buf.copy_from_slice(&*to_read);

            self.0 = leftover;
        } else {
            buf[..bytes_available].copy_from_slice(&self.0);
            for b in buf[bytes_available..].iter_mut() {
                *b = 0u8;
            }
            self.0 = &[];
        }
        Ok(())
    }
    fn by_ref(&mut self) -> &mut Self where Self: Sized, { self }
    fn bytes(self) -> std::io::Bytes<Self> where Self: Sized { unimplemented!() }
    fn chain<R: std::io::Read>(self, _next: R) -> std::io::Chain<Self, R> where Self: Sized { unimplemented!() }
    fn take(self, _limit: u64) -> std::io::Take<Self> where Self: Sized { unimplemented!() }
}

#[derive(Clone, Copy)]
struct ZeroPrePaddingBuffer<'a>(&'a [u8], usize);

impl<'a> std::io::Read for ZeroPrePaddingBuffer<'a> {
    fn read(&mut self, _buf: &mut [u8]) -> std::io::Result<usize> { unimplemented!() }
    fn read_vectored(&mut self, _bufs: &mut [std::io::IoSliceMut<'_>]) -> std::io::Result<usize> { unimplemented!( )}
    fn read_to_end(&mut self, _buf: &mut Vec<u8>) -> std::io::Result<usize> { unimplemented!() }
    fn read_to_string(&mut self, _buf: &mut String) -> std::io::Result<usize> { unimplemented!() }
    fn read_exact(&mut self, buf: &mut [u8]) -> std::io::Result<()> {
        let bytes_available = self.0.len();
        let padding_available = self.1;
        let len = buf.len();
        if padding_available >= len {
            self.1 -= len;
            for b in buf.iter_mut() {
                *b = 0u8;
            }
        } else {
            let (dst_to_zero, dst_to_read_to) = buf.split_at_mut(self.1);
            self.1 = 0;
            for b in dst_to_zero.iter_mut() {
                *b = 0u8;
            }
            let len = dst_to_read_to.len();
            if len >= bytes_available {
                let (to_read, leftover) = self.0.split_at(len);
                dst_to_read_to.copy_from_slice(&*to_read);
                self.0 = leftover;
            } else {
                let midpoint = len - bytes_available;
                dst_to_read_to[midpoint..].copy_from_slice(&self.0);
                for b in dst_to_read_to[..midpoint].iter_mut() {
                    *b = 0u8;
                }
                self.0 = &[];
            }
        }
        
        Ok(())
    }
    fn by_ref(&mut self) -> &mut Self where Self: Sized, { self }
    fn bytes(self) -> std::io::Bytes<Self> where Self: Sized { unimplemented!() }
    fn chain<R: std::io::Read>(self, _next: R) -> std::io::Chain<Self, R> where Self: Sized { unimplemented!() }
    fn take(self, _limit: u64) -> std::io::Take<Self> where Self: Sized { unimplemented!() }
}

#[track_caller]
pub fn pack_be_bytes_to_fe<F: PrimeField>(bytes: &[u8]) -> Result<F, SynthesisError>{
    let mut repr = F::zero().into_repr();
    let expected_len = repr.as_ref().len() * 8;
    assert!(bytes.len() <= expected_len);
    let padding = expected_len - bytes.len();
    let buff = ZeroPrePaddingBuffer(&bytes, padding);
    repr.read_be(buff).map_err(|_| SynthesisError::Unsatisfiable)?;
    let el = F::from_repr(repr).map_err(|_| SynthesisError::Unsatisfiable)?;

    Ok(el)
}

#[track_caller]
pub fn pack_le_bytes_to_fe<F: PrimeField>(bytes: &[u8]) -> Result<F, SynthesisError> {
    let buff = ZeroPaddingBuffer(&bytes);
    let mut repr = F::zero().into_repr();
    repr.read_le(buff).map_err(|_| SynthesisError::Unsatisfiable)?;
    let el = F::from_repr(repr).map_err(|_| SynthesisError::Unsatisfiable)?;

    Ok(el)
}

#[track_caller]
pub fn fe_to_be_bytes<F: PrimeField>(el: &F) -> Result<Vec<u8>, SynthesisError> {
    let mut buffer = vec![];
    let repr = el.into_repr();
    repr.write_be(&mut buffer).map_err(|_| SynthesisError::Unsatisfiable)?;

    Ok(buffer)
}

#[track_caller]
pub fn fe_to_le_bytes<F: PrimeField>(el: &F) -> Result<Vec<u8>, SynthesisError> {
    let mut buffer = vec![];
    let repr = el.into_repr();
    repr.write_le(&mut buffer).map_err(|_| SynthesisError::Unsatisfiable)?;

    Ok(buffer)
}