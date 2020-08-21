use jubjub::{
    JubjubEngine,
    PrimeOrder,
    edwards
};

use bellman::pairing::ff::{
    PrimeField
};

use tiny_keccak::Keccak;
use blake2_rfc::blake2s::Blake2s;
use constants;

pub trait GroupHasher {
    fn new(personalization: &[u8]) -> Self;
    fn update(&mut self, data: &[u8]);
    fn finalize(&mut self) -> Vec<u8>;
}

pub struct BlakeHasher {
    h: Blake2s
}

impl GroupHasher for BlakeHasher {
    fn new(personalization: &[u8]) -> Self {
        let h = Blake2s::with_params(32, &[], &[], personalization);

        Self {
            h
        }
    }

    fn update(&mut self, data: &[u8]) {
        self.h.update(data);
    }

    fn finalize(&mut self) -> Vec<u8> {
        use std::mem;

        let new_h = Blake2s::with_params(32, &[], &[], &[]);
        let h = std::mem::replace(&mut self.h, new_h);

        let result = h.finalize();

        result.as_ref().to_vec()
    }
}

pub struct Keccak256Hasher {
    h: Keccak
}

impl GroupHasher for Keccak256Hasher {
    fn new(personalization: &[u8]) -> Self {
        let mut h = Keccak::new_keccak256();
        h.update(personalization);

        Self {
            h
        }
    }

    fn update(&mut self, data: &[u8]) {
        self.h.update(data);
    }

    fn finalize(&mut self) -> Vec<u8> {
        use std::mem;

        let new_h = Keccak::new_keccak256();
        let h = std::mem::replace(&mut self.h, new_h);

        let mut res: [u8; 32] = [0; 32];
        h.finalize(&mut res);

        res[..].to_vec()
    }
}

/// Produces a random point in the Jubjub curve.
/// The point is guaranteed to be prime order
/// and not the identity.
pub fn group_hash<E: JubjubEngine>(
    tag: &[u8],
    personalization: &[u8],
    params: &E::Params
) -> Option<edwards::Point<E, PrimeOrder>>
{
    assert_eq!(personalization.len(), 8);

    // Check to see that scalar field is 255 bits
    assert!(E::Fr::NUM_BITS == 255);

    let mut h = Blake2s::with_params(32, &[], &[], personalization);
    h.update(constants::GH_FIRST_BLOCK);
    h.update(tag);
    let h = h.finalize().as_ref().to_vec();
    assert!(h.len() == 32);

    match edwards::Point::<E, _>::read(&h[..], params) {
        Ok(p) => {
            let p = p.mul_by_cofactor(params);

            if p != edwards::Point::zero() {
                Some(p)
            } else {
                None
            }
        },
        Err(_) => None
    }
}

/// Produces a random point in the Alt Baby Jubjub curve.
/// The point is guaranteed to be prime order
/// and not the identity.
pub fn baby_group_hash<E: JubjubEngine>(
    tag: &[u8],
    personalization: &[u8],
    params: &E::Params
) -> Option<edwards::Point<E, PrimeOrder>>
{
    assert_eq!(personalization.len(), 8);

    // Check to see that scalar field is 255 bits
    assert!(E::Fr::NUM_BITS == 254);

    let mut h = Blake2s::with_params(32, &[], &[], personalization);
    h.update(constants::GH_FIRST_BLOCK);
    h.update(tag);
    let h = h.finalize().as_ref().to_vec();
    assert!(h.len() == 32);

    match edwards::Point::<E, _>::read(&h[..], params) {
        Ok(p) => {
            let p = p.mul_by_cofactor(params);

            if p != edwards::Point::zero() {
                Some(p)
            } else {
                None
            }
        },
        Err(_) => None
    }
}

/// Produces a random point in the Jubjub curve.
/// The point is guaranteed to be prime order
/// and not the identity.
pub fn generic_group_hash<E: JubjubEngine, H: GroupHasher>(
    tag: &[u8],
    personalization: &[u8],
    params: &E::Params
) -> Option<edwards::Point<E, PrimeOrder>>
{
    assert_eq!(personalization.len(), 8);

    // Due to small number of iterations Fr should be close to 255 bits
    assert!(E::Fr::NUM_BITS == 255 || E::Fr::NUM_BITS == 254);

    let mut h = H::new(personalization);
    h.update(constants::GH_FIRST_BLOCK);
    h.update(tag);
    let h = h.finalize();
    assert!(h.len() == 32);

    match edwards::Point::<E, _>::read(&h[..], params) {
        Ok(p) => {
            let p = p.mul_by_cofactor(params);

            if p != edwards::Point::zero() {
                Some(p)
            } else {
                None
            }
        },
        Err(_) => None
    }
}

#[test]
fn test_generic_hash() {
    use bellman::pairing::bn256::Bn256;
    use alt_babyjubjub::JubjubEngine;
    use alt_babyjubjub::AltJubjubBn256;

    let personalization = b"Hello123";
    let params = AltJubjubBn256::new();
    for t in 0u8..=255u8 {
        let tag = [t];
        let blake_point = baby_group_hash::<Bn256>(&tag, &personalization[..], &params);
        let generic_point = generic_group_hash::<Bn256, BlakeHasher>(&tag, &personalization[..], &params);
        assert!(blake_point == generic_point);
    }
}

#[test]
fn test_export_blake_generators() {
    use bellman::pairing::bn256::Bn256;
    use alt_babyjubjub::JubjubEngine;
    use alt_babyjubjub::AltJubjubBn256;

    let personalization = b"Hello123";
    let params = AltJubjubBn256::new();
    for t in 0u8..=255u8 {
        let tag = [t];
        let blake_point = baby_group_hash::<Bn256>(&tag, &personalization[..], &params);
        let generic_point = generic_group_hash::<Bn256, BlakeHasher>(&tag, &personalization[..], &params);
        assert!(blake_point == generic_point);
    }
}

#[test]
fn blake2s_consistency_test() {
    let personalization = b"Hello_w!";
    let tag = b"World_123!";
    let mut h = Blake2s::with_params(32, &[], &[], personalization);
    h.update(constants::GH_FIRST_BLOCK);
    h.update(tag);
    let h = h.finalize().as_ref().to_vec();
    let reference = hex!("989e1d96f8d977db95b7fcb59d26fe7f66b4e21e84cdb9387b67aa78ebd07ecf");

    assert_eq!(reference[..], h[..]);
}