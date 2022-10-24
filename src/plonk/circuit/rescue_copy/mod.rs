pub mod circuit_rescue;
#[allow(dead_code)]
mod common;
pub mod sponge;
pub mod poseidon;
pub mod rescue;
pub mod rescue_prime;
#[cfg(test)]
mod tests;
pub mod traits;

use std::convert::TryInto;
// use crate::smallvec::SmallVec;
use serde::{ser::{SerializeTuple}, Serialize};

pub trait BigArraySerde<'de>: Sized {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where S: serde::Serializer;
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where D: serde::Deserializer<'de>;
}

// some wrappers that make array wrappers serializable themselves (resursively)

pub struct BigArrayRefWrapper<'de, B: BigArraySerde<'de>>(&'de B);

impl<'de, B: BigArraySerde<'de>> serde::Serialize for BigArrayRefWrapper<'de, B> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: serde::Serializer {
        self.0.serialize(serializer)
    }
}

pub struct BigArrayWrapper<'de, B: BigArraySerde<'de>>(B, std::marker::PhantomData<& 'de ()>);

impl<'de, B: BigArraySerde<'de>> serde::Serialize for BigArrayWrapper<'de, B> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: serde::Serializer {
        self.0.serialize(serializer)
    }
}

impl<'de, B: BigArraySerde<'de>> serde::Deserialize<'de> for BigArrayWrapper<'de, B> {
fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de> {
        let new = B::deserialize(deserializer)?;

        Ok(Self(new, std::marker::PhantomData))
    }
}

struct ArrayVisitor<T, const M: usize> {
    element: std::marker::PhantomData<T>,
}

impl<'de, T, const M: usize> serde::de::Visitor<'de> for ArrayVisitor<T, M>
    where T: serde::Deserialize<'de>
{
    type Value = [T; M];

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        formatter.write_str(&format!("an array of length {}", M))
    }

    fn visit_seq<A>(self, mut seq: A) -> Result<[T; M], A::Error>
        where A: serde::de::SeqAccess<'de>
    {
        let mut arr = Vec::with_capacity(M);
        for i in 0..M {
            let el = seq.next_element()?
                .ok_or_else(|| serde::de::Error::invalid_length(i, &self))?;
            arr.push(el);
        }
        use std::convert::TryInto;
        let arr: [T; M] = arr.try_into().map_err(|_| serde::de::Error::invalid_length(M, &self))?;

        Ok(arr)
    }
}

impl<'de, T, const N: usize> BigArraySerde<'de> for [T; N]
    where T: serde::Serialize + serde::Deserialize<'de>
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where S: serde::Serializer
    {
        let mut seq = serializer.serialize_tuple(N)?;
        for elem in &self[..] {
            seq.serialize_element(elem)?;
        }
        seq.end()
    }

    fn deserialize<D>(deserializer: D) -> Result<[T; N], D::Error>
        where D: serde::Deserializer<'de>
    {
        let visitor = ArrayVisitor::<_, N> { element: std::marker::PhantomData };
        deserializer.deserialize_tuple(N, visitor)
    }
}

// pub trait BigArrayOfArraysSerde<'de>: Sized {
//     fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
//         where S: serde::Serializer;
//     fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
//         where D: serde::Deserializer<'de>;
// }

// impl<'de, T, const N: usize, const M: usize> BigArrayOfArraysSerde<'de> for [[T; N]; M]
//     where T: serde::Serialize + serde::Deserialize<'de>
// {
//     fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
//         where S: serde::Serializer
//     {
//         use serde::ser::SerializeTuple;
//         let mut seq = serializer.serialize_tuple(N)?;
//         for elem in &self[..] {
//             seq.serialize_element(elem)?;
//         }
//         seq.end()
//     }

//     fn deserialize<D>(deserializer: D) -> Result<[[T; N]; M], D::Error>
//         where D: serde::Deserializer<'de>
//     {
//         struct ArrayVisitor<T, const M: usize> {
//             element: std::marker::PhantomData<T>,
//         }

//         impl<'de, T, const M: usize> serde::de::Visitor<'de> for ArrayVisitor<T, M>
//             where T: serde::Deserialize<'de>
//         {
//             type Value = [T; M];

//             fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
//                 formatter.write_str(&format!("an array of length {}", M))
//             }

//             fn visit_seq<A>(self, mut seq: A) -> Result<[T; M], A::Error>
//                 where A: serde::de::SeqAccess<'de>
//             {
//                 let mut arr = Vec::with_capacity(M);
//                 for i in 0..M {
//                     let el = seq.next_element()?
//                         .ok_or_else(|| serde::de::Error::invalid_length(i, &self))?;
//                     arr.push(el);
//                 }
//                 use std::convert::TryInto;
//                 let arr: [T; M] = arr.try_into().map_err(|_| serde::de::Error::invalid_length(M, &self))?;

//                 Ok(arr)
//             }
//         }

//         let visitor = ArrayVisitor::<_, N> { element: std::marker::PhantomData };
//         deserializer.deserialize_tuple(N, visitor)
//     }
// }

fn serialize_vec_of_arrays<T: serde::Serialize + serde::de::DeserializeOwned, const N: usize, S>(t: &Vec<[T; N]>, serializer: S) -> Result<S::Ok, S::Error> where S: serde::Serializer {
    let cast: Vec<_> = t.iter().map(|el| BigArrayRefWrapper(el)).collect();
    cast.serialize(serializer)
}

fn deserialize_vec_of_arrays<'de, D, T: serde::Serialize + serde::de::DeserializeOwned, const N: usize>(deserializer: D) -> Result<Vec<[T; N]>, D::Error> where D: serde::Deserializer<'de> {
    use serde::Deserialize;

    let result: Vec<BigArrayWrapper<'de, [T; N]>> = <Vec<BigArrayWrapper<'de, [T; N]>>>::deserialize(deserializer)?;
    let result: Vec<_> = result.into_iter().map(|el| el.0).collect();

    Ok(result)
}

fn serialize_vec_of_arrays_of_arrays<T: serde::Serialize + serde::de::DeserializeOwned, const N: usize, const M: usize, S>(t: &Vec<[[T; N]; M]>, serializer: S) -> Result<S::Ok, S::Error> where S: serde::Serializer {
    let mut flattened = Vec::with_capacity(t.len() * M);
    for row in t.iter() {
        for el in row.iter() {
            let w = BigArrayRefWrapper(el);
            flattened.push(w);
        }
    }

    flattened.serialize(serializer)
}

fn deserialize_vec_of_arrays_of_arrays<'de, D, T: serde::Serialize + serde::de::DeserializeOwned, const N: usize, const M: usize>(deserializer: D) -> Result<Vec<[[T; N]; M]>, D::Error> where D: serde::Deserializer<'de> {
    use serde::Deserialize;

    let flat_result: Vec<BigArrayWrapper<'de, [T; N]>> = <Vec<BigArrayWrapper<'de, [T; N]>>>::deserialize(deserializer)?;
    let mut flat_result: Vec<[T; N]> = flat_result.into_iter().map(|el| el.0).collect();
    assert!(flat_result.len() % M == 0);
    let num_elements = flat_result.len() / M;

    let mut result = Vec::with_capacity(flat_result.len() / M);
    for _ in 0..num_elements {
        let subarray: [[T; N]; M] = match flat_result.drain(..M).collect::<Vec<_>>().try_into() {
            Ok(a) => a,
            Err(..) => panic!("length must patch")
        };
        result.push(subarray);
    }

    Ok(result)
}

fn serialize_array_of_arrays<T: serde::Serialize + serde::de::DeserializeOwned, const N: usize, const M: usize, S>(t: &[[T; N]; M], serializer: S) -> Result<S::Ok, S::Error> where S: serde::Serializer {
    let mut seq = serializer.serialize_tuple(M)?;
    for el in t.iter() {
        let w = BigArrayRefWrapper(el);
        seq.serialize_element(&w)?;
    }

    seq.end()
}

fn deserialize_array_of_arrays<'de, D, T: serde::Serialize + serde::de::DeserializeOwned, const N: usize, const M: usize>(deserializer: D) -> Result<[[T; N]; M], D::Error> where D: serde::Deserializer<'de> {
    let visitor = ArrayVisitor::<BigArrayWrapper<'de, [T; N]>, M> { element: std::marker::PhantomData };
    let result = deserializer.deserialize_tuple(M, visitor)?;

    let subarray: [[T; N]; M] = match std::array::IntoIter::new(result).map(|el| el.0).collect::<Vec<_>>().try_into() {
        Ok(a) => a,
        Err(..) => panic!("length must patch")
    };

    Ok(subarray)
}

fn add_chain_pow_smallvec<F: bellman::pairing::ff::PrimeField>(
    base: F,
    add_chain: &[traits::Step],
    scratch_space: &mut smallvec::SmallVec<[F; 512]>,
) -> F {
    scratch_space.push(base);

    for (idx, el) in add_chain.iter().enumerate() {
        match el {
            traits::Step::Double { index } => {
                let mut el = scratch_space[*index];
                el.square();

                scratch_space.push(el);
            },
            traits::Step::Add { left, right } => {
                let mut el = scratch_space[*left];
                el.mul_assign(&scratch_space[*right]);

                scratch_space.push(el);
            }
        }
    }

    let result = scratch_space.pop().unwrap();

    scratch_space.clear();

    result
}