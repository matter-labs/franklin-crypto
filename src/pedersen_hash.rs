use jubjub::*;
use bellman::pairing::ff::{Field, PrimeField, PrimeFieldRepr};

#[derive(Copy, Clone)]
pub enum Personalization {
    NoteCommitment,
    MerkleTree(usize)
}

impl Personalization {
    pub fn get_bits(&self) -> Vec<bool> {
        match *self {
            Personalization::NoteCommitment =>
                vec![true, true, true, true, true, true],
            Personalization::MerkleTree(num) => {
                assert!(num < 63);

                (0..6).map(|i| (num >> i) & 1 == 1).collect()
            }
        }
    }
}

pub fn pedersen_hash<E, I>(
    personalization: Personalization,
    bits: I,
    params: &E::Params
) -> edwards::Point<E, PrimeOrder>
    where I: IntoIterator<Item=bool>,
          E: JubjubEngine
{
    let mut bits = personalization.get_bits().into_iter().chain(bits.into_iter());

    let mut result = edwards::Point::zero();
    let mut generators = params.pedersen_hash_exp_table().iter();

    loop {
        let mut acc = E::Fs::zero();
        let mut cur = E::Fs::one();
        let mut chunks_remaining = params.pedersen_hash_chunks_per_generator();
        let mut encountered_bits = false;

        // Grab three bits from the input
        while let Some(a) = bits.next() {
            encountered_bits = true;

            let b = bits.next().unwrap_or(false);
            let c = bits.next().unwrap_or(false);

            // Start computing this portion of the scalar
            let mut tmp = cur;
            if a {
                tmp.add_assign(&cur);
            }
            cur.double(); // 2^1 * cur
            if b {
                tmp.add_assign(&cur);
            }

            // conditionally negate
            if c {
                tmp.negate();
            }

            acc.add_assign(&tmp);

            chunks_remaining -= 1;

            if chunks_remaining == 0 {
                break;
            } else {
                cur.double(); // 2^2 * cur
                cur.double(); // 2^3 * cur
                cur.double(); // 2^4 * cur
            }
        }

        if !encountered_bits {
            break;
        }

        let mut table: &[Vec<edwards::Point<E, _>>] = &generators.next().expect("we don't have enough generators");
        let window = params.pedersen_hash_exp_window_size();
        let window_mask = (1 << window) - 1;

        let mut acc = acc.into_repr();
        
        let mut tmp = edwards::Point::zero();

        while !acc.is_zero() {
            let i = (acc.as_ref()[0] & window_mask) as usize;

            tmp = tmp.add(&table[0][i], params);

            acc.shr(window);
            table = &table[1..];
        }

        result = result.add(&tmp, params);
    }

    result
}

use alt_babyjubjub::{AltJubjubBn256};

pub fn baby_pedersen_hash<E, I>(
    personalization: Personalization,
    bits: I,
    params: &E::Params
) -> edwards::Point<E, PrimeOrder>
    where I: IntoIterator<Item=bool>,
          E: JubjubEngine
{
    let mut bits = personalization.get_bits().into_iter().chain(bits.into_iter());

    let mut result = edwards::Point::zero();
    let mut generators = params.pedersen_hash_exp_table().iter();

    loop {
        let mut acc = E::Fs::zero();
        let mut cur = E::Fs::one();
        let mut chunks_remaining = params.pedersen_hash_chunks_per_generator();
        let mut encountered_bits = false;

        // Grab three bits from the input
        while let Some(a) = bits.next() {
            encountered_bits = true;

            let b = bits.next().unwrap_or(false);
            let c = bits.next().unwrap_or(false);

            // Start computing this portion of the scalar
            let mut tmp = cur;
            if a {
                tmp.add_assign(&cur);
            }
            cur.double(); // 2^1 * cur
            if b {
                tmp.add_assign(&cur);
            }

            // conditionally negate
            if c {
                tmp.negate();
            }

            acc.add_assign(&tmp);

            chunks_remaining -= 1;

            if chunks_remaining == 0 {
                break;
            } else {
                cur.double(); // 2^2 * cur
                cur.double(); // 2^3 * cur
                cur.double(); // 2^4 * cur
            }
        }

        if !encountered_bits {
            break;
        }

        let mut table: &[Vec<edwards::Point<E, _>>] = &generators.next().expect("we don't have enough generators");
        let window = params.pedersen_hash_exp_window_size();
        let window_mask = (1 << window) - 1;

        let mut acc = acc.into_repr();
        
        let mut tmp = edwards::Point::zero();

        while !acc.is_zero() {
            let i = (acc.as_ref()[0] & window_mask) as usize;

            tmp = tmp.add(&table[0][i], params);

            acc.shr(window);
            table = &table[1..];
        }

        result = result.add(&tmp, params);
    }

    result
}

#[test]
fn print_baby_pedersen_hash_test_values() {
    fn buffer2bits(buff: Vec<u8>) -> Vec<bool> {
        let mut res = vec![true; buff.len()*8];
        for i in 0..buff.len() {
            let b = buff[i];
            res[i*8] = b & 0x01 != 0;
            res[i*8+1] = b & 0x02 != 0;
            res[i*8+2] = b & 0x04 != 0;
            res[i*8+3] = b & 0x08 != 0;
            res[i*8+4] = b & 0x10 != 0;
            res[i*8+5] = b & 0x20 != 0;
            res[i*8+6] = b & 0x40 != 0;
            res[i*8+7] = b & 0x80 != 0;
        }
        res
    }

    use bellman::pairing::bn256::Bn256;

    let params = AltJubjubBn256::new();
    let bits = buffer2bits(vec![144u8; 115]);
    let point = baby_pedersen_hash::<Bn256, _>(Personalization::NoteCommitment, bits, &params);
    let (x,y) = point.into_xy();
    println!("input: vec![144u8; 115]");
    println!("{:?}, {:?}",x,y);
    println!();

    let point = baby_pedersen_hash::<Bn256, _>(Personalization::NoteCommitment, Vec::new().into_iter(), &params);
    let (x,y) = point.into_xy();
    println!("input: empty");
    println!("{:?}, {:?}",x,y);
    println!();

    let mut input: Vec<u8> = Vec::new();
    for i in 0..97u8 {
        input.push(i.wrapping_mul(11u8).wrapping_add(7u8))
    }
    println!("input: {:?}",input);
    let bits = buffer2bits(input);
    let point = baby_pedersen_hash::<Bn256, _>(Personalization::NoteCommitment, bits, &params);
    let (x,y) = point.into_xy();
    println!("{:?}, {:?}",x,y);
}