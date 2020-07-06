use super::jubjub::{
    JubjubEngine, 
    Unknown, 
    edwards::Point
};

use subtle::{
    Choice, 
    ConditionallySelectable, 
    ConditionallyNegatable, 
    ConstantTimeEq
};

use bellman::{
    PrimeField, 
    PrimeFieldRepr, 
    Field
};

use std::time::{Duration, Instant};
use std::thread::sleep;

struct LookupTable<E: JubjubEngine, Subgroup>(Vec<Point<E, Subgroup>>);

impl<E: JubjubEngine, Subgroup> LookupTable<E, Subgroup>{

    fn from_point(p: Point<E, Subgroup>, params: &E::Params) -> Self{
        let mut buf = vec![p.clone(); 8];

        for i in 0..7{ 
            buf[i+1] = p.add(&buf[i], params);
        }

        Self(buf)
    }

    fn select(&self, x: i8) -> Point<E, Subgroup>{

        debug_assert!(x >= -8);
        debug_assert!(x <= 8);

        // Compute xabs = |x|
        let xmask = x >> 7;
        let xabs = (x + xmask) ^ xmask;

        // Set t = 0 * P = identity
        let mut t = Point::zero();

        for j in 1..9 {
            // Copy `points[j-1] == j*P` onto `t` in constant time if `|x| == j`.
            let c = (xabs as u8).ct_eq(&(j as u8));
            t.conditional_assign(&self.0[j - 1], c);
        }
        // Now t == |x| * P.

        let neg_mask = Choice::from((xmask & 1) as u8);
        t.conditional_negate(neg_mask);
        // Now t == x * P.

        t

    }

}

pub fn field_element_conditional_select<E: JubjubEngine>(a: &E::Fr, b: &E::Fr, choice: Choice) -> E::Fr{
    let a_repr  = a.into_raw_repr();
    let b_repr  = b.into_raw_repr();

    let  mut new_repr = <E::Fr as PrimeField>::Repr::default();

    new_repr.as_mut()[0] = u64::conditional_select(&a_repr.as_ref()[0], &b_repr.as_ref()[0], choice);
    new_repr.as_mut()[1] = u64::conditional_select(&a_repr.as_ref()[1], &b_repr.as_ref()[1], choice);
    new_repr.as_mut()[2] = u64::conditional_select(&a_repr.as_ref()[2], &b_repr.as_ref()[2], choice);
    new_repr.as_mut()[3] = u64::conditional_select(&a_repr.as_ref()[3], &b_repr.as_ref()[3], choice);

    E::Fr::from_raw_repr(new_repr).expect("should be valid repr")
}

pub fn field_element_conditional_assign<E: JubjubEngine>(a: &mut E::Fr, b: &E::Fr, choice: Choice){
    let mut a_repr  = a.into_raw_repr();
    let b_repr  = b.into_raw_repr();

    a_repr.as_mut()[0].conditional_assign(&b_repr.as_ref()[0], choice);    
    a_repr.as_mut()[1].conditional_assign(&b_repr.as_ref()[1], choice);    
    a_repr.as_mut()[2].conditional_assign(&b_repr.as_ref()[2], choice);    
    a_repr.as_mut()[3].conditional_assign(&b_repr.as_ref()[3], choice);    
    
    let c = E::Fr::from_raw_repr(a_repr).expect("should be valid repr");

    a.clone_from(&c)
}

pub fn field_element_conditional_swap<E: JubjubEngine>(a: &mut E::Fr, b: &mut E::Fr, choice: Choice){
    let mut a_repr  = a.into_raw_repr();
    let mut b_repr  = b.into_raw_repr();

    u64::conditional_swap(&mut a_repr.as_mut()[0], &mut b_repr.as_mut()[0], choice);
    u64::conditional_swap(&mut a_repr.as_mut()[1], &mut b_repr.as_mut()[1], choice);
    u64::conditional_swap(&mut a_repr.as_mut()[2], &mut b_repr.as_mut()[2], choice);
    u64::conditional_swap(&mut a_repr.as_mut()[3], &mut b_repr.as_mut()[3], choice);

    let new_a = E::Fr::from_raw_repr(a_repr).unwrap();
    let new_b = E::Fr::from_raw_repr(b_repr).unwrap();

    a.clone_from(&new_a);
    b.clone_from(&new_b);
}

fn scalar_to_radix_16<E: JubjubEngine>(scalar: &E::Fs) -> [i8; 64] {
    let mut buf = [0u8; 32];

    let repr = scalar.into_repr();
    repr.write_le(&mut buf[..]).unwrap();

    debug_assert!(buf[31] <= 127);

    let mut output = [0i8; 64];

    // Step 1: change radix.
    // Convert from radix 256 (bytes) to radix 16 (nibbles)
    #[inline(always)]
    fn bot_half(x: u8) -> u8 { (x >> 0) & 15 }
    #[inline(always)]
    fn top_half(x: u8) -> u8 { (x >> 4) & 15 }

    for i in 0..32 {
        output[2*i  ] = bot_half(buf[i]) as i8;
        output[2*i+1] = top_half(buf[i]) as i8;
    }

    // Precondition note: since self[31] <= 127, output[63] <= 7

    // Step 2: recenter coefficients from [0,16) to [-8,8)
    for i in 0..63 {
        let carry    = (output[i] + 8) >> 4;
        output[i  ] -= carry << 4;
        output[i+1] += carry;
    }
    // Precondition note: output[63] is not recentered.  It
    // increases by carry <= 1.  Thus output[63] <= 8.

    output
}


pub fn mul_scalar_ct<E: JubjubEngine, Subgroup>(
    scalars: Vec<E::Fs>, 
    points: Vec<Point<E, Subgroup>>, 
    params: &E::Params
) -> Point<E, Subgroup> {        
    let radix_scalars : Vec<_> = scalars
        .iter()
        .map(|s| scalar_to_radix_16::<E>(s))
        .collect();
        
    let tables: Vec<_> = points.iter().map(|p| LookupTable::from_point(*p, params)).collect();

    let mut acc = Point::<E, Subgroup>::zero();

    let mut four = E::Fs::one();
    four.double();
    four.double();
    four.double();
    four.double();

    for i in (0..64).rev(){
        acc = acc.mul(four, params);

        let it = radix_scalars.iter().zip(tables.iter());

        for (s, t) in it{
            let selected_value = t.select(s[i]);
            acc = acc.add(&selected_value, params);
        }
    }

    acc
}

#[test]
fn test_straus_lookup(){
    use super::jubjub::JubjubBls12;
    use super::bellman::bls12_381::{Bls12, Fr};
    use super::bellman::{PrimeField};

    use rand::{XorShiftRng, SeedableRng, Rand};

    let rng = &mut XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    let params = JubjubBls12::new();

    let p = Point::<Bls12, _>::rand(rng, &params);

    let inf = Point::<Bls12, _>::zero();

    let result = p.add(&inf, &params);

    assert!(p == result);


    let table = LookupTable::from_point(p.clone(), &params);

    for (i, q) in table.0.iter().enumerate(){
        let scalar = Fr::from_str(&format!("{}", i)).unwrap().into_repr();
        let tmp = p.mul((i+1) as u64, &params);
        assert!(tmp == *q, format!("failed at {}", i));
    }

}

#[test]
fn test_field_element_conditional_select(){
    use bellman::bls12_381::{Bls12, Fr};
    use super::jubjub::{JubjubBls12, JubjubEngine};

    let three = Fr::from_str(&format!("{}", 3)).unwrap();
    let five = Fr::from_str(&format!("{}", 5)).unwrap();

    let now = Instant::now();

    let result = field_element_conditional_select::<Bls12>(&three, &five, 0.into());

    println!("1 {}", now.elapsed().as_nanos());

    assert!(three == result);

    let result = field_element_conditional_select::<Bls12>(&three, &five, 1.into());
    println!("2 {}", now.elapsed().as_nanos());

    assert!(three != result);
}

#[test]
fn test_curve_point_conditional_select(){
    use super::jubjub::JubjubBls12;
    use super::bellman::bls12_381::{Bls12, Fr};
    use super::bellman::{PrimeField};

    use rand::{XorShiftRng, SeedableRng, Rand};

    let rng = &mut XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    let params = JubjubBls12::new();

    let p = Point::<Bls12, _>::rand(rng, &params);
    
    let q = Point::<Bls12, _>::rand(rng, &params);

    let result = Point::<Bls12, _>::conditional_select(&p, &q, 0.into());
    assert!(p == result);
    
    let result = Point::<Bls12, _>::conditional_select(&p, &q, 1.into());
    assert!(p != result);
}

#[test]
fn test_curve_point_conditional_swap(){
    use super::jubjub::JubjubBls12;
    use super::bellman::bls12_381::{Bls12, Fr};
    use super::bellman::{PrimeField};

    use rand::{XorShiftRng, SeedableRng, Rand};

    let rng = &mut XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    let params = JubjubBls12::new();

    let mut p = Point::<Bls12, _>::rand(rng, &params);
    
    let mut q = Point::<Bls12, _>::rand(rng, &params);

    assert!(p != q);

    Point::<Bls12, _>::conditional_swap(&mut p, &mut q, 0.into());
    assert!(p != q);
    
    Point::<Bls12, _>::conditional_swap(&mut p, &mut q, 1.into());
    assert!(p != q);
}

#[test]
fn test_curve_point_conditional_assign(){
    use super::jubjub::JubjubBls12;
    use super::bellman::bls12_381::{Bls12, Fr};
    use super::bellman::{PrimeField};

    use rand::{XorShiftRng, SeedableRng, Rand};

    let rng = &mut XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    let params = JubjubBls12::new();

    let mut p = Point::<Bls12, _>::rand(rng, &params);
    
    let q = Point::<Bls12, _>::rand(rng, &params);

    assert!(p != q);

    p.conditional_assign(&q, 0.into());
    assert!(p != q);
    
    p.conditional_assign(&q, 1.into());
    assert!(p == q);
}

#[test]
fn test_curve_point_conditional_negate(){
    use super::jubjub::JubjubBls12;
    use super::bellman::bls12_381::{Bls12, Fr};
    use super::bellman::{PrimeField};

    use rand::{XorShiftRng, SeedableRng, Rand};

    let rng = &mut XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    let params = JubjubBls12::new();

    let mut p = Point::<Bls12, _>::rand(rng, &params);
    let p_neg = p.negate();

    p.conditional_negate(0.into());
    assert!(p != p_neg);

    p.conditional_negate(1.into());
    assert!(p == p_neg);
}

#[test]
fn test_constant_time_mul_scalar(){
    use super::jubjub::{JubjubBls12, fs::Fs};
    use super::bellman::bls12_381::{Bls12, Fr};
    use super::bellman::{PrimeField};

    use rand::{XorShiftRng, SeedableRng, Rand};

    let rng = &mut XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    let params = JubjubBls12::new();

    let p = Point::<Bls12, _>::rand(rng, &params);

    let scalar = Fs::rand(rng);

    let now = Instant::now();

    let expected = p.mul(scalar, &params);

    println!("var time duration {}", now.elapsed().as_nanos());

    let result = mul_scalar_ct(vec![scalar], vec![p],&params);

    println!("const time duration {}", now.elapsed().as_nanos());

    let scalars : Vec<_>  = (0..10).map(|i| Fs::rand(rng)).collect();

    for (i, s) in scalars.iter().enumerate(){
        let last = Instant::now();
        mul_scalar_ct(vec![*s], vec![p], &params);
        println!("{} const time duration {}", i, last.elapsed().as_nanos());
    }

    let zero = Point::zero();

    assert!(expected != zero);

    assert!(expected == result);
}

#[test]
fn test_scalar_to_radix16(){
    use super::bellman::bls12_381::{Bls12, Fr, FrRepr};
    use super::bellman::{PrimeField};
    use super::jubjub::fs::{Fs, FsRepr};

    let repr = FsRepr::from(0xEEEEEEEEE as u64);

    let s = Fs::from_repr(repr).unwrap();

    let radix = scalar_to_radix_16::<Bls12>(&s);

    println!("s: {} r: {:?}", s, radix.as_ref());
}

