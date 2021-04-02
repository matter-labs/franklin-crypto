// extern crate test as self_test;
// use self::self_test::Bencher;
// use rand::{thread_rng, Rand};
// use super::alt_babyjubjub::AltJubjub;
// use super::{edwards::TwistedEdwardsCurve, super::fs::Fs};

// #[bench]
// fn bench_constant_time_mul(b: &mut Bencher){
//     let jubjub = AltJubjub::new();
//     let rng = &mut thread_rng();
    
//     let p = jubjub.rand(rng);
//     let scalar = Fs::rand(rng);

//     b.iter(|| {
//         jubjub.ct_mul(&p, scalar)
//     });
// }