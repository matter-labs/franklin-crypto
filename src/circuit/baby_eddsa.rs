use bellman::pairing::{
    Engine,
};

use bellman::pairing::ff::{Field};

use bellman::{
    SynthesisError,
    ConstraintSystem
};

use super::{
    Assignment
};

use super::num::{
    AllocatedNum,
};

use ::jubjub::{
    edwards,
    JubjubEngine,
    JubjubParams,
    FixedGenerators
};

use super::lookup::{
    lookup3_xy
};

use super::boolean::{
    Boolean, 
    field_into_boolean_vec_le,
    le_bits_into_le_bytes
};

use super::sha256::sha256;

use super::ecc::EdwardsPoint;

use super::blake2s::{blake2s};

#[derive(Clone)]
pub struct EddsaSignature<E: JubjubEngine> {
    pub r: EdwardsPoint<E>,
    pub s: AllocatedNum<E>,
    pub pk: EdwardsPoint<E>
}

use ::alt_babyjubjub::{fs::Fs};

use constants::{MATTER_EDDSA_BLAKE2S_PERSONALIZATION};
use circuit::expression::Expression;
use circuit::pedersen_hash;

impl <E: JubjubEngine>EddsaSignature<E> {

    pub fn verify_schnorr_blake2s<CS>(
        &self,
        mut cs: CS,
        params: &E::Params,
        message: &[Boolean],
        generator: EdwardsPoint<E>
    ) -> Result<(), SynthesisError>
        where CS: ConstraintSystem<E>
    {
        // TODO check that s < Fs::Char
        let scalar_bits = field_into_boolean_vec_le(
            cs.namespace(|| "Get S bits"),
            self.s.get_value()
        )?;

        let sb = generator.mul(
            cs.namespace(|| "S*B computation"),
            &scalar_bits, params
        )?;

        // h = Hash(R_X || message)

        // only order of R is checked. Public key and generator can be guaranteed to be in proper group!
        // by some other means for out particular case
        self.r.assert_not_small_order(
            cs.namespace(|| "R is in right order"),
            &params
        )?;

        let mut hash_bits: Vec<Boolean> = vec![];

        let r_x_serialized = field_into_boolean_vec_le(
            cs.namespace(|| "Serialize R_X"), self.r.get_x().get_value()
        )?;

        hash_bits.extend(r_x_serialized.into_iter());
        hash_bits.resize(256, Boolean::Constant(false));

        hash_bits.extend(message.iter().cloned());
        hash_bits.resize(512, Boolean::Constant(false));

        assert_eq!(hash_bits.len(), 512);

        let h = blake2s(
            cs.namespace(|| "Calculate EdDSA hash"),
            &hash_bits, 
            MATTER_EDDSA_BLAKE2S_PERSONALIZATION
        )?;
        
        let pk_mul_hash = self.pk.mul(
            cs.namespace(|| "Calculate h*PK"), 
            &h, 
            params
        )?;

        let rhs = pk_mul_hash.add(
            cs.namespace(|| "Make signature RHS"), 
            &self.r, 
            params
        )?;

        let rhs_x = rhs.get_x();
        let rhs_y = rhs.get_y();

        let sb_x = sb.get_x();
        let sb_y = sb.get_y();

        let one = CS::one();
        cs.enforce(
            || "check x coordinate of signature",
            |lc| lc + rhs_x.get_variable(),
            |lc| lc + one,
            |lc| lc + sb_x.get_variable()
        );

        cs.enforce(
            || "check y coordinate of signature",
            |lc| lc + rhs_y.get_variable(),
            |lc| lc + one,
            |lc| lc + sb_y.get_variable()
        );

        return Ok(());
    }

    // message here is expected to be a digest, which is internally padded to 256 bits
    pub fn verify_sha256_musig<CS>(
        &self,
        mut cs: CS,
        params: &E::Params,
        message: &[Boolean],
        generator: EdwardsPoint<E>
    ) -> Result<(), SynthesisError>
        where CS: ConstraintSystem<E>
    {
        // TODO check that s < Fs::Char
        let scalar_bits = field_into_boolean_vec_le(
            cs.namespace(|| "Get S bits"),
            self.s.get_value()
        )?;

        let sb = generator.mul(
            cs.namespace(|| "S*B computation"),
            &scalar_bits, params
        )?;

        // h = Hash(PK_X || R_X || message)

        self.r.assert_not_small_order(
            cs.namespace(|| "R is in right order"),
            &params
        )?;

        // self.pk.assert_not_small_order(
        //     cs.namespace(|| "Check that public key is of correct order"),
        //     &params
        // )?;

        let mut hash_bits: Vec<Boolean> = vec![];

        let pk_x_serialized = field_into_boolean_vec_le(
            cs.namespace(|| "Serialize PK_X"), self.pk.get_x().get_value()
        )?;

        let r_x_serialized = field_into_boolean_vec_le(
            cs.namespace(|| "Serialize R_X"), self.r.get_x().get_value()
        )?;

        let mut t = vec![];
        t.extend(pk_x_serialized.into_iter());
        t.resize(256, Boolean::Constant(false));

        hash_bits.extend(le_bits_into_le_bytes(t).into_iter());

        let mut t = vec![];
        t.extend(r_x_serialized.into_iter());
        t.resize(256, Boolean::Constant(false));

        hash_bits.extend(le_bits_into_le_bytes(t).into_iter());

        hash_bits.extend(message.iter().cloned());
        hash_bits.resize(768, Boolean::Constant(false));

        assert_eq!(hash_bits.len(), 768);

        let h = sha256(
            cs.namespace(|| "Calculate sha256 of PK_X || R_X|| M"),
            &hash_bits
        )?;
        
        let pk_mul_hash = self.pk.mul(
            cs.namespace(|| "Calculate h*PK"), 
            &le_bits_into_le_bytes(h), 
            params
        )?;

        let rhs = pk_mul_hash.add(
            cs.namespace(|| "Make signature RHS"), 
            &self.r, 
            params
        )?;

        let rhs_x = rhs.get_x();
        let rhs_y = rhs.get_y();

        let sb_x = sb.get_x();
        let sb_y = sb.get_y();

        let one = CS::one();
        cs.enforce(
            || "check x coordinate of signature",
            |lc| lc + rhs_x.get_variable(),
            |lc| lc + one,
            |lc| lc + sb_x.get_variable()
        );

        cs.enforce(
            || "check y coordinate of signature",
            |lc| lc + rhs_y.get_variable(),
            |lc| lc + one,
            |lc| lc + sb_y.get_variable()
        );

        return Ok(());
    }

    pub fn verify_raw_message_signature<CS>(
        &self,
        mut cs: CS,
        params: &E::Params,
        message: &[Boolean],
        generator: EdwardsPoint<E>,
        max_message_len: usize
    ) -> Result<(), SynthesisError>
        where CS: ConstraintSystem<E>
    {
        // TODO check that s < Fs::Char

        // message is always padded to 256 bits in this gadget, but still checked on synthesis
        assert!(message.len() <= max_message_len * 8);

        // let scalar_bits = AllocatedNum::alloc(
        //     cs.namespace(|| "Allocate S witness"),
        //     || Ok(*self.s.get_value().get()?)
        // )?;

        let scalar_bits = self.s.into_bits_le(
            cs.namespace(|| "Get S bits")
        )?;

        // generator.assert_not_small_order(
        //     cs.namespace(|| "Temporary check that generator is of correct order"),
        //     &params
        // )?;

        // self.pk.assert_not_small_order(
        //     cs.namespace(|| "Temporary check that public key is of correct order"),
        //     &params
        // )?;

        let sb = generator.mul(
            cs.namespace(|| "S*B computation"),
            &scalar_bits, 
            params
        )?;

        // only order of R is checked. Public key and generator can be guaranteed to be in proper group!
        // by some other means for out particular case
        self.r.assert_not_small_order(
            cs.namespace(|| "R is in right order"),
            &params
        )?;

        let mut h: Vec<Boolean> = vec![];
        h.extend(message.iter().cloned());
        h.resize(256, Boolean::Constant(false));

        assert_eq!(h.len(), 256);
        
        let pk_mul_hash = self.pk.mul(
            cs.namespace(|| "Calculate h*PK"), 
            &h, 
            params
        )?;

        let rhs = pk_mul_hash.add(
            cs.namespace(|| "Make signature RHS"), 
            &self.r, 
            params
        )?;

        let rhs_x = rhs.get_x();
        let rhs_y = rhs.get_y();

        let sb_x = sb.get_x();
        let sb_y = sb.get_y();

        let one = CS::one();
        cs.enforce(
            || "check x coordinate of signature",
            |lc| lc + rhs_x.get_variable(),
            |lc| lc + one,
            |lc| lc + sb_x.get_variable()
        );

        cs.enforce(
            || "check y coordinate of signature",
            |lc| lc + rhs_y.get_variable(),
            |lc| lc + one,
            |lc| lc + sb_y.get_variable()
        );

        return Ok(());
    }

    pub fn is_verified_raw_message_signature<CS>(
        &self,
        mut cs: CS,
        params: &E::Params,
        message: &[Boolean],
        generator: EdwardsPoint<E>,
        max_message_len: usize,
    ) -> Result<Boolean, SynthesisError>
        where
            CS: ConstraintSystem<E>,
    {
        // message is always padded to 256 bits in this gadget, but still checked on synthesis
        assert!(message.len() <= max_message_len * 8);

        let scalar_bits = self.s.into_bits_le(cs.namespace(|| "Get S bits"))?;

        let sb = generator.mul(cs.namespace(|| "S*B computation"), &scalar_bits, params)?;

        // only order of R is checked. Public key and generator can be guaranteed to be in proper group!
        // by some other means for out particular case
        let r_is_not_small_order = Self::is_not_small_order(
            &self.r,
            cs.namespace(|| "R is in right order"),
            &params,
        )?;

        let mut h: Vec<Boolean> = vec![];
        h.extend(message.iter().cloned());
        h.resize(256, Boolean::Constant(false));

        assert_eq!(h.len(), 256);

        let pk_mul_hash = self
            .pk
            .mul(cs.namespace(|| "Calculate h*PK"), &h, params)?;

        let rhs = pk_mul_hash.add(cs.namespace(|| "Make signature RHS"), &self.r, params)?;

        let rhs_x = rhs.get_x();
        let rhs_y = rhs.get_y();

        let sb_x = sb.get_x();
        let sb_y = sb.get_y();

        let is_x_correct = Boolean::from(Expression::equals(
            cs.namespace(|| "is x coordinate correct"),
            Expression::from(rhs_x),
            Expression::from(sb_x),
        )?);
        let is_y_correct = Boolean::from(Expression::equals(
            cs.namespace(|| "is y coordinate correct"),
            Expression::from(rhs_y),
            Expression::from(sb_y),
        )?);

        let mut is_verified = Boolean::constant(true);
        is_verified = Boolean::and(
            cs.namespace(|| "is_verified and r_is_not_small_order"),
            &is_verified,
            &r_is_not_small_order,
        )?;
        is_verified = Boolean::and(
            cs.namespace(|| "is_verified and is_x_correct"),
            &is_verified,
            &is_x_correct,
        )?;
        is_verified = Boolean::and(
            cs.namespace(|| "is_verified and is_y_correct"),
            &is_verified,
            &is_y_correct,
        )?;
        Ok(is_verified)
    }

    pub fn verify_pedersen<CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
        sig_data_bits: &[Boolean],
        params: &E::Params,
        generator: EdwardsPoint<E>,
    ) -> Result<Boolean, SynthesisError> {
        let mut sig_data_bits = sig_data_bits.to_vec();
        sig_data_bits.resize(256, Boolean::constant(false));

        let mut first_round_bits: Vec<Boolean> = vec![];

        let mut pk_x_serialized = self
            .pk
            .get_x()
            .clone()
            .into_bits_le(cs.namespace(|| "pk_x_bits"))?;
        pk_x_serialized.resize(256, Boolean::constant(false));

        let mut r_x_serialized = self
            .r
            .get_x()
            .clone()
            .into_bits_le(cs.namespace(|| "r_x_bits"))?;
        r_x_serialized.resize(256, Boolean::constant(false));

        first_round_bits.extend(pk_x_serialized);
        first_round_bits.extend(r_x_serialized);

        let first_round_hash = pedersen_hash::pedersen_hash(
            cs.namespace(|| "first_round_hash"),
            pedersen_hash::Personalization::NoteCommitment,
            &first_round_bits,
            params,
        )?;
        let mut first_round_hash_bits = first_round_hash
            .get_x()
            .into_bits_le(cs.namespace(|| "first_round_hash_bits"))?;
        first_round_hash_bits.resize(256, Boolean::constant(false));

        let mut second_round_bits = vec![];
        second_round_bits.extend(first_round_hash_bits);
        second_round_bits.extend(sig_data_bits);
        let second_round_hash = pedersen_hash::pedersen_hash(
            cs.namespace(|| "second_hash"),
            pedersen_hash::Personalization::NoteCommitment,
            &second_round_bits,
            params,
        )?
            .get_x()
            .clone();

        let h_bits = second_round_hash.into_bits_le(cs.namespace(|| "h_bits"))?;

        let max_message_len = 32 as usize; //since it is the result of pedersen hash

        let is_sig_verified = self.is_verified_raw_message_signature(
            cs.namespace(|| "verify transaction signature"),
            params,
            &h_bits,
            generator,
            max_message_len,
        )?;
        Ok(is_sig_verified)
    }

    fn is_not_small_order<CS>(
        point: &EdwardsPoint<E>,
        mut cs: CS,
        params: &E::Params,
    ) -> Result<Boolean, SynthesisError>
        where
            CS: ConstraintSystem<E>,
    {
        let tmp = point.double(cs.namespace(|| "first doubling"), params)?;
        let tmp = tmp.double(cs.namespace(|| "second doubling"), params)?;
        let tmp = tmp.double(cs.namespace(|| "third doubling"), params)?;

        // (0, -1) is a small order point, but won't ever appear here
        // because cofactor is 2^3, and we performed three doublings.
        // (0, 1) is the neutral element, so checking if x is nonzero
        // is sufficient to prevent small order points here.
        let is_zero = Expression::equals(
            cs.namespace(|| "x==0"),
            Expression::from(tmp.get_x()),
            Expression::u64::<CS>(0),
        )?;

        Ok(Boolean::from(is_zero).not())
    }
}


#[cfg(test)]
mod test {
    use ::eddsa::{Seed, PrivateKey, PublicKey};
    use rand::{SeedableRng, Rng, XorShiftRng};
    use super::*;
    use ::circuit::test::*;
    use ::circuit::boolean::{Boolean, AllocatedBit};
    use bellman::pairing::bn256::{Bn256, Fr};
    use bellman::pairing::ff::{PrimeField, PrimeFieldRepr};
    use ::alt_babyjubjub::AltJubjubBn256;
    
    #[test]
    fn test_schnorr_signatures() {
        
        let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        let p_g = FixedGenerators::SpendingKeyGenerator;
        let params = &AltJubjubBn256::new();
        let mut cs = TestConstraintSystem::<Bn256>::new();
        let sk = PrivateKey::<Bn256>(rng.gen());
        let vk = PublicKey::from_private(&sk, p_g, params);

        let msg1 = b"Foo bar pad to16"; // 16 bytes

        let mut input: Vec<bool> = vec![];

        for b in msg1.iter() {  
            for i in (0..8).into_iter() {
                if (b & (1 << i)) != 0 {
                    input.extend(&[true; 1]);
                } else {
                    input.extend(&[false; 1]);
                }
            }
        }
        
        let seed1 = Seed::random_seed(&mut rng, msg1);

        let sig1 = sk.sign_schnorr_blake2s(msg1, &seed1, p_g, params);
        assert!(vk.verify_schnorr_blake2s(msg1, &sig1, p_g, params));

        let input_bools: Vec<Boolean> = input.iter().enumerate().map(|(i, b)| {
            Boolean::from(
                AllocatedBit::alloc(cs.namespace(|| format!("input {}", i)), Some(*b)).unwrap()
            )
        }).collect();

        let mut sigs_bytes = [0u8; 32];
        sig1.s.into_repr().write_le(& mut sigs_bytes[..]).expect("get LE bytes of signature S");
        let mut sigs_repr = <Fr as PrimeField>::Repr::from(0);
        sigs_repr.read_le(&sigs_bytes[..]).expect("interpret S as field element representation");

        let sigs_converted = Fr::from_repr(sigs_repr).unwrap();

        let s = AllocatedNum::alloc(cs.namespace(|| "allocate s"), || {
                Ok(sigs_converted)
            }
        ).unwrap();

        let public_generator = params.generator(FixedGenerators::SpendingKeyGenerator).clone();

        let generator = EdwardsPoint::witness(cs.namespace(|| "allocate public generator"), Some(public_generator), params).unwrap();

        let r = EdwardsPoint::witness(cs.namespace(|| "allocate r"), Some(sig1.r), params).unwrap();

        let pk = EdwardsPoint::witness(cs.namespace(|| "allocate pk"), Some(vk.0), params).unwrap();

        let signature = EddsaSignature{r, s, pk};
        signature.verify_schnorr_blake2s(cs.namespace(|| "verify signature"), params, &input_bools, generator).expect("succesfully generated verifying gadget");

        assert!(cs.is_satisfied());
        print!("Schnorr signature verification takes constraints: {}\n", cs.num_constraints());
    }

    #[test]
    fn test_valid_musig_signatures() {
        
        let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        let p_g = FixedGenerators::SpendingKeyGenerator;
        let params = &AltJubjubBn256::new();
        let mut cs = TestConstraintSystem::<Bn256>::new();
        let sk = PrivateKey::<Bn256>(rng.gen());
        let vk = PublicKey::from_private(&sk, p_g, params);

        let msg1 = b"Foo bar pad to16".to_vec(); // 16 bytes

        let mut input: Vec<bool> = vec![];

        for input_byte in msg1.iter() {
            for bit_i in (0..8).rev() {
                input.push((input_byte >> bit_i) & 1u8 == 1u8);
            }
        }

        let seed1 = Seed::random_seed(&mut rng, &msg1[..]);

        let sig1 = sk.musig_sha256_sign(&msg1[..], &seed1, p_g, params);
        assert!(vk.verify_musig_sha256(&msg1[..], &sig1, p_g, params));

        let input_bools: Vec<Boolean> = input.iter().enumerate().map(|(i, b)| {
            Boolean::from(
                AllocatedBit::alloc(cs.namespace(|| format!("input {}", i)), Some(*b)).unwrap()
            )
        }).collect();

        let mut sigs_bytes = [0u8; 32];
        sig1.s.into_repr().write_le(& mut sigs_bytes[..]).expect("get LE bytes of signature S");
        let mut sigs_repr = <Fr as PrimeField>::Repr::from(0);
        sigs_repr.read_le(&sigs_bytes[..]).expect("interpret S as field element representation");

        let sigs_converted = Fr::from_repr(sigs_repr).unwrap();

        let s = AllocatedNum::alloc(cs.namespace(|| "allocate s"), || {
                Ok(sigs_converted)
            }
        ).unwrap();

        let public_generator = params.generator(FixedGenerators::SpendingKeyGenerator).clone();

        let generator = EdwardsPoint::witness(cs.namespace(|| "allocate public generator"), Some(public_generator), params).unwrap();

        let r = EdwardsPoint::witness(cs.namespace(|| "allocate r"), Some(sig1.r), params).unwrap();

        let pk = EdwardsPoint::witness(cs.namespace(|| "allocate pk"), Some(vk.0), params).unwrap();

        let signature = EddsaSignature{r, s, pk};

        signature.verify_sha256_musig(
            cs.namespace(|| "verify signature"), 
            params, 
            &input_bools, 
            generator).expect("succesfully generated verifying gadget");

        assert!(cs.is_satisfied());
        print!("MuSig verification without message hashing takes constraints: {}\n", cs.num_constraints());
    }

    #[test]
    fn test_valid_raw_message_signatures() {
        let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        let p_g = FixedGenerators::SpendingKeyGenerator;
        let params = &AltJubjubBn256::new();
        let mut cs = TestConstraintSystem::<Bn256>::new();
        let sk = PrivateKey::<Bn256>(rng.gen());
        let vk = PublicKey::from_private(&sk, p_g, params);

        let msg1 = b"Foo bar pad to16"; // 16 bytes

        let mut input: Vec<bool> = vec![];

        for b in msg1.iter() {  
            for i in (0..8).into_iter() {
                if (b & (1 << i)) != 0 {
                    input.extend(&[true; 1]);
                } else {
                    input.extend(&[false; 1]);
                }
            }
        }

        // test for maximum message length of 16 bytes
        let seed1 = Seed::random_seed(&mut rng, msg1);

        let sig1 = sk.sign_raw_message(msg1, &seed1, p_g, params, 16);
        assert!(vk.verify_for_raw_message(msg1, &sig1, p_g, params, 16));

        let input_bools: Vec<Boolean> = input.iter().enumerate().map(|(i, b)| {
            Boolean::from(
                AllocatedBit::alloc(cs.namespace(|| format!("input {}", i)), Some(*b)).unwrap()
            )
        }).collect();

        let mut sigs_bytes = [0u8; 32];
        sig1.s.into_repr().write_le(& mut sigs_bytes[..]).expect("get LE bytes of signature S");
        let mut sigs_repr = <Fr as PrimeField>::Repr::from(0);
        sigs_repr.read_le(&sigs_bytes[..]).expect("interpret S as field element representation");

        let sigs_converted = Fr::from_repr(sigs_repr).unwrap();

        let s = AllocatedNum::alloc(cs.namespace(|| "allocate s"), || {
                Ok(sigs_converted)
            }
        ).unwrap();

        let public_generator = params.generator(FixedGenerators::SpendingKeyGenerator).clone();

        let generator = EdwardsPoint::witness(cs.namespace(|| "allocate public generator"), Some(public_generator), params).unwrap();

        let r = EdwardsPoint::witness(cs.namespace(|| "allocate r"), Some(sig1.r), params).unwrap();

        let pk = EdwardsPoint::witness(cs.namespace(|| "allocate pk"), Some(vk.0), params).unwrap();

        let signature = EddsaSignature{r, s, pk};
        signature.verify_raw_message_signature(cs.namespace(|| "verify signature"), params, &input_bools, generator, 16).expect("succesfully generated verifying gadget");

        assert!(cs.is_satisfied());
        print!("EdDSA variant raw message signature takes constraints: {}\n", cs.num_constraints());
    }

    #[test]
    fn test_valid_raw_message_signatures_evaluation() {
        let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        let p_g = FixedGenerators::SpendingKeyGenerator;
        let params = &AltJubjubBn256::new();
        let mut cs = TestConstraintSystem::<Bn256>::new();
        let sk = PrivateKey::<Bn256>(rng.gen());
        let vk = PublicKey::from_private(&sk, p_g, params);

        let msg1 = b"Foo bar pad to16"; // 16 bytes

        let mut input: Vec<bool> = vec![];

        for b in msg1.iter() {
            for i in (0..8).into_iter() {
                if (b & (1 << i)) != 0 {
                    input.extend(&[true; 1]);
                } else {
                    input.extend(&[false; 1]);
                }
            }
        }

        // test for maximum message length of 16 bytes
        let seed1 = Seed::random_seed(&mut rng, msg1);

        let sig1 = sk.sign_raw_message(msg1, &seed1, p_g, params, 16);
        assert!(vk.verify_for_raw_message(msg1, &sig1, p_g, params, 16));

        let input_bools: Vec<Boolean> = input
            .iter()
            .enumerate()
            .map(|(i, b)| {
                Boolean::from(
                    AllocatedBit::alloc(
                        cs.namespace(|| format!("input {}", i)),
                        Some(*b)
                    ).unwrap()
                )
            })
            .collect();

        let mut sigs_bytes = [0u8; 32];
        sig1.s.into_repr().write_le(& mut sigs_bytes[..]).expect("get LE bytes of signature S");
        let mut sigs_repr = <Fr as PrimeField>::Repr::from(0);
        sigs_repr.read_le(&sigs_bytes[..]).expect("interpret S as field element representation");

        let sigs_converted = Fr::from_repr(sigs_repr).unwrap();

        let s = AllocatedNum::alloc(
            cs.namespace(|| "allocate s"),
            || Ok(sigs_converted)
        ).unwrap();

        let public_generator = params.generator(FixedGenerators::SpendingKeyGenerator).clone();

        let generator = EdwardsPoint::witness(
            cs.namespace(|| "allocate public generator"),
            Some(public_generator),
            params
        ).unwrap();

        let r = EdwardsPoint::witness(cs.namespace(|| "allocate r"), Some(sig1.r), params).unwrap();

        let pk = EdwardsPoint::witness(cs.namespace(|| "allocate pk"), Some(vk.0), params).unwrap();

        let signature = EddsaSignature {r, s, pk};
        let success = signature
            .is_verified_raw_message_signature(
                cs.namespace(|| "verify signature"),
                params,
                &input_bools,
                generator,
                16
            )
            .expect("succesfully generated verifying gadget");

        assert!(cs.is_satisfied());
        print!("EdDSA variant raw message signature takes constraints: {}\n", cs.num_constraints());
        assert_eq!(success.get_value(), Some(true));
    }
}


