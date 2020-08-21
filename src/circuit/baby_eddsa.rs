use bellman::pairing::{
    Engine,
};

use bellman::pairing::ff::{Field, PrimeField};

use bellman::{
    SynthesisError,
    ConstraintSystem
};

use super::{
    Assignment,
    rescue,
    expression::Expression
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

use ::rescue::{
    RescueEngine
};

use super::super::util::{
    resize_grow_only
};

use super::ecc;

use super::lookup::{
    lookup3_xy
};

use super::boolean::{
    Boolean, 
    multi_and,
    field_into_boolean_vec_le,
    le_bits_into_le_bytes
};

use super::sha256::sha256;

use super::ecc::EdwardsPoint;

use super::blake2s::{blake2s};

use super::multipack;

#[derive(Clone)]
pub struct EddsaSignature<E: JubjubEngine> {
    pub r: EdwardsPoint<E>,
    pub s: AllocatedNum<E>,
    pub pk: EdwardsPoint<E>
}

use ::alt_babyjubjub::{fs::Fs};

use constants::{MATTER_EDDSA_BLAKE2S_PERSONALIZATION};

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

        Ok(())
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

        Ok(())
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

        Ok(())
    }
} 

impl<E: RescueEngine + JubjubEngine> EddsaSignature<E> {
    pub fn verify_rescue_musig<CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
        rescue_params: &<E as RescueEngine>::Params,
        jubjub_params: &<E as JubjubEngine>::Params,
        message: &[Boolean],
        generator: ecc::EdwardsPoint<E>,
    ) -> Result<(), SynthesisError> {
        // This constant is also used inside `franklin_crypto` verify rescue(enforce version of this check)
        const INPUT_PAD_LEN_FOR_RESCUE: usize = 256 * 3;
        const MAX_SIGN_MESSAGE_BIT_WIDTH: usize = 256;
        let fr_bit_width = E::Fr::NUM_BITS as usize;
        const FR_BIT_WIDTH_PADDED: usize = 256;

        let mut sig_data_bits = message.to_vec();
        resize_grow_only(
            &mut sig_data_bits,
            MAX_SIGN_MESSAGE_BIT_WIDTH,
            Boolean::constant(false),
        );
        //sig_data_bits = le_bits_into_le_bytes(sig_data_bits);
    
        let mut hash_input: Vec<Boolean> = vec![];
        {
            let mut pk_x_serialized = self
                .pk
                .get_x()
                .into_bits_le_strict(cs.namespace(|| "pk_x_bits into bits strict"))?;
    
            assert_eq!(pk_x_serialized.len(), fr_bit_width);

            resize_grow_only(
                &mut pk_x_serialized,
                FR_BIT_WIDTH_PADDED,
                Boolean::constant(false),
            );
            hash_input.extend(le_bits_into_le_bytes(pk_x_serialized));
        }
        {
            let mut r_x_serialized = self
                .r
                .get_x()
                .into_bits_le_strict(cs.namespace(|| "r_x_bits into bits strict"))?;
    
            assert_eq!(r_x_serialized.len(), fr_bit_width);
    
            resize_grow_only(
                &mut r_x_serialized,
                FR_BIT_WIDTH_PADDED,
                Boolean::constant(false),
            );
            hash_input.extend(le_bits_into_le_bytes(r_x_serialized));
        }
        hash_input.extend(sig_data_bits);
        resize_grow_only(
            &mut hash_input,
            INPUT_PAD_LEN_FOR_RESCUE,
            Boolean::constant(false),
        );
    
        let hash_input = multipack::pack_into_witness(
            cs.namespace(|| "pack FS parameter bits into field elements"),
            &hash_input,
        )?;
    
        assert_eq!(
            hash_input.len(),
            4,
            "multipacking of FS hash is expected to have length 4"
        );
    
        let mut sponge = rescue::StatefulRescueGadget::new(rescue_params);
        sponge.specialize(
            cs.namespace(|| "specialize rescue on input length"),
            hash_input.len() as u8,
        );
    
        sponge.absorb(
            cs.namespace(|| "apply rescue hash on FS parameters"),
            &hash_input,
            &rescue_params,
        )?;
    
        let s0 = sponge.squeeze_out_single(
            cs.namespace(|| "squeeze first word form sponge"),
            &rescue_params,
        )?;
    
        let s1 = sponge.squeeze_out_single(
            cs.namespace(|| "squeeze second word form sponge"),
            &rescue_params,
        )?;
    
        let s0_bits =
            s0.into_bits_le_strict(cs.namespace(|| "make bits of first word for FS challenge"))?;
        let s1_bits =
            s1.into_bits_le_strict(cs.namespace(|| "make bits of second word for FS challenge"))?;
    
        let take_bits = (<E as JubjubEngine>::Fs::CAPACITY / 2) as usize;
    
        let mut bits = Vec::with_capacity(<E as JubjubEngine>::Fs::CAPACITY as usize);
        bits.extend_from_slice(&s0_bits[0..take_bits]);
        bits.extend_from_slice(&s1_bits[0..take_bits]);
        assert!(bits.len() == E::Fs::CAPACITY as usize);
    
        let max_message_len = 32 as usize; //since it is the result of sha256 hash
    
        // we can use lowest bits of the challenge
        let is_sig_verified = self.verify_schnorr_relationship(
            cs.namespace(|| "verify schnorr relationship"),
            jubjub_params,
            &bits,
            generator
        )?;
        
        Boolean::enforce_equal(
          cs.namespace(|| "signature must be verified"), 
          &is_sig_verified, 
          &Boolean::Constant(true)
        )?;

        Ok(())
    }

    // The same as verify_rescue_musig, but it needs to have allocatedNum
    // as a message
    pub fn verify_field_rescue_musig<CS: ConstraintSystem<E>>(
      &self,
      mut cs: CS,
      rescue_params: &<E as RescueEngine>::Params,
      jubjub_params: &<E as JubjubEngine>::Params,
      message: &AllocatedNum<E>,
      generator: ecc::EdwardsPoint<E>,
  ) -> Result<(), SynthesisError> {
      let mut hash_input: Vec<AllocatedNum<E>> = vec![];
      
      let pk_x_serialized = self
          .pk
          .get_x();
      hash_input.push(pk_x_serialized.clone());
  
      let r_x_serialized = self
          .r
          .get_x();      
      hash_input.push(r_x_serialized.clone());
      
      hash_input.push(message.clone());
  
      assert_eq!(
          hash_input.len(),
          3,
          "FS hash is expected to have length 3"
      );
  
      let mut sponge = rescue::StatefulRescueGadget::new(rescue_params);
      sponge.specialize(
          cs.namespace(|| "specialize rescue on input length"),
          hash_input.len() as u8,
      );
  
      sponge.absorb(
          cs.namespace(|| "apply rescue hash on FS parameters"),
          &hash_input[..],
          &rescue_params,
      )?;
  
      let s0 = sponge.squeeze_out_single(
          cs.namespace(|| "squeeze first word form sponge"),
          &rescue_params,
      )?;
  
      let s1 = sponge.squeeze_out_single(
          cs.namespace(|| "squeeze second word form sponge"),
          &rescue_params,
      )?;
  
      let s0_bits =
          s0.into_bits_le_strict(cs.namespace(|| "make bits of first word for FS challenge"))?;
      let s1_bits =
          s1.into_bits_le_strict(cs.namespace(|| "make bits of second word for FS challenge"))?;
  
      let take_bits = (<E as JubjubEngine>::Fs::CAPACITY / 2) as usize;
  
      let mut bits = Vec::with_capacity(<E as JubjubEngine>::Fs::CAPACITY as usize);
      bits.extend_from_slice(&s0_bits[0..take_bits]);
      bits.extend_from_slice(&s1_bits[0..take_bits]);
      assert!(bits.len() == E::Fs::CAPACITY as usize);
  
      // we can use lowest bits of the challenge
      let is_sig_verified = self.verify_schnorr_relationship(
          cs.namespace(|| "verify schnorr relationship"),
          jubjub_params,
          &bits,
          generator
      )?;

      Boolean::enforce_equal(
        cs.namespace(|| "signature must be verified"), 
        &is_sig_verified, 
        &Boolean::Constant(true)
      )?;

      Ok(())
  }

    pub fn verify_schnorr_relationship<CS>(
        &self,
        mut cs: CS,
        params: &<E as JubjubEngine>::Params,
        fs_challenge: &[Boolean],
        generator: ecc::EdwardsPoint<E>
    ) -> Result<Boolean, SynthesisError>
    where
        CS: ConstraintSystem<E>
    {
        // message is always padded to 256 bits in this gadget, but still checked on synthesis
        assert!(fs_challenge.len() <= 256);
        
        let scalar_bits = self
            .s
            .into_bits_le_fixed(cs.namespace(|| "Get S bits"), E::Fs::NUM_BITS as usize)?;
    
        let sb = generator.mul(cs.namespace(|| "S*B computation"), &scalar_bits, params)?;
    
        // only order of R is checked. Public key and generator can be guaranteed to be in proper group!
        // by some other means for out particular case
        let r_is_not_small_order = self.r.is_not_small_order(
            cs.namespace(|| "R is in right order"),
            &params,
        )?;
    
        let challenge = fs_challenge;
    
        let pk_mul_hash = self
            .pk
            .mul(cs.namespace(|| "Calculate h*PK"), &challenge, params)?;
    
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
        Ok(multi_and(
            cs.namespace(|| "is signature correct"),
            &[r_is_not_small_order, is_x_correct, is_y_correct],
        )?)
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
    use super::super::super::rescue::bn256::Bn256RescueParams;
    
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
    fn test_valid_rescue_musig_signatures() {
        let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        let p_g = FixedGenerators::SpendingKeyGenerator;
        let params = &AltJubjubBn256::new();
        let rescue_params = &Bn256RescueParams::new_checked_2_into_1();
        let mut cs = TestConstraintSystem::<Bn256>::new();
        let sk = PrivateKey::<Bn256>(rng.gen());
        let vk = PublicKey::from_private(&sk, p_g, params);

        let mut msg1 = b"Foo bar pad to16".to_vec(); // 16 bytes

        let mut input: Vec<bool> = vec![];

        resize_grow_only(&mut msg1, 31, 0);

        for input_byte in msg1.iter() {
            for bit_i in (0..8).rev() {
                input.push((input_byte >> bit_i) & 1u8 == 1u8);
            }
        }

        let seed1 = Seed::random_seed(&mut rng, &msg1[..]);

        let sig1 = sk.musig_rescue_sign(&msg1[..], &seed1, p_g, rescue_params, params);
        assert!(vk.verify_musig_rescue(&msg1[..], &sig1, p_g, rescue_params, params));

        let input_bools: Vec<Boolean> = input.iter().enumerate().map(|(i, b)| {
            Boolean::from(
                AllocatedBit::alloc(cs.namespace(|| format!("input {}", i)), Some(*b)).unwrap()
            )
        }).collect();

        let input_nums = multipack::pack_into_witness(
            cs.namespace(|| "pack transaction bits into field elements for rescue"),
            &input_bools,
        ).unwrap();

        // Input must be only one element
        assert_eq!(input_nums.len(), 1);
        let mut sig_msg_bits = input_nums[0].into_bits_le(cs.namespace(|| "sig_msg_bits")).unwrap();
        resize_grow_only(&mut sig_msg_bits, 256, Boolean::constant(false));

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

        signature.verify_rescue_musig(
            cs.namespace(|| "verify signature"),
            &rescue_params, 
            &params, 
            &sig_msg_bits, 
            generator).expect("succesfully generated verifying gadget");

        assert!(cs.is_satisfied());
        print!("MuSig verification without message hashing takes constraints: {}\n", cs.num_constraints());
    }

    #[test]
    fn test_valid_field_rescue_musig_signatures() {
      let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
      let p_g = FixedGenerators::SpendingKeyGenerator;
      let params = &AltJubjubBn256::new();
      let rescue_params = &Bn256RescueParams::new_checked_2_into_1();
      let mut cs = TestConstraintSystem::<Bn256>::new();
      let sk = PrivateKey::<Bn256>(rng.gen());
      let vk = PublicKey::from_private(&sk, p_g, params);

      let mut msg1 = b"Foo bar pad to16".to_vec(); // 16 bytes

      let mut input: Vec<bool> = vec![];

      resize_grow_only(&mut msg1, 31, 0);

      for input_byte in msg1.iter() {
          for bit_i in (0..8).rev() {
              input.push((input_byte >> bit_i) & 1u8 == 1u8);
          }
      }

      let message_array = multipack::compute_multipacking::<Bn256>(&input);
      assert_eq!(message_array.len(), 1, "message is 1 E::Fr");
      let message = message_array[0];

      let seed1 = Seed::random_seed(&mut rng, &msg1[..]);

      let sig1 = sk.field_musig_rescue_sign(message, &seed1, p_g, rescue_params, params);
      assert!(vk.verify_field_musig_rescue(message, &sig1, p_g, rescue_params, params));

      let input_num = AllocatedNum::alloc(cs.namespace(|| "input for rescue"), || Ok(message)).unwrap();

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

      signature.verify_field_rescue_musig(
          cs.namespace(|| "verify signature"),
          &rescue_params, 
          &params, 
          &input_num, 
          generator).expect("succesfully generated verifying gadget");

      assert!(cs.is_satisfied());
      print!("MuSig verification without message hashing takes constraints: {}\n", cs.num_constraints());
  }
}


