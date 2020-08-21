//! This is an implementation of EdDSA as refered in literature
//! Generation of randomness is not specified

use sha2::{Sha256, Digest};
use bellman::pairing::ff::{Field, PrimeField, PrimeFieldRepr, BitIterator};
use rand::{Rng};
use std::io::{self, Read, Write};
use std::convert::{TryInto, TryFrom};
use crate::pedersen_hash::*;
use jubjub::{
    FixedGenerators,
    JubjubEngine,
    JubjubParams,
    Unknown,
    edwards::Point,
    ToUniform};
use hmac::{Hmac, Mac};
use crate::rescue::{RescueEngine};

use util::{hash_to_scalar, hash_to_scalar_s, sha256_hash_to_scalar, rescue_hash_to_scalar, field_rescue_hash_to_scalar};

use ::constants::{MATTER_EDDSA_BLAKE2S_PERSONALIZATION};

type HmacSha256 = Hmac<Sha256>;

fn read_scalar<E: JubjubEngine, R: Read>(reader: R) -> io::Result<E::Fs> {
    let mut s_repr = <E::Fs as PrimeField>::Repr::default();
    s_repr.read_le(reader)?;

    match E::Fs::from_repr(s_repr) {
        Ok(s) => Ok(s),
        Err(_) => Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "scalar is not in field",
        )),
    }
}

fn write_scalar<E: JubjubEngine, W: Write>(s: &E::Fs, writer: W) -> io::Result<()> {
    s.into_repr().write_le(writer)
}

fn h_star<E: JubjubEngine>(a: &[u8], b: &[u8]) -> E::Fs {
    hash_to_scalar::<E>(b"Zcash_RedJubjubH", a, b)
}

fn h_star_s<E: JubjubEngine>(a: &[u8], b: &[u8]) -> E::Fs {
    hash_to_scalar_s::<E>(MATTER_EDDSA_BLAKE2S_PERSONALIZATION, a, b)
}

fn sha256_h_star<E: JubjubEngine>(a: &[u8], b: &[u8]) -> E::Fs {
    sha256_hash_to_scalar::<E>(&[], a, b)
}

fn pedersen_h_star<E: JubjubEngine>(bits: &[bool], params: &E::Params) -> E::Fs{
    let result: E::Fr = baby_pedersen_hash::<E,_>(Personalization::NoteCommitment, bits.to_vec().into_iter(), params).into_xy().0;
    let mut result_le_bits: Vec<bool> = BitIterator::new(result.into_repr()).collect();
    result_le_bits.reverse();
    let mut fe = E::Fs::zero();
    let mut base = E::Fs::one();

    for bit in result_le_bits {
        if bit {
            fe.add_assign(&base);
        }
        base.double();
    }

    fe
}

fn field_rescue_h_star<E: RescueEngine + JubjubEngine>(
    a: E::Fr,
    b: E::Fr,
    c: E::Fr,
    params: &<E as RescueEngine>::Params
) -> E::Fs {
    field_rescue_hash_to_scalar::<E>(
        None,
        &[a, b, c][..],
        params
    )
}

fn rescue_h_star<E: RescueEngine + JubjubEngine>(
    a: &[u8],
    b: &[u8],
    params: &<E as RescueEngine>::Params
) -> E::Fs {
    rescue_hash_to_scalar::<E>(
        &[],
        a,
        b,
        params
    )
}

#[derive(Copy, Clone)]
pub struct SerializedSignature {
    rbar: [u8; 32],
    sbar: [u8; 32],
}

#[derive(Clone)]
pub struct Signature<E: JubjubEngine> {
    pub r: Point<E, Unknown>,
    pub s: E::Fs,
}

pub struct PrivateKey<E: JubjubEngine>(pub E::Fs);

#[derive(Clone)]
pub struct PublicKey<E: JubjubEngine>(pub Point<E, Unknown>);

#[derive(Clone)]
pub struct Seed<E: JubjubEngine>(pub E::Fs);

impl<E: JubjubEngine> Seed<E> {
    pub fn random_seed<R: Rng>(rng: &mut R, msg: &[u8]) -> Self {
        // T = (l_H + 128) bits of randomness
        // For H*, l_H = 512 bits
        let mut t = [0u8; 80];
        rng.fill_bytes(&mut t[..]);

        // Generate randomness using hash function based on some entropy and the message
        // Generation of randommess is completely off-chain, so we use BLAKE2b!
        // r = H*(T || M)
        Seed(h_star::<E>(&t[..], msg))
    }

    pub fn deterministic_seed(pk: &PrivateKey<E>, msg: &[u8]) -> Self {
        use std::slice;

        let mut hasher = Sha256::new();
        hasher.input(msg);
        let h1 = hasher.result(); // h1 = sha256(msg)

        let zero = [0x00];
        let one = [0x01];
        let mut v = [1u8; 32];  // v = 0x01 0x01 0x01 ... 0x01
        let mut key = [0u8; 32]; //  key = 0x00 0x00 0x00 ... 0x00

        let mut mac = HmacSha256::new_varkey(&key).expect("HMAC can take key of any size");
        
        let mut priv_key = [0u8; 32];
        pk.0.into_repr().write_be(&mut priv_key[..]).expect("PK must be representable as bytes slice");

        // concatenated = v || 0x00 || priv_key || h1
        let mut concatenated: Vec<u8> = v.as_ref().to_vec();
        concatenated.extend_from_slice(&zero[..]);
        concatenated.extend_from_slice(&priv_key[..]);
        concatenated.extend_from_slice(h1.as_slice());

        mac.input(&concatenated[..]);
        key.copy_from_slice(mac.clone().result().code().as_mut_slice()); // key = HMAC(key, concatenated)

        mac = HmacSha256::new_varkey(&key).expect("HMAC can take key of any size");
        mac.input(&v);
        v.copy_from_slice(mac.clone().result().code().as_mut_slice()); // v = HMAC(key, v)

        // concatenated = v || 0x01 || priv_key || h1
        concatenated = v.as_ref().to_vec();
        concatenated.extend_from_slice(&one[..]);
        concatenated.extend_from_slice(&priv_key[..]);
        concatenated.extend_from_slice(h1.as_slice());
        
        mac = HmacSha256::new_varkey(&key).expect("HMAC can take key of any size");
        mac.input(&concatenated[..]);
        key.copy_from_slice(mac.clone().result().code().as_mut_slice()); // key = HMAC(key, concatenated)

        mac = HmacSha256::new_varkey(&key).expect("HMAC can take key of any size");
        mac.input(&v);
        v.copy_from_slice(mac.clone().result().code().as_mut_slice()); // v = HMAC(key, v)

        loop {
            let mut k_slice = [0u8; 32];
            mac = HmacSha256::new_varkey(&key).expect("HMAC can take key of any size");
            mac.input(&v);
            k_slice.copy_from_slice(mac.clone().result().code().as_mut_slice()); // k = HMAC(key, v)

            // k E [1; MODULUS-1]
            let mut s_repr = <E::Fs as PrimeField>::Repr::default();
            s_repr.read_be(&k_slice[..]).expect("Should be a valid scalar");
            if let Ok(k) = E::Fs::from_repr(s_repr) {
                return Seed(k)
            } else {
                // concatenated = v || 0x00
                concatenated = v.as_ref().to_vec();
                concatenated.extend_from_slice(&zero[..]);
                mac.input(&concatenated[..]);
                key.copy_from_slice(mac.clone().result().code().as_mut_slice()); // key = HMAC(key, concatenated)
            }
        }
    }
}

impl SerializedSignature {
    pub fn read<R: Read>(mut reader: R) -> io::Result<Self> {
        let mut rbar = [0u8; 32];
        let mut sbar = [0u8; 32];
        reader.read_exact(&mut rbar)?;
        reader.read_exact(&mut sbar)?;
        Ok(SerializedSignature { rbar, sbar })
    }

    pub fn write<W: Write>(&self, mut writer: W) -> io::Result<()> {
        writer.write_all(&self.rbar)?;
        writer.write_all(&self.sbar)
    }
}

impl<E: JubjubEngine> PrivateKey<E> {
    pub fn randomize(&self, alpha: E::Fs) -> Self {
        let mut tmp = self.0;
        tmp.add_assign(&alpha);
        PrivateKey(tmp)
    }

    pub fn read<R: Read>(reader: R) -> io::Result<Self> {
        let pk = read_scalar::<E, R>(reader)?;
        Ok(PrivateKey(pk))
    }

    pub fn write<W: Write>(&self, writer: W) -> io::Result<()> {
        write_scalar::<E, W>(&self.0, writer)
    }

    pub fn sign_raw_message(
        &self,
        msg: &[u8],
        seed: &Seed<E>,
        p_g: FixedGenerators,
        params: &E::Params,
        max_message_size: usize,
    ) -> Signature<E> {
        let pk = PublicKey::from_private(&self, p_g, params);
        let order_check = pk.0.mul(E::Fs::char(), params);
        assert!(order_check.eq(&Point::zero()));

        // R = seed . P_G
        let r_g = params.generator(p_g).mul(seed.0, params);

        // In a VERY LIMITED case of messages known to be unique due to application level
        // and being less than the group order when interpreted as integer, one can sign
        // the message directly without hashing

        assert!(msg.len() <= max_message_size);
        assert!(max_message_size * 8 <= E::Fs::CAPACITY as usize);
        // we also pad message to max size

        // pad with zeroes to match representation length
        let mut msg_padded : Vec<u8> = msg.to_vec();
        for _ in 0..(32 - msg.len()) {
            msg_padded.extend(&[0u8;1]);
        }

        // S = seed + M . sk
        let mut s = E::Fs::to_uniform_32(msg_padded.as_ref());
        
        s.mul_assign(&self.0);
        s.add_assign(&seed.0);
    
        let as_unknown = Point::from(r_g);
        Signature { r: as_unknown, s }
    }


    // This is a plain Schnorr signature that does not capture public key into the hash
    pub fn sign_schnorr_blake2s(
        &self,
        msg: &[u8],
        seed: &Seed<E>,
        p_g: FixedGenerators,
        params: &E::Params,
    ) -> Signature<E> {
        let pk = PublicKey::from_private(&self, p_g, params);
        let order_check = pk.0.mul(E::Fs::char(), params);
        assert!(order_check.eq(&Point::zero()));

        // for hash function for a part that is INSIDE the zkSNARK it's 
        // BLAKE2s has 512 of input and 256 bits of output,
        // so we use R_X || M as an input to hash only (without public key component),
        // with a point coordinate padded to 256 bits

        // R = seed . P_G
        let r_g = params.generator(p_g).mul(seed.0, params);

        let (r_g_x, _) = r_g.into_xy();
        let mut r_g_x_bytes = [0u8; 32];
        r_g_x.into_repr().write_le(& mut r_g_x_bytes[..]).expect("has serialized r_g_x");

        // we also pad message to 256 bits as LE

        let concatenated: Vec<u8> = r_g_x_bytes.iter().cloned().collect();

        let mut msg_padded : Vec<u8> = msg.to_vec();
        msg_padded.resize(32, 0u8);

        // S = r + H*(R_X || M) . sk
        let mut s = h_star_s::<E>(&concatenated[..], &msg_padded[..]);
        s.mul_assign(&self.0);
        s.add_assign(&seed.0);
    
        let as_unknown = Point::from(r_g);
        Signature { r: as_unknown, s }
    }

    // sign a message by following MuSig protocol, with public key being just a trivial key,
    // not a multisignature one
    pub fn musig_sha256_sign(
        &self,
        msg: &[u8],
        seed: &Seed<E>,
        p_g: FixedGenerators,
        params: &E::Params,
    ) -> Signature<E> {
        let pk = PublicKey::from_private(&self, p_g, params);
        let order_check = pk.0.mul(E::Fs::char(), params);
        assert!(order_check.eq(&Point::zero()));

        let (pk_x, _) = pk.0.into_xy();
        let mut pk_x_bytes = [0u8; 32];
        pk_x.into_repr().write_le(& mut pk_x_bytes[..]).expect("has serialized pk_x");

        // for hash function for a part that is INSIDE the zkSNARK it's 
        // sha256 that has 3*256 of input and 256 bits of output,
        // so we use PK_X || R_X || M as an input to hash,
        // with a point coordinates padded to 256 bits

        // R = seed . P_G
        let r_g = params.generator(p_g).mul(seed.0, params);

        let (r_g_x, _) = r_g.into_xy();
        let mut r_g_x_bytes = [0u8; 32];
        r_g_x.into_repr().write_le(& mut r_g_x_bytes[..]).expect("has serialized r_g_x");

        // we also pad message to 256 bits as LE

        let mut concatenated: Vec<u8> = pk_x_bytes.as_ref().to_vec();
        concatenated.extend(r_g_x_bytes.as_ref().to_vec().into_iter());

        let mut msg_padded : Vec<u8> = msg.to_vec();
        msg_padded.resize(32, 0u8);

        // S = r + H*(PK_X || R_X || M) . sk
        let mut s = sha256_h_star::<E>(&concatenated[..], &msg_padded[..]);
        s.mul_assign(&self.0);
        s.add_assign(&seed.0);
    
        let as_unknown = Point::from(r_g);
        Signature { r: as_unknown, s }
    }

    // sign a message by following MuSig protocol, with public key being just a trivial key,
    // not a multisignature one
    pub fn musig_pedersen_sign(
        &self,
        msg: &[u8],
        seed: &Seed<E>,
        p_g: FixedGenerators,
        params: &E::Params,
    ) -> Signature<E> {
        let pk = PublicKey::from_private(&self, p_g, params);
        let order_check = pk.0.mul(E::Fs::char(), params);
        assert!(order_check.eq(&Point::zero()));

        let (pk_x, _) = pk.0.into_xy();
        let mut pk_x_bits: Vec<bool> = BitIterator::new(pk_x.into_repr()).collect();
        pk_x_bits.reverse();
        pk_x_bits.resize(256, false);

        // R = seed . P_G
        let r_g = params.generator(p_g).mul(seed.0, params);

        let (r_g_x, _) = r_g.into_xy();
        let mut r_g_x_bits: Vec<bool> = BitIterator::new(r_g_x.into_repr()).collect();
        r_g_x_bits.reverse();
        r_g_x_bits.resize(256, false);


        let mut concatenated_bits: Vec<bool> = pk_x_bits;
        concatenated_bits.extend(r_g_x_bits);
        let phash_concatenated: E::Fr = baby_pedersen_hash::<E,_>(Personalization::NoteCommitment, concatenated_bits, &params).into_xy().0;
        let mut phash_first_bits: Vec<bool> = BitIterator::new(phash_concatenated.into_repr()).collect();
        phash_first_bits.reverse();
        phash_first_bits.resize(256, false);
        // we also pad message to 256 bits as LE
        let mut msg_padded : Vec<u8> = msg.to_vec();
        msg_padded.resize(32, 0u8);
        
        //le_bits
        let mut msg_bits = vec![];
        for msg_byte in msg_padded{
            for i in 0..8{
                msg_bits.push(msg_byte & 1<<i != 0);
            }  
        }
        let mut to_hash_bits = vec![];
        to_hash_bits.extend(phash_first_bits);
        to_hash_bits.extend(msg_bits);
        // S = r + H*(PK_X || R_X || M) . sk
        let mut s = pedersen_h_star::<E>(&to_hash_bits, params);
        s.mul_assign(&self.0);
        s.add_assign(&seed.0);
    
        let as_unknown = Point::from(r_g);
        Signature { r: as_unknown, s }
    }

    pub fn sign(
        &self,
        msg: &[u8],
        seed: &Seed<E>,
        p_g: FixedGenerators,
        params: &E::Params,
    ) -> Signature<E> {
        let pk = PublicKey::from_private(&self, p_g, params);
        let order_check = pk.0.mul(E::Fs::char(), params);
        assert!(order_check.eq(&Point::zero()));

        // for hash function for a part that is INSIDE the zkSNARK it's 
        // BLAKE2s has 512 of input and 256 bits of output,
        // so we use R_X || M as an input to hash only (without public key component), with point coordinates badded to 

        // R = seed . P_G
        let r_g = params.generator(p_g).mul(seed.0, params);

        let (r_g_x, r_g_y) = r_g.into_xy();
        let mut r_g_x_bytes = [0u8; 32];
        r_g_x.into_repr().write_le(& mut r_g_x_bytes[..]).expect("has serialized r_g_x");

        let mut r_g_y_bytes = [0u8; 32];
        r_g_y.into_repr().write_le(& mut r_g_y_bytes[..]).expect("has serialized r_g_y");

        let (pk_x, pk_y) = pk.0.into_xy();
        let mut pk_x_bytes = [0u8; 32];
        pk_x.into_repr().write_le(& mut pk_x_bytes[..]).expect("has serialized pk_x");

        let mut pk_y_bytes = [0u8; 32];
        pk_y.into_repr().write_le(& mut pk_y_bytes[..]).expect("has serialized pk_y");

        let concatenated: Vec<u8> = r_g_x_bytes.iter().chain(r_g_y_bytes.iter()).chain(pk_x_bytes.iter()).chain(pk_y_bytes.iter()).cloned().collect();

        // S = r + H*(Rbar || Pk || M) . sk
        let mut s = h_star::<E>(&concatenated[..], msg);
        s.mul_assign(&self.0);
        s.add_assign(&seed.0);
    
        let as_unknown = Point::from(r_g);
        Signature { r: as_unknown, s }
    }
}

impl<E: RescueEngine + JubjubEngine> PrivateKey<E> {
    // sign a message by following MuSig protocol, with public key being just a trivial key,
    // not a multisignature one
    pub fn musig_rescue_sign(
        &self,
        msg: &[u8],
        seed: &Seed<E>,
        p_g: FixedGenerators,
        rescue_params: &<E as RescueEngine>::Params,
        jubjub_params: &<E as JubjubEngine>::Params,
    ) -> Signature<E> {
        assert!(msg.len() <= 32);
        let pk = PublicKey::from_private(&self, p_g, jubjub_params);
        let order_check = pk.0.mul(E::Fs::char(), jubjub_params);
        assert!(order_check.eq(&Point::zero()));

        let (pk_x, _) = pk.0.into_xy();
        let mut pk_x_bytes = [0u8; 32];
        pk_x.into_repr().write_le(& mut pk_x_bytes[..]).expect("has serialized pk_x");

        // R = seed . P_G
        let r_g = jubjub_params.generator(p_g).mul(seed.0, jubjub_params);

        let (r_g_x, _) = r_g.into_xy();
        let mut r_g_x_bytes = [0u8; 32];
        r_g_x.into_repr().write_le(& mut r_g_x_bytes[..]).expect("has serialized r_g_x");

        // we also pad message to 256 bits as LE

        let mut concatenated: Vec<u8> = pk_x_bytes.as_ref().to_vec();
        concatenated.extend(r_g_x_bytes.as_ref().to_vec().into_iter());

        let mut msg_padded : Vec<u8> = msg.to_vec();
        msg_padded.resize(32, 0u8);

        // S = r + H*(PK_X || R_X || M) . sk
        let mut s = rescue_h_star::<E>(&concatenated[..], &msg_padded[..], &rescue_params);
        s.mul_assign(&self.0);
        s.add_assign(&seed.0);

        let as_unknown = Point::from(r_g);
        Signature { r: as_unknown, s }
    }

    // sign a message by following MuSig protocol, with public key being just a trivial key,
    // not a multisignature one
    pub fn field_musig_rescue_sign(
        &self,
        msg: E::Fr,
        seed: &Seed<E>,
        p_g: FixedGenerators,
        rescue_params: &<E as RescueEngine>::Params,
        jubjub_params: &<E as JubjubEngine>::Params,
    ) -> Signature<E> {
        // assert!(msg.len() <= 32);
        let pk = PublicKey::from_private(&self, p_g, jubjub_params);
        let order_check = pk.0.mul(E::Fs::char(), jubjub_params);
        assert!(order_check.eq(&Point::zero()));

        let (pk_x, _) = pk.0.into_xy();
        // R = seed . P_G
        let r_g = jubjub_params.generator(p_g).mul(seed.0, jubjub_params);
        let (r_g_x, _) = r_g.into_xy();

        // S = r + H*(PK_X || R_X || M) . sk
        let mut s = field_rescue_h_star::<E>(pk_x, r_g_x, msg, &rescue_params);
        s.mul_assign(&self.0);
        s.add_assign(&seed.0);

        let as_unknown = Point::from(r_g);
        Signature { r: as_unknown, s }
    }

}

impl<E: JubjubEngine> PublicKey<E> {
    pub fn from_private(privkey: &PrivateKey<E>, p_g: FixedGenerators, params: &E::Params) -> Self {
        let res = params.generator(p_g).mul(privkey.0, params).into();
        PublicKey(res)
    }

    pub fn randomize(&self, alpha: E::Fs, p_g: FixedGenerators, params: &E::Params) -> Self {
        let res: Point<E, Unknown> = params.generator(p_g).mul(alpha, params).into();
        let res = res.add(&self.0, params);
        PublicKey(res)
    }

    pub fn read<R: Read>(reader: R, params: &E::Params) -> io::Result<Self> {
        let p = Point::read(reader, params)?;
        Ok(PublicKey(p))
    }

    pub fn write<W: Write>(&self, writer: W) -> io::Result<()> {
        self.0.write(writer)
    }

    pub fn verify(
        &self,
        msg: &[u8],
        sig: &Signature<E>,
        p_g: FixedGenerators,
        params: &E::Params,
    ) -> bool {
        // c = H*(Rbar || Pk || M)
        let (r_g_x, r_g_y) = sig.r.into_xy();
        let mut r_g_x_bytes = [0u8; 32];
        r_g_x.into_repr().write_le(& mut r_g_x_bytes[..]).expect("has serialized r_g_x");

        let mut r_g_y_bytes = [0u8; 32];
        r_g_y.into_repr().write_le(& mut r_g_y_bytes[..]).expect("has serialized r_g_y");

        let (pk_x, pk_y) = self.0.into_xy();
        let mut pk_x_bytes = [0u8; 32];
        pk_x.into_repr().write_le(& mut pk_x_bytes[..]).expect("has serialized pk_x");

        let mut pk_y_bytes = [0u8; 32];
        pk_y.into_repr().write_le(& mut pk_y_bytes[..]).expect("has serialized pk_y");

        let concatenated: Vec<u8> = r_g_x_bytes.iter().chain(r_g_y_bytes.iter()).chain(pk_x_bytes.iter()).chain(pk_y_bytes.iter()).cloned().collect();

        let c = h_star::<E>(&concatenated[..], msg);

        // this one is for a simple sanity check. In application purposes the pk will always be in a right group 
        let order_check_pk = self.0.mul(E::Fs::char(), params);
        if !order_check_pk.eq(&Point::zero()) {
            return false;
        }

        // r is input from user, so always check it!
        let order_check_r = sig.r.mul(E::Fs::char(), params);
        if !order_check_r.eq(&Point::zero()) {
            return false;
        }

        // 0 = h_G(-S . P_G + R + c . vk)
        // self.0.mul(c, params).add(&sig.r, params).add(
        //     &params.generator(p_g).mul(sig.s, params).negate().into(),
        //     params
        // ).mul_by_cofactor(params).eq(&Point::zero());


        // 0 = -S . P_G + R + c . vk that requires all points to be in the same group
        self.0.mul(c, params).add(&sig.r, params).add(
            &params.generator(p_g).mul(sig.s, params).negate().into(),
            params
        ).eq(&Point::zero())
    }

    pub fn verify_for_raw_message(
        &self,
        msg: &[u8],
        sig: &Signature<E>,
        p_g: FixedGenerators,
        params: &E::Params,
        max_message_size: usize,
    ) -> bool {
        // c = M

        assert!(msg.len() <= max_message_size);
        assert!(max_message_size * 8 <= E::Fs::CAPACITY as usize);
        // assert!(max_message_size * 8 <= E::Fs::Repr::len());
        // we also pad message to max size

        // pad with zeroes to match representation length
        let mut msg_padded : Vec<u8> = msg.to_vec();
        msg_padded.resize(32, 0u8);

        let c = E::Fs::to_uniform_32(msg_padded.as_ref());

        // this one is for a simple sanity check. In application purposes the pk will always be in a right group 
        let order_check_pk = self.0.mul(E::Fs::char(), params);
        if !order_check_pk.eq(&Point::zero()) {
            return false;
        }

        // r is input from user, so always check it!
        let order_check_r = sig.r.mul(E::Fs::char(), params);
        if !order_check_r.eq(&Point::zero()) {
            return false;
        }

        // 0 = h_G(-S . P_G + R + c . vk)
        // self.0.mul(c, params).add(&sig.r, params).add(
        //     &params.generator(p_g).mul(sig.s, params).negate().into(),
        //     params
        // ).mul_by_cofactor(params).eq(&Point::zero());


        // 0 = -S . P_G + R + c . vk that requires all points to be in the same group
        self.0.mul(c, params).add(&sig.r, params).add(
            &params.generator(p_g).mul(sig.s, params).negate().into(),
            params
        ).eq(&Point::zero())
    }
    
    pub fn verify_schnorr_blake2s(
        &self,
        msg: &[u8],
        sig: &Signature<E>,
        p_g: FixedGenerators,
        params: &E::Params,
    ) -> bool {
        assert!(msg.len() <= 32);

        // c = H*(R_x || M)
        let (r_g_x, _) = sig.r.into_xy();
        let mut r_g_x_bytes = [0u8; 32];
        r_g_x.into_repr().write_le(& mut r_g_x_bytes[..]).expect("has serialized r_g_x");

        let concatenated: Vec<u8> = r_g_x_bytes.iter().cloned().collect();

        let mut msg_padded : Vec<u8> = msg.to_vec();
        msg_padded.resize(32, 0u8);

        let c = h_star_s::<E>(&concatenated[..], &msg_padded[..]);

        // this one is for a simple sanity check. In application purposes the pk will always be in a right group 
        let order_check_pk = self.0.mul(E::Fs::char(), params);
        if !order_check_pk.eq(&Point::zero()) {
            return false;
        }

        // r is input from user, so always check it!
        let order_check_r = sig.r.mul(E::Fs::char(), params);
        if !order_check_r.eq(&Point::zero()) {
            return false;
        }

        // 0 = h_G(-S . P_G + R + c . vk)
        // self.0.mul(c, params).add(&sig.r, params).add(
        //     &params.generator(p_g).mul(sig.s, params).negate().into(),
        //     params
        // ).mul_by_cofactor(params).eq(&Point::zero());


        // 0 = -S . P_G + R + c . vk that requires all points to be in the same group
        self.0.mul(c, params).add(&sig.r, params).add(
            &params.generator(p_g).mul(sig.s, params).negate().into(),
            params
        ).eq(&Point::zero())
    }


    // verify MuSig. While we are on the Edwards curve with cofactor,
    // verification will be successful if and only if every element is in the main group
    pub fn verify_musig_pedersen(
        &self,
        msg: &[u8],
        sig: &Signature<E>,
        p_g: FixedGenerators,
        params: &E::Params,
    ) -> bool {
        assert!(msg.len() <= 32);

        let (pk_x, _) = self.0.into_xy();
        let mut pk_x_bits: Vec<bool> = BitIterator::new(pk_x.into_repr()).collect();
        pk_x_bits.reverse();
        pk_x_bits.resize(256, false);

        let (r_g_x, _) = sig.r.into_xy();
        let mut r_g_x_bits: Vec<bool> = BitIterator::new(r_g_x.into_repr()).collect();
        r_g_x_bits.reverse();
        r_g_x_bits.resize(256, false);


        let mut concatenated_bits: Vec<bool> = pk_x_bits;
        concatenated_bits.extend(r_g_x_bits);
        let phash_concatenated = baby_pedersen_hash::<E,_>(Personalization::NoteCommitment, concatenated_bits, &params).into_xy().0;
        let mut phash_first_bits: Vec<bool> = BitIterator::new(phash_concatenated.into_repr()).collect();
        phash_first_bits.reverse();
        phash_first_bits.resize(256, false);
        // we also pad message to 256 bits as LE
        let mut msg_padded : Vec<u8> = msg.to_vec();
        msg_padded.resize(32, 0u8);
        
        //le_bits
        let mut msg_bits = vec![];
        for msg_byte in msg_padded{
            for i in 0..8{
                msg_bits.push(msg_byte & 1<<i != 0);
            }  
        }
        let mut to_hash_bits = vec![];
        to_hash_bits.extend(phash_first_bits);
        to_hash_bits.extend(msg_bits);
        // S = r + H*(PK_X || R_X || M) . sk
        let c = pedersen_h_star::<E>(&to_hash_bits, params);

        // this one is for a simple sanity check. In application purposes the pk will always be in a right group 
        let order_check_pk = self.0.mul(E::Fs::char(), params);
        if !order_check_pk.eq(&Point::zero()) {
            return false;
        }

        // r is input from user, so always check it!
        let order_check_r = sig.r.mul(E::Fs::char(), params);
        if !order_check_r.eq(&Point::zero()) {
            return false;
        }

        // 0 = h_G(-S . P_G + R + c . vk)
        // self.0.mul(c, params).add(&sig.r, params).add(
        //     &params.generator(p_g).mul(sig.s, params).negate().into(),
        //     params
        // ).mul_by_cofactor(params).eq(&Point::zero());

        // 0 = -S . P_G + R + c . vk that requires all points to be in the same group
        self.0.mul(c, params).add(&sig.r, params).add(
            &params.generator(p_g).mul(sig.s, params).negate().into(),
            params
        ).eq(&Point::zero())
    }

    // verify MuSig. While we are on the Edwards curve with cofactor,
    // verification will be successful if and only if every element is in the main group
    pub fn verify_musig_sha256(
        &self,
        msg: &[u8],
        sig: &Signature<E>,
        p_g: FixedGenerators,
        params: &E::Params,
    ) -> bool {
        assert!(msg.len() <= 32);

        // c = H*(PK_x || R_x || M)
        let (pk_x, _) = self.0.into_xy();
        let mut pk_x_bytes = [0u8; 32];
        pk_x.into_repr().write_le(& mut pk_x_bytes[..]).expect("has serialized pk_x");

        let (r_g_x, _) = sig.r.into_xy();
        let mut r_g_x_bytes = [0u8; 32];
        r_g_x.into_repr().write_le(& mut r_g_x_bytes[..]).expect("has serialized r_g_x");

        let mut concatenated: Vec<u8> = pk_x_bytes.as_ref().to_vec();
        concatenated.extend(r_g_x_bytes.as_ref().to_vec().into_iter());

        let mut msg_padded : Vec<u8> = msg.to_vec();
        msg_padded.resize(32, 0u8);

        let c = sha256_h_star::<E>(&concatenated[..], &msg_padded[..]);

        // this one is for a simple sanity check. In application purposes the pk will always be in a right group 
        let order_check_pk = self.0.mul(E::Fs::char(), params);
        if !order_check_pk.eq(&Point::zero()) {
            return false;
        }

        // r is input from user, so always check it!
        let order_check_r = sig.r.mul(E::Fs::char(), params);
        if !order_check_r.eq(&Point::zero()) {
            return false;
        }

        // 0 = h_G(-S . P_G + R + c . vk)
        // self.0.mul(c, params).add(&sig.r, params).add(
        //     &params.generator(p_g).mul(sig.s, params).negate().into(),
        //     params
        // ).mul_by_cofactor(params).eq(&Point::zero());

        // 0 = -S . P_G + R + c . vk that requires all points to be in the same group
        self.0.mul(c, params).add(&sig.r, params).add(
            &params.generator(p_g).mul(sig.s, params).negate().into(),
            params
        ).eq(&Point::zero())
    }

    pub fn verify_serialized(
        &self,
        msg: &[u8],
        sig: &SerializedSignature,
        p_g: FixedGenerators,
        params: &E::Params,
    ) -> bool {
        // c = H*(Rbar || M)
        let c = h_star::<E>(&sig.rbar[..], msg);

        // Signature checks:
        // R != invalid
        let r = match Point::read(&sig.rbar[..], params) {
            Ok(r) => r,
            Err(_) => return false,
        };
        // S < order(G)
        // (E::Fs guarantees its representation is in the field)
        let s = match read_scalar::<E, &[u8]>(&sig.sbar[..]) {
            Ok(s) => s,
            Err(_) => return false,
        };
        // 0 = h_G(-S . P_G + R + c . vk)
        self.0.mul(c, params).add(&r, params).add(
            &params.generator(p_g).mul(s, params).negate().into(),
            params
        ).mul_by_cofactor(params).eq(&Point::zero())
    }
}

impl<E: RescueEngine + JubjubEngine> PublicKey<E> {
// verify MuSig. While we are on the Edwards curve with cofactor,
    // verification will be successful if and only if every element is in the main group
    pub fn verify_field_musig_rescue(
        &self,
        msg: E::Fr,
        sig: &Signature<E>,
        p_g: FixedGenerators,
        rescue_params: &<E as RescueEngine>::Params,
        jubjub_params: &<E as JubjubEngine>::Params,
    ) -> bool {
        // c = H*(PK_x || R_x || M)
        let (pk_x, _) = self.0.into_xy();
        let (r_g_x, _) = sig.r.into_xy();
        let c = field_rescue_h_star::<E>(pk_x, r_g_x, msg, rescue_params);

        // this one is for a simple sanity check. In application purposes the pk will always be in a right group
        let order_check_pk = self.0.mul(E::Fs::char(), jubjub_params);
        if !order_check_pk.eq(&Point::zero()) {
            return false;
        }

        // r is input from user, so always check it!
        let order_check_r = sig.r.mul(E::Fs::char(), jubjub_params);
        if !order_check_r.eq(&Point::zero()) {
            return false;
        }

        // 0 = -S . P_G + R + c . vk that requires all points to be in the same group
        self.0.mul(c, jubjub_params).add(&sig.r, jubjub_params).add(
            &jubjub_params.generator(p_g).mul(sig.s, jubjub_params).negate().into(),
            jubjub_params
        ).eq(&Point::zero())
    }

    pub fn verify_musig_rescue(
        &self,
        msg: &[u8],
        sig: &Signature<E>,
        p_g: FixedGenerators,
        rescue_params: &<E as RescueEngine>::Params,
        jubjub_params: &<E as JubjubEngine>::Params,
    ) -> bool {
        assert!(msg.len() <= 32);

        // c = H*(PK_x || R_x || M)
        let (pk_x, _) = self.0.into_xy();
        let mut pk_x_bytes = [0u8; 32];
        pk_x.into_repr().write_le(& mut pk_x_bytes[..]).expect("has serialized pk_x");

        let (r_g_x, _) = sig.r.into_xy();
        let mut r_g_x_bytes = [0u8; 32];
        r_g_x.into_repr().write_le(& mut r_g_x_bytes[..]).expect("has serialized r_g_x");

        let mut concatenated: Vec<u8> = pk_x_bytes.as_ref().to_vec();
        concatenated.extend(r_g_x_bytes.as_ref().to_vec().into_iter());

        let mut msg_padded : Vec<u8> = msg.to_vec();
        msg_padded.resize(32, 0u8);

        let c = rescue_h_star::<E>(&concatenated[..], &msg_padded[..], rescue_params);

        // this one is for a simple sanity check. In application purposes the pk will always be in a right group 
        let order_check_pk = self.0.mul(E::Fs::char(), jubjub_params);
        if !order_check_pk.eq(&Point::zero()) {
            return false;
        }

        // r is input from user, so always check it!
        let order_check_r = sig.r.mul(E::Fs::char(), jubjub_params);
        if !order_check_r.eq(&Point::zero()) {
            return false;
        }

        // 0 = h_G(-S . P_G + R + c . vk)
        // self.0.mul(c, params).add(&sig.r, params).add(
        //     &params.generator(p_g).mul(sig.s, params).negate().into(),
        //     params
        // ).mul_by_cofactor(params).eq(&Point::zero());

        // 0 = -S . P_G + R + c . vk that requires all points to be in the same group
        self.0.mul(c, jubjub_params).add(&sig.r, jubjub_params).add(
            &jubjub_params.generator(p_g).mul(sig.s, jubjub_params).negate().into(),
            jubjub_params
        ).eq(&Point::zero())
    }
}

#[cfg(test)]
mod baby_tests {
    use bellman::pairing::bn256::Bn256;
    use rand::{XorShiftRng, SeedableRng, thread_rng};

    use alt_babyjubjub::{AltJubjubBn256, fs::Fs, edwards, FixedGenerators};

    use super::*;

    #[test]
    fn deterministic_seed() {
        let rng = &mut thread_rng();
        let msg = b"Foo bar";
        let sk = PrivateKey::<Bn256>(rng.gen());
        let seed1 = Seed::deterministic_seed(&sk, msg);
        let seed2 = Seed::deterministic_seed(&sk, msg);
        assert_eq!(seed1.0, seed2.0);
    }

    #[test]
    fn random_seed() {
        let rng = &mut thread_rng();
        let msg = b"Foo bar";
        let seed1 = Seed::<Bn256>::random_seed(rng, msg);
        let seed2 = Seed::<Bn256>::random_seed(rng, msg);
        assert_ne!(seed1.0, seed2.0);
    }

    #[test]
    fn cofactor_check() {
        let rng = &mut thread_rng();
        let params = &AltJubjubBn256::new();
        let zero = edwards::Point::zero();
        let p_g = FixedGenerators::SpendingKeyGenerator;

        // Get a point of order 8
        let p8 = loop {
            let r = edwards::Point::<Bn256, _>::rand(rng, params).mul(Fs::char(), params);

            let r2 = r.double(params);
            let r4 = r2.double(params);
            let r8 = r4.double(params);

            if r2 != zero && r4 != zero && r8 == zero {
                break r;
            }
        };

        let sk = PrivateKey::<Bn256>(rng.gen());
        let vk = PublicKey::from_private(&sk, p_g, params);

        let msg = b"Foo bar";
        let seed = Seed::random_seed(rng, msg);
        let sig = sk.sign(msg, &seed, p_g, params);
        assert!(vk.verify(msg, &sig, p_g, params));

        // in contrast to redjubjub, in this implementation out-of-group R is NOT allowed!
        let vktorsion = PublicKey(vk.0.add(&p8, params));
        assert!(!vktorsion.verify(msg, &sig, p_g, params));

        let rtorsion = sig.r.add(&p8, params);
        let mut sig_torsion = sig;
        sig_torsion.r = rtorsion;
        assert!(!vk.verify(msg, &sig_torsion, p_g, params));
    }

    // #[test]
    // fn round_trip_serialization() {
    //     let rng = &mut thread_rng();
    //     let p_g = FixedGenerators::SpendingKeyGenerator;
    //     let params = &AltJubjubBn256::new();

    //     for _ in 0..1000 {
    //         let sk = PrivateKey::<Bn256>(rng.gen());
    //         let vk = PublicKey::from_private(&sk, p_g, params);
    //         let msg = b"Foo bar";
    //         let sig = sk.sign(msg, rng, p_g, params);

    //         let mut sk_bytes = [0u8; 32];
    //         let mut vk_bytes = [0u8; 32];
    //         let mut sig_bytes = [0u8; 64];
    //         sk.write(&mut sk_bytes[..]).unwrap();
    //         vk.write(&mut vk_bytes[..]).unwrap();
    //         sig.write(&mut sig_bytes[..]).unwrap();

    //         let sk_2 = PrivateKey::<Bn256>::read(&sk_bytes[..]).unwrap();
    //         let vk_2 = PublicKey::from_private(&sk_2, p_g, params);
    //         let mut vk_2_bytes = [0u8; 32];
    //         vk_2.write(&mut vk_2_bytes[..]).unwrap();
    //         assert!(vk_bytes == vk_2_bytes);

    //         let vk_2 = PublicKey::<Bn256>::read(&vk_bytes[..], params).unwrap();
    //         let sig_2 = Signature::read(&sig_bytes[..]).unwrap();
    //         assert!(vk.verify(msg, &sig_2, p_g, params));
    //         assert!(vk_2.verify(msg, &sig, p_g, params));
    //         assert!(vk_2.verify(msg, &sig_2, p_g, params));
    //     }
    // }

    #[test]
    fn random_signatures() {
        let rng = &mut thread_rng();
        let p_g = FixedGenerators::SpendingKeyGenerator;
        let params = &AltJubjubBn256::new();

        for _ in 0..1000 {
            let sk = PrivateKey::<Bn256>(rng.gen());
            let vk = PublicKey::from_private(&sk, p_g, params);

            let msg1 = b"Foo bar";
            let msg2 = b"Spam eggs";

            let seed1 = Seed::random_seed(rng, msg1);
            let seed2 = Seed::random_seed(rng, msg2);

            let sig1 = sk.sign(msg1, &seed1, p_g, params);
            let sig2 = sk.sign(msg2, &seed2, p_g, params);

            assert!(vk.verify(msg1, &sig1, p_g, params));
            assert!(vk.verify(msg2, &sig2, p_g, params));
            assert!(!vk.verify(msg1, &sig2, p_g, params));
            assert!(!vk.verify(msg2, &sig1, p_g, params));

            let alpha = rng.gen();
            let rsk = sk.randomize(alpha);
            let rvk = vk.randomize(alpha, p_g, params);

            let sig1 = rsk.sign(msg1, &seed1, p_g, params);
            let sig2 = rsk.sign(msg2, &seed2, p_g, params);

            assert!(rvk.verify(msg1, &sig1, p_g, params));
            assert!(rvk.verify(msg2, &sig2, p_g, params));
            assert!(!rvk.verify(msg1, &sig2, p_g, params));
            assert!(!rvk.verify(msg2, &sig1, p_g, params));
        }
    }

    #[test]
    fn random_signatures_for_snark() {
        let rng = &mut thread_rng();
        let p_g = FixedGenerators::SpendingKeyGenerator;
        let params = &AltJubjubBn256::new();

        for _ in 0..1000 {
            let sk = PrivateKey::<Bn256>(rng.gen());
            let vk = PublicKey::from_private(&sk, p_g, params);

            let msg1 = b"Foo bar";
            let msg2 = b"Spam eggs";

            let seed1 = Seed::random_seed(rng, msg1);
            let seed2 = Seed::random_seed(rng, msg2);

            let sig1 = sk.sign_schnorr_blake2s(msg1, &seed1, p_g, params);
            let sig2 = sk.sign_schnorr_blake2s(msg2, &seed2, p_g, params);

            assert!(vk.verify_schnorr_blake2s(msg1, &sig1, p_g, params));
            assert!(vk.verify_schnorr_blake2s(msg2, &sig2, p_g, params));
            assert!(!vk.verify_schnorr_blake2s(msg1, &sig2, p_g, params));
            assert!(!vk.verify_schnorr_blake2s(msg2, &sig1, p_g, params));

            let alpha = rng.gen();
            let rsk = sk.randomize(alpha);
            let rvk = vk.randomize(alpha, p_g, params);

            let sig1 = rsk.sign_schnorr_blake2s(msg1, &seed1, p_g, params);
            let sig2 = rsk.sign_schnorr_blake2s(msg2, &seed2, p_g, params);

            assert!(rvk.verify_schnorr_blake2s(msg1, &sig1, p_g, params));
            assert!(rvk.verify_schnorr_blake2s(msg2, &sig2, p_g, params));
            assert!(!rvk.verify_schnorr_blake2s(msg1, &sig2, p_g, params));
            assert!(!rvk.verify_schnorr_blake2s(msg2, &sig1, p_g, params));
        }
    }

    #[test]
    fn random_signatures_for_raw_message() {
        let rng = &mut thread_rng();
        let p_g = FixedGenerators::SpendingKeyGenerator;
        let params = &AltJubjubBn256::new();

        for _ in 0..1000 {
            let sk = PrivateKey::<Bn256>(rng.gen());
            let vk = PublicKey::from_private(&sk, p_g, params);

            let msg1 = b"Foo bar";
            let msg2 = b"Spam eggs";

            let max_message_size: usize = 16;

            let seed1 = Seed::random_seed(rng, msg1);
            let seed2 = Seed::random_seed(rng, msg2);

            let sig1 = sk.sign_raw_message(msg1, &seed1, p_g, params, max_message_size);
            let sig2 = sk.sign_raw_message(msg2, &seed2, p_g, params, max_message_size);

            assert!(vk.verify_for_raw_message(msg1, &sig1, p_g, params, max_message_size));
            assert!(vk.verify_for_raw_message(msg2, &sig2, p_g, params, max_message_size));
            assert!(!vk.verify_for_raw_message(msg1, &sig2, p_g, params, max_message_size));
            assert!(!vk.verify_for_raw_message(msg2, &sig1, p_g, params, max_message_size));

            let alpha = rng.gen();
            let rsk = sk.randomize(alpha);
            let rvk = vk.randomize(alpha, p_g, params);

            let sig1 = rsk.sign_raw_message(msg1, &seed1, p_g, params, max_message_size);
            let sig2 = rsk.sign_raw_message(msg2, &seed2, p_g, params, max_message_size);

            assert!(rvk.verify_for_raw_message(msg1, &sig1, p_g, params, max_message_size));
            assert!(rvk.verify_for_raw_message(msg2, &sig2, p_g, params, max_message_size));
            assert!(!rvk.verify_for_raw_message(msg1, &sig2, p_g, params, max_message_size));
            assert!(!rvk.verify_for_raw_message(msg2, &sig1, p_g, params, max_message_size));
        }
    }

    #[test]
    fn random_signatures_for_sha256_musig() {
        let rng = &mut thread_rng();
        let p_g = FixedGenerators::SpendingKeyGenerator;
        let params = &AltJubjubBn256::new();

        for _ in 0..1000 {
            let sk = PrivateKey::<Bn256>(rng.gen());
            let vk = PublicKey::from_private(&sk, p_g, params);

            let msg1 = b"Foo bar";
            let msg2 = b"Spam eggs";

            let max_message_size: usize = 16;

            let seed1 = Seed::random_seed(rng, msg1);
            let seed2 = Seed::random_seed(rng, msg2);

            let sig1 = sk.musig_sha256_sign(msg1, &seed1, p_g, params);
            let sig2 = sk.musig_sha256_sign(msg2, &seed2, p_g, params);

            assert!(vk.verify_musig_sha256(msg1, &sig1, p_g, params));
            assert!(vk.verify_musig_sha256(msg2, &sig2, p_g, params));
            assert!(!vk.verify_musig_sha256(msg1, &sig2, p_g, params));
            assert!(!vk.verify_musig_sha256(msg2, &sig1, p_g, params));

            let alpha = rng.gen();
            let rsk = sk.randomize(alpha);
            let rvk = vk.randomize(alpha, p_g, params);

            let sig1 = rsk.musig_sha256_sign(msg1, &seed1, p_g, params);
            let sig2 = rsk.musig_sha256_sign(msg2, &seed2, p_g, params);

            assert!(rvk.verify_musig_sha256(msg1, &sig1, p_g, params));
            assert!(rvk.verify_musig_sha256(msg2, &sig2, p_g, params));
            assert!(!rvk.verify_musig_sha256(msg1, &sig2, p_g, params));
            assert!(!rvk.verify_musig_sha256(msg2, &sig1, p_g, params));
        }
    }

    #[test]
    fn random_signatures_for_pedersen_musig() {
        let rng = &mut thread_rng();
        let p_g = FixedGenerators::SpendingKeyGenerator;
        let params = &AltJubjubBn256::new();

        for _ in 0..1000 {
            let sk = PrivateKey::<Bn256>(rng.gen());
            let vk = PublicKey::from_private(&sk, p_g, params);

            let msg1 = b"Foo bar";
            let msg2 = b"Spam eggs";

            let max_message_size: usize = 16;

            let seed1 = Seed::random_seed(rng, msg1);
            let seed2 = Seed::random_seed(rng, msg2);

            let sig1 = sk.musig_pedersen_sign(msg1, &seed1, p_g, params);
            let sig2 = sk.musig_pedersen_sign(msg2, &seed2, p_g, params);

            assert!(vk.verify_musig_pedersen(msg1, &sig1, p_g, params));
            assert!(vk.verify_musig_pedersen(msg2, &sig2, p_g, params));
            assert!(!vk.verify_musig_pedersen(msg1, &sig2, p_g, params));
            assert!(!vk.verify_musig_pedersen(msg2, &sig1, p_g, params));

            let alpha = rng.gen();
            let rsk = sk.randomize(alpha);
            let rvk = vk.randomize(alpha, p_g, params);

            let sig1 = sk.musig_pedersen_sign(msg1, &seed1, p_g, params);
            let sig2 = sk.musig_pedersen_sign(msg2, &seed2, p_g, params);

            assert!(rvk.verify_musig_pedersen(msg1, &sig1, p_g, params));
            assert!(rvk.verify_musig_pedersen(msg2, &sig2, p_g, params));
            assert!(!rvk.verify_musig_pedersen(msg1, &sig2, p_g, params));
            assert!(!rvk.verify_musig_pedersen(msg2, &sig1, p_g, params));
        }
    }

    #[test]
    fn get_generator_for_signatures() {
        let rng = &mut thread_rng();
        let p_g = FixedGenerators::SpendingKeyGenerator;
        let params = &AltJubjubBn256::new();
        let s = <Bn256 as JubjubEngine>::Fs::one();
        let sk = PrivateKey::<Bn256>(s);
        let vk = PublicKey::from_private(&sk, p_g, params);
        let (x, y) = vk.0.into_xy();
        println!("Public generator x = {}, y = {}", x, y);
    }

    #[test]
    fn random_field_signatures_for_rescue_musig() {
        use crate::circuit::multipack;
        use crate::rescue::rescue_hash;
        let rng = &mut thread_rng();
        let p_g = FixedGenerators::SpendingKeyGenerator;
        let params = &AltJubjubBn256::new();
        let rescue_params = &crate::rescue::bn256::Bn256RescueParams::new_checked_2_into_1();

        for _ in 0..1000 {
            let sk = PrivateKey::<Bn256>(rng.gen());
            let vk = PublicKey::from_private(&sk, p_g, params);

            let msg1 = b"Foo bar";
            let msg2 = b"Spam eggs";

            let field_msg1 = multipack::compute_multipacking::<Bn256>(&multipack::bytes_to_bits(msg1));
            let field_msg2 = multipack::compute_multipacking::<Bn256>(&multipack::bytes_to_bits(msg2));

            let hashed_msg1 = rescue_hash::<Bn256>(rescue_params, &field_msg1);
            let hashed_msg2 = rescue_hash::<Bn256>(rescue_params, &field_msg2);
            assert_eq!(hashed_msg1.len(), 1);
            assert_eq!(hashed_msg2.len(), 1);

            let seed1 = Seed::random_seed(rng, msg1);
            let seed2 = Seed::random_seed(rng, msg2);

            let sig1 = sk.field_musig_rescue_sign(hashed_msg1[0], &seed1, p_g, rescue_params, params);
            let sig2 = sk.field_musig_rescue_sign(hashed_msg2[0], &seed2, p_g, rescue_params, params);

            assert!(vk.verify_field_musig_rescue(hashed_msg1[0], &sig1, p_g, rescue_params, params));
            assert!(vk.verify_field_musig_rescue(hashed_msg2[0], &sig2, p_g, rescue_params, params));
            assert!(!vk.verify_field_musig_rescue(hashed_msg1[0], &sig2, p_g, rescue_params, params));
            assert!(!vk.verify_field_musig_rescue(hashed_msg2[0], &sig1, p_g, rescue_params, params));

            let alpha = rng.gen();
            let rsk = sk.randomize(alpha);
            let rvk = vk.randomize(alpha, p_g, params);

            let sig1 = rsk.field_musig_rescue_sign(hashed_msg1[0], &seed1, p_g, rescue_params, params);
            let sig2 = rsk.field_musig_rescue_sign(hashed_msg2[0], &seed2, p_g, rescue_params, params);

            assert!(rvk.verify_field_musig_rescue(hashed_msg1[0], &sig1, p_g, rescue_params, params));
            assert!(rvk.verify_field_musig_rescue(hashed_msg2[0], &sig2, p_g, rescue_params, params));
            assert!(!rvk.verify_field_musig_rescue(hashed_msg1[0], &sig2, p_g, rescue_params, params));
            assert!(!rvk.verify_field_musig_rescue(hashed_msg2[0], &sig1, p_g, rescue_params, params));
        }
    }

    #[test]
    fn random_signatures_for_rescue_musig() {
        let rng = &mut thread_rng();
        let p_g = FixedGenerators::SpendingKeyGenerator;
        let params = &AltJubjubBn256::new();
        let rescue_params = &crate::rescue::bn256::Bn256RescueParams::new_checked_2_into_1();

        for _ in 0..1000 {
            let sk = PrivateKey::<Bn256>(rng.gen());
            let vk = PublicKey::from_private(&sk, p_g, params);

            let msg1 = b"Foo bar";
            let msg2 = b"Spam eggs";

            let max_message_size: usize = 16;

            let seed1 = Seed::random_seed(rng, msg1);
            let seed2 = Seed::random_seed(rng, msg2);

            let sig1 = sk.musig_rescue_sign(msg1, &seed1, p_g, rescue_params, params);
            let sig2 = sk.musig_rescue_sign(msg2, &seed2, p_g, rescue_params, params);

            assert!(vk.verify_musig_rescue(msg1, &sig1, p_g, rescue_params, params));
            assert!(vk.verify_musig_rescue(msg2, &sig2, p_g, rescue_params, params));
            assert!(!vk.verify_musig_rescue(msg1, &sig2, p_g, rescue_params, params));
            assert!(!vk.verify_musig_rescue(msg2, &sig1, p_g, rescue_params, params));

            let alpha = rng.gen();
            let rsk = sk.randomize(alpha);
            let rvk = vk.randomize(alpha, p_g, params);

            let sig1 = rsk.musig_rescue_sign(msg1, &seed1, p_g, rescue_params, params);
            let sig2 = rsk.musig_rescue_sign(msg2, &seed2, p_g, rescue_params, params);

            assert!(rvk.verify_musig_rescue(msg1, &sig1, p_g, rescue_params, params));
            assert!(rvk.verify_musig_rescue(msg2, &sig2, p_g, rescue_params, params));
            assert!(!rvk.verify_musig_rescue(msg1, &sig2, p_g, rescue_params, params));
            assert!(!rvk.verify_musig_rescue(msg2, &sig1, p_g, rescue_params, params));
        }
    }

    #[test]
    fn output_signatures_for_rescue_musig() {
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        let p_g = FixedGenerators::SpendingKeyGenerator;
        let params = &AltJubjubBn256::new();
        let rescue_params = &crate::rescue::bn256::Bn256RescueParams::new_checked_2_into_1();

        let sk = PrivateKey::<Bn256>(rng.gen());
        let vk = PublicKey::from_private(&sk, p_g, params);
        
        println!("SK = {}", sk.0);
        let (x, y) = vk.0.into_xy();
        println!("VK.x = {}", x);
        println!("VK.y = {}", y);

        for msg in vec![vec![], hex::decode("72").unwrap(), hex::decode("af82").unwrap()].into_iter() {
            let seed = Seed::deterministic_seed(&sk, &msg);
            let sig = sk.musig_rescue_sign(&msg, &seed, p_g, rescue_params, params);

            let (x, y) = sig.r.into_xy();
            let s = sig.s;
            println!("Sig R.x = {}", x);
            println!("Sig R.y = {}", y);
            println!("Sig s = {}", s);
        }
    }
}
