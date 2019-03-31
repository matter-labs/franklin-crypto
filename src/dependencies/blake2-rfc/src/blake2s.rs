// Copyright 2015 blake2-rfc Developers
// Copyright 2017 Google Inc.
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

//! The BLAKE2s hash function.
//!
//! # Examples
//!
//! ```
//! use blake2_rfc::blake2s::{Blake2s, blake2s};
//!
//! // Using the convenience function.
//! let hash = blake2s(32, &[], b"The quick brown fox jumps over the lazy dog");
//!
//! // Using the state context.
//! let mut context = Blake2s::new(32);
//! context.update(b"The quick brown fox jumps over the lazy dog");
//! let hash = context.finalize();
//!
//! // Using the convenience function, with a key.
//! let hash = blake2s(32, b"key", b"The quick brown fox jumps over the lazy dog");
//!
//! // Using the state context, with a key.
//! let mut context = Blake2s::with_key(32, b"key");
//! context.update(b"The quick brown fox jumps over the lazy dog");
//! let hash = context.finalize();
//! ```
//!
//! The returned hash is a `Blake2sResult`, which can be compared with
//! a byte string (the comparison will take constant time), or converted
//! into a byte string.

#![cfg_attr(feature = "cargo-clippy", allow(unreadable_literal))]

blake2_impl!(
    Blake2s, Blake2sResult, blake2s, u32,
    u32x4, read_u32, 32, 16, 12, 8, 7, [
    0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
    0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19,
]);

blake2_selftest_impl!(Blake2s, blake2s, [
    0x6A, 0x41, 0x1F, 0x08, 0xCE, 0x25, 0xAD, 0xCD,
    0xFB, 0x02, 0xAB, 0xA6, 0x41, 0x45, 0x1C, 0xEC,
    0x53, 0xC5, 0x98, 0xB2, 0x4F, 0x4F, 0xC7, 0x87,
    0xFB, 0xDC, 0x88, 0x79, 0x7F, 0x4C, 0x1D, 0xFE,
], [ 16, 20, 28, 32 ], [ 0,  3,  64, 65, 255, 1024 ]);

#[cfg(test)]
mod tests {
    #![cfg_attr(feature = "cargo-clippy", allow(result_unwrap_used))]

    extern crate data_encoding;
    use self::data_encoding::HEXUPPER;
    use self::data_encoding::HEXLOWER;

    use blake2::selftest_seq;
    use super::{Blake2s, blake2s};

    #[test]
    fn test_empty() {
        assert_eq!(&blake2s(32, &[], b""), &HEXUPPER.decode(
            b"69217A3079908094E11121D042354A7C1F55B6482CA1A51E1B250DFD1ED0EEF9")
            .unwrap()[..]);
    }

    #[test]
    fn test_default() {
        assert_eq!(&Blake2s::default().finalize(), &HEXUPPER.decode(
            b"69217A3079908094E11121D042354A7C1F55B6482CA1A51E1B250DFD1ED0EEF9")
            .unwrap()[..]);
    }

    #[test]
    fn test_persona() {
        let key_bytes = &HEXLOWER.decode(b"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f").unwrap();
        let persona = "personal";
        let persona_bytes = persona.as_bytes();
        let ctx = Blake2s::with_params(32, key_bytes, &[], persona_bytes);
        assert_eq!(&ctx.finalize(), &HEXLOWER.decode(b"25a4ee63b594aed3f88a971e1877ef7099534f9097291f88fb86c79b5e70d022").unwrap()[..]);
    }

    #[test]
    fn selftest() {
        super::selftest();
    }

    #[test]
    fn test_split() {
        let data = selftest_seq(256);

        let mut ctx = Blake2s::new(32);
        ctx.update(&data[..16]);
        ctx.update(&data[16..32]);
        ctx.update(&data[32..224]);
        ctx.update(&data[224..]);

        assert_eq!(&ctx.finalize(), &blake2s(32, &[], &data));
    }

    #[cfg(feature = "std")]
    #[test]
    fn test_write() {
        use std::io::prelude::*;

        let data = selftest_seq(1024);

        let mut ctx = Blake2s::new(32);
        ctx.update(&data[..]);

        let mut writer = Blake2s::new(32);
        writer.write_all(&data[..]).unwrap();

        assert_eq!(&writer.finalize(), &ctx.finalize());
    }

    #[cfg_attr(debug_assertions, ignore)]
    #[test]
    fn test_4g() {
        const ZEROS: [u8; 4096] = [0; 4096];

        let mut state = Blake2s::new(32);
        for _ in 0..1048576 {
            state.update(&ZEROS);
        }
        assert_eq!(&state.finalize(), &HEXUPPER.decode(
            b"2A8E26830310DA3EF7F7032B7B1AF11B989ABA44A3713A22F539F69BD2CE4A87")
            .unwrap()[..]);
    }
}
