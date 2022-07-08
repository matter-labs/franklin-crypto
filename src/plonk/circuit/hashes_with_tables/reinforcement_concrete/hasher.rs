use super::utils;
use crate::bellman::pairing::bls12_381::Bls12;
use crate::bellman::pairing::bn256::Bn256;
use crate::bellman::pairing::ff::*;
use crate::bellman::pairing::ff::{PrimeField, PrimeFieldRepr};
use crate::bellman::Engine;
use crate::lazy_static::lazy_static;
use crate::sha3::{digest::ExtendableOutput, digest::Update, Sha3XofReader, Shake128};
use std::sync::Arc;

#[derive(Clone, Debug)]
pub struct ReinforcedConcreteParams<F: PrimeField> {
    pub(crate) round_constants: Vec<Vec<F>>,
    pub(crate) alphas: [u16; 2],
    pub(crate) betas: [F; 2],
    pub(crate) si: Vec<u16>,
    pub(crate) divisor_i: Vec<u64>,
    pub(crate) reciprokal_i: Vec<u64>,
    pub(crate) norm_shift_i: Vec<u32>,
    pub(crate) sbox: Vec<u16>,
    pub(crate) d: usize,
    pub(crate) p_prime: u16,
}

impl<F: PrimeField> ReinforcedConcreteParams<F> {
    pub const PRE_ROUNDS: usize = 3;
    pub const POST_ROUNDS: usize = 3;
    pub const TOTAL_ROUNDS: usize = Self::PRE_ROUNDS + Self::POST_ROUNDS + 1;
    pub const T: usize = 3;
    pub const INIT_SHAKE: &'static str = "ReinforcedConcrete";

    pub fn new(d: usize, si: &[u16], sbox: &[u16], ab: &[u16]) -> Self {
        assert!(sbox.len() <= u16::MAX as usize);
        assert!(ab.len() == 4);

        let mut shake = Self::init_shake();
        let alphas = [ab[0], ab[1]];
        let betas = [utils::from_u64(ab[2] as u64), utils::from_u64(ab[3] as u64)];
        let round_constants = Self::instantiate_rc(&mut shake);
        let p_prime = sbox.len() as u16;

        let len = si.len();
        let mut divisor_i = Vec::with_capacity(len);
        let mut reciprokal_i = Vec::with_capacity(len);
        let mut norm_shift_i = Vec::with_capacity(len);
        for s in si {
            let (div, rec) = utils::compute_normalized_divisor_and_reciproical(*s);
            divisor_i.push(div);
            reciprokal_i.push(rec);
            norm_shift_i.push((*s as u64).leading_zeros());
        }

        ReinforcedConcreteParams {
            round_constants,
            alphas,
            betas,
            si: si.to_owned(),
            divisor_i,
            reciprokal_i,
            norm_shift_i,
            sbox: Self::pad_sbox(sbox, si),
            d,
            p_prime,
        }
    }

    fn init_shake() -> Sha3XofReader {
        let mut shake = Shake128::default();
        shake.update(Self::INIT_SHAKE);
        for i in F::char().as_ref() {
            shake.update(u64::to_le_bytes(*i));
        }
        shake.finalize_xof()
    }

    fn pad_sbox(sbox: &[u16], si: &[u16]) -> Vec<u16> {
        let len = sbox.len();

        let max = si.iter().max().expect("si are empty...").to_owned();
        let mut out = sbox.to_owned();

        out.reserve((max as usize) - len);
        for i in (len as u16)..max {
            out.push(i);
        }

        out
    }

    fn instantiate_rc(shake: &mut Sha3XofReader) -> Vec<Vec<F>> {
        (0..=Self::TOTAL_ROUNDS)
            .map(|_| {
                (0..Self::T)
                    .map(|_| utils::field_element_from_shake(shake))
                    .collect()
            })
            .collect()
    }

    pub fn get_t(&self) -> usize {
        Self::T
    }

    pub fn get_rounds(&self) -> usize {
        Self::TOTAL_ROUNDS
    }
}

#[derive(Clone, Debug)]
pub struct ReinforcedConcrete<F: PrimeField> {
    pub(crate) params: Arc<ReinforcedConcreteParams<F>>,
}

impl<F: PrimeField> ReinforcedConcrete<F> {
    pub fn new(params: &Arc<ReinforcedConcreteParams<F>>) -> Self {
        debug_assert!(ReinforcedConcreteParams::<F>::T == 3);
        ReinforcedConcrete {
            params: Arc::clone(params),
        }
    }

    pub fn concrete(&self, state: &mut [F; 3], round: usize) {
        // multiplication by circ(2 1 1) is equal to state + sum(state)

        let mut sum = state[0];
        state.iter().skip(1).for_each(|el| sum.add_assign(el));

        for (el, rc) in state
            .iter_mut()
            .zip(self.params.round_constants[round].iter())
        {
            el.add_assign(&sum);
            el.add_assign(rc); // add round constant
        }
    }

    pub fn bricks(&self, state: &[F; 3]) -> [F; 3] {
        let mut new_state: [F; 3] = [F::zero(); 3];

        // squaring
        let mut x1_sq = state[0];
        x1_sq.square();
        let mut x2_sq = state[1];
        x2_sq.square();

        // x1
        let mut x1 = x1_sq;
        match self.params.d {
            3 => {}
            5 => x1.square(),
            _ => panic!("not implemented!"),
        }
        x1.mul_assign(&state[0]);
        new_state[0] = x1;

        // x2
        for _ in 0..self.params.alphas[0] {
            x1_sq.add_assign(&state[0]);
        }
        x1_sq.add_assign(&self.params.betas[0]);
        x1_sq.mul_assign(&state[1]);
        new_state[1] = x1_sq;

        // x3
        for _ in 0..self.params.alphas[1] {
            x2_sq.add_assign(&state[1]);
        }
        x2_sq.add_assign(&self.params.betas[1]);
        x2_sq.mul_assign(&state[2]);
        new_state[2] = x2_sq;

        new_state
    }

    pub fn decompose(&self, val: &F) -> Vec<u16> {
        let len = self.params.si.len();
        let mut res = vec![0; len];
        let mut repr = val.into_repr();

        for i in (1..self.params.si.len()).rev() {
            let (r, m) = utils::divide_long_using_recip::<F>(
                &repr,
                self.params.divisor_i[i],
                self.params.reciprokal_i[i],
                self.params.norm_shift_i[i],
            );
            repr = r;
            res[i] = m;
        }

        res[0] = repr.as_ref()[0] as u16;

        // just debugging
        if cfg!(debug_assertions) {
            let repr_ref = repr.as_ref();
            debug_assert!(repr_ref[0] < self.params.si[0] as u64);
            repr_ref
                .iter()
                .skip(1)
                .for_each(|el| debug_assert!(*el == 0));
        }

        res
    }

    pub fn compose(&self, vals: &[u16]) -> F {
        let mut repr = F::Repr::default();
        repr.as_mut()[0] = vals[0] as u64;

        for (val, s) in vals.iter().zip(self.params.si.iter()).skip(1) {
            repr = utils::mul_by_single_word::<F>(&repr, *s as u64);
            repr = utils::add_single_word::<F>(&repr, *val as u64);
        }
        F::from_repr(repr).unwrap()
    }

    pub fn bars(&self, state: &[F; 3]) -> [F; 3] {
        let mut s = state.to_owned();
        for el in s.iter_mut() {
            let mut vals = self.decompose(&el);
            for val in vals.iter_mut() {
                // *val = self.params.sbox[*val as usize];
                // safe because sbox is padded to the correct size in params
                unsafe {
                    *val = *self.params.sbox.get_unchecked(*val as usize);
                }
            }
            *el = self.compose(&vals);
        }
        s
    }

    pub fn permutation(&self, input: &[F; 3]) -> [F; 3] {
        assert_eq!(ReinforcedConcreteParams::<F>::T, input.len());
        let mut current_state = input.to_owned();
        // first concrete
        self.concrete(&mut current_state, 0);

        // first rounds
        for i in 1..=ReinforcedConcreteParams::<F>::PRE_ROUNDS {
            current_state = self.bricks(&current_state);
            self.concrete(&mut current_state, i);
        }

        // bar round
        current_state = self.bars(&current_state);
        self.concrete(
            &mut current_state,
            ReinforcedConcreteParams::<F>::PRE_ROUNDS + 1,
        );

        // final rounds
        for i in ReinforcedConcreteParams::<F>::PRE_ROUNDS + 2
            ..=ReinforcedConcreteParams::<F>::TOTAL_ROUNDS
        {
            current_state = self.bricks(&current_state);
            self.concrete(&mut current_state, i);
        }
        current_state
    }

    pub fn hash(&self, el1: &F, el2: &F) -> F {
        let input: [F; 3] = [el1.to_owned(), el2.to_owned(), F::zero()];
        self.permutation(&input)[0]
    }

    // should be used for testing purposes only
    pub fn tester(&self, state: &[F; 3], elems_to_absorb: &[F; 2]) -> [F; 3] {
        let mut current_state = state.to_owned();
        current_state[0].add_assign(&elems_to_absorb[0]);
        current_state[1].add_assign(&elems_to_absorb[1]);
        self.permutation(&current_state)
    }
}

lazy_static! {
    // BLS12
    pub static ref BLS12_SI: Vec<u16> = vec![
        679, 703, 688, 691, 702, 703, 697, 698, 695, 701, 701, 701, 699, 694, 701, 694, 700, 688,
        700, 693, 691, 695, 679, 668, 694, 696, 693,
    ];
    pub static ref BLS12_AB: [u16; 4] = [1,3,2,4];
    pub static ref BLS12_SBOX: Vec<u16> = vec![
        171, 178, 483, 527, 653, 408, 197, 599, 300, 607, 403, 511, 579, 520, 591, 412, 261, 559,
        551, 154, 180, 138, 596, 150, 276, 271, 48, 168, 362, 637, 467, 164, 536, 554, 287, 530,
        431, 92, 654, 518, 323, 572, 624, 4, 258, 439, 430, 495, 534, 222, 545, 31, 44, 18, 80, 55,
        399, 328, 505, 313, 441, 586, 501, 598, 566, 568, 77, 496, 106, 563, 537, 78, 50, 450, 445,
        166, 237, 617, 185, 404, 621, 578, 133, 517, 646, 98, 86, 492, 267, 193, 33, 476, 207, 17,
        487, 643, 52, 384, 74, 148, 121, 657, 633, 528, 269, 611, 567, 601, 391, 231, 226, 658,
        331, 191, 354, 23, 474, 277, 390, 341, 279, 442, 422, 638, 15, 196, 329, 377, 36, 433, 398,
        72, 256, 352, 253, 550, 635, 142, 343, 176, 500, 588, 413, 569, 266, 42, 283, 535, 410,
        538, 647, 85, 27, 423, 558, 61, 356, 348, 43, 19, 625, 291, 238, 274, 432, 448, 100, 642,
        260, 587, 622, 608, 366, 420, 477, 316, 605, 254, 130, 407, 471, 174, 631, 34, 652, 628,
        175, 134, 122, 192, 531, 217, 32, 257, 145, 307, 262, 83, 509, 440, 600, 589, 359, 522,
        268, 143, 498, 512, 333, 651, 151, 183, 126, 351, 39, 246, 242, 630, 543, 574, 610, 655,
        25, 494, 456, 612, 123, 315, 340, 296, 580, 503, 281, 428, 62, 10, 76, 203, 288, 91, 426,
        128, 629, 29, 218, 292, 447, 161, 117, 388, 540, 364, 245, 541, 224, 502, 370, 229, 90,
        466, 636, 208, 51, 562, 259, 344, 334, 111, 235, 488, 632, 577, 54, 386, 75, 181, 463, 421,
        24, 96, 406, 156, 158, 265, 5, 310, 37, 124, 88, 155, 480, 593, 202, 451, 1, 497, 645, 457,
        187, 56, 206, 179, 640, 249, 99, 240, 460, 490, 163, 369, 293, 186, 553, 46, 449, 41, 219,
        308, 7, 234, 336, 373, 372, 347, 215, 481, 542, 146, 357, 656, 136, 330, 595, 516, 592,
        273, 365, 8, 47, 641, 81, 484, 573, 614, 437, 533, 0, 282, 184, 400, 49, 114, 374, 280,
        499, 418, 139, 382, 613, 233, 345, 393, 575, 508, 299, 101, 582, 360, 285, 2, 376, 548,
        189, 648, 214, 618, 385, 371, 425, 552, 204, 286, 443, 210, 294, 211, 241, 461, 275, 165,
        350, 59, 583, 159, 434, 252, 71, 436, 529, 236, 475, 339, 367, 147, 170, 110, 22, 298, 506,
        172, 247, 513, 73, 230, 314, 239, 157, 116, 65, 11, 570, 40, 620, 205, 251, 594, 468, 69,
        489, 109, 452, 465, 312, 383, 129, 379, 335, 353, 602, 546, 243, 57, 473, 486, 320, 162,
        526, 115, 26, 560, 107, 458, 519, 169, 97, 358, 504, 414, 13, 459, 132, 167, 402, 14, 491,
        571, 105, 112, 363, 581, 194, 84, 349, 201, 462, 289, 53, 603, 209, 396, 303, 317, 102, 82,
        131, 639, 3, 435, 378, 415, 539, 223, 30, 510, 199, 479, 397, 45, 248, 561, 67, 213, 438,
        20, 405, 557, 120, 89, 584, 555, 264, 419, 525, 429, 392, 311, 68, 446, 270, 585, 113, 627,
        472, 38, 375, 327, 127, 417, 547, 12, 108, 368, 95, 250, 322, 198, 380, 149, 104, 87, 332,
        135, 28, 318, 482, 221, 188, 58, 544, 521, 93, 324, 64, 272, 297, 644, 453, 225, 606, 295,
        216, 152, 411, 361, 444, 469, 427, 507, 395, 609, 153, 381, 464, 424, 94, 9, 564, 321, 615,
        21, 227, 137, 70, 326, 549, 556, 565, 416, 470, 255, 60, 604, 590, 305, 35, 278, 6, 125,
        387, 220, 597, 63, 454, 401, 119, 302, 309, 342, 16, 619, 493, 290, 616, 173, 304, 195,
        524, 263, 212, 649, 626, 409, 338, 306, 389, 79, 160, 66, 177, 232, 478, 514, 650, 455,
        103, 144, 355, 182, 346, 284, 200, 634, 244, 140, 337, 325, 319, 532, 394, 118, 485, 301,
        623, 190, 523, 515, 576, 141, 228
    ];
    pub static ref RC_BLS_PARAMS: Arc<ReinforcedConcreteParams<<Bls12 as ScalarEngine>::Fr>> =
        Arc::new(ReinforcedConcreteParams::new(5, &BLS12_SI, &BLS12_SBOX, BLS12_AB.as_ref()));
    // BN256
    pub static ref BN256_SI: Vec<u16> = vec![
        673, 678, 667, 683, 680, 655, 683, 683, 681, 683, 675, 668, 675, 677, 680, 681, 669, 683,
        681, 677, 668, 654, 663, 666, 656, 658, 651
    ];
    pub static ref BN256_AB: [u16; 4] = [1,3,2,4];
    pub static ref BN256_SBOX: Vec<u16> = vec![
        377, 222, 243, 537, 518, 373, 152, 435, 526, 352, 2, 410, 513, 545, 567, 354, 405, 80, 233,
        261, 49, 240, 568, 74, 131, 349, 146, 278, 330, 372, 43, 432, 247, 583, 105, 203, 637, 307,
        29, 597, 633, 198, 519, 95, 148, 62, 68, 312, 616, 357, 234, 433, 154, 90, 163, 249, 101,
        573, 447, 587, 494, 103, 608, 394, 409, 73, 317, 305, 346, 562, 262, 313, 303, 550, 64,
        102, 259, 400, 495, 572, 238, 40, 612, 236, 586, 15, 361, 386, 138, 136, 107, 33, 190, 423,
        176, 161, 460, 35, 202, 589, 32, 160, 444, 517, 490, 515, 144, 195, 269, 332, 25, 308, 192,
        276, 623, 180, 626, 217, 329, 66, 392, 431, 12, 478, 67, 232, 258, 355, 94, 191, 632, 181,
        298, 1, 301, 79, 618, 523, 627, 484, 306, 610, 635, 619, 544, 420, 408, 158, 328, 61, 406,
        299, 442, 178, 625, 621, 497, 465, 574, 143, 54, 57, 89, 322, 135, 96, 605, 599, 473, 97,
        85, 133, 200, 93, 291, 525, 529, 206, 614, 319, 196, 482, 17, 168, 70, 104, 441, 159, 364,
        603, 78, 150, 230, 116, 31, 630, 132, 69, 499, 532, 218, 492, 112, 505, 437, 333, 457, 456,
        439, 639, 398, 16, 436, 264, 450, 211, 241, 524, 294, 235, 126, 165, 527, 452, 212, 157,
        272, 208, 469, 611, 338, 83, 326, 151, 139, 607, 285, 585, 58, 14, 193, 71, 440, 511, 542,
        390, 470, 155, 413, 606, 142, 367, 371, 174, 5, 60, 289, 297, 336, 370, 76, 209, 622, 453,
        257, 555, 44, 430, 345, 335, 548, 459, 47, 426, 591, 559, 417, 284, 552, 137, 277, 281,
        463, 631, 350, 265, 323, 108, 290, 169, 634, 609, 414, 130, 6, 166, 316, 207, 592, 280,
        391, 274, 20, 300, 593, 549, 3, 602, 418, 472, 419, 296, 41, 46, 615, 638, 388, 553, 282,
        356, 327, 462, 115, 325, 121, 399, 273, 334, 383, 488, 292, 55, 628, 9, 19, 601, 496, 228,
        201, 576, 374, 558, 153, 162, 341, 353, 84, 220, 461, 221, 547, 344, 507, 577, 140, 485,
        471, 11, 175, 13, 53, 543, 270, 120, 30, 584, 384, 368, 397, 239, 4, 483, 620, 189, 522,
        540, 510, 149, 245, 533, 283, 256, 369, 302, 571, 128, 253, 448, 446, 183, 99, 438, 468,
        42, 594, 487, 403, 23, 172, 340, 106, 481, 251, 363, 295, 489, 474, 337, 87, 86, 246, 215,
        376, 315, 415, 117, 286, 600, 56, 145, 91, 358, 429, 411, 516, 310, 213, 598, 10, 395, 111,
        506, 237, 170, 512, 82, 147, 579, 402, 501, 343, 38, 434, 214, 314, 360, 77, 565, 320, 385,
        404, 199, 331, 351, 466, 596, 365, 231, 477, 604, 254, 268, 539, 424, 167, 378, 491, 535,
        141, 267, 177, 27, 546, 219, 556, 216, 451, 387, 28, 50, 569, 255, 288, 156, 449, 379, 508,
        528, 531, 624, 581, 554, 59, 171, 252, 0, 595, 185, 51, 520, 575, 475, 113, 187, 194, 428,
        500, 617, 188, 321, 179, 263, 110, 467, 18, 401, 22, 164, 342, 21, 382, 381, 127, 52, 570,
        45, 445, 36, 534, 339, 98, 293, 244, 266, 629, 229, 122, 123, 48, 88, 225, 173, 100, 114,
        536, 636, 205, 34, 425, 502, 514, 304, 613, 530, 118, 75, 561, 582, 81, 480, 92, 498, 464,
        224, 479, 563, 223, 640, 521, 427, 503, 250, 375, 186, 72, 242, 125, 380, 271, 204, 407,
        366, 197, 119, 7, 493, 26, 109, 65, 359, 396, 311, 309, 458, 134, 393, 557, 476, 324, 421,
        275, 37, 39, 580, 184, 560, 8, 455, 509, 422, 24, 287, 590, 182, 416, 318, 260, 578, 454,
        389, 129, 566, 63, 486, 541, 362, 210, 551, 348, 279, 538, 347, 504, 124, 564, 443, 412,
        226, 227, 248, 588
    ];
    pub static ref RC_BN_PARAMS: Arc<ReinforcedConcreteParams<<Bn256 as ScalarEngine>::Fr>> =
        Arc::new(ReinforcedConcreteParams::new(5, &BN256_SI, &BN256_SBOX, BN256_AB.as_ref()));
}

pub trait DefaultRcParams: Engine {
    fn get_default_rc_params() -> Arc<ReinforcedConcreteParams<<Self as ScalarEngine>::Fr>>;
}

impl DefaultRcParams for Bn256 {
    fn get_default_rc_params() -> Arc<ReinforcedConcreteParams<<Bn256 as ScalarEngine>::Fr>> {
        RC_BN_PARAMS.clone()
    }
}

impl DefaultRcParams for Bls12 {
    fn get_default_rc_params() -> Arc<ReinforcedConcreteParams<<Bls12 as ScalarEngine>::Fr>> {
        RC_BLS_PARAMS.clone()
    }
}
