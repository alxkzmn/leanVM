//! Keccak-f AIR adapted to this repository's `p3_air::Air` trait (the "Whirlaway-style" AIR).
//!
//! This is based on the `keccak_air/` folder in this repo (itself adapted from upstream Plonky3),
//! but expressed using `up_f()/down_f()` instead of matrix-row access.

extern crate alloc;

use alloc::vec::Vec;
use core::borrow::{Borrow, BorrowMut};
use core::mem::{size_of, transmute};

use core::marker::PhantomData;
use p3_air::{Air, AirBuilder};

use p3_field::PrimeCharacteristicRing;
use p3_util::indices_arr;

/// Total number of Keccak-f rounds.
pub const NUM_ROUNDS: usize = 24;
/// Number of Keccak-f rounds minus one.
pub const NUM_ROUNDS_MIN_1: usize = NUM_ROUNDS - 1;

/// Number of bits in each limb used to represent 64-bit words.
const BITS_PER_LIMB: usize = 16;
/// Number of limbs needed to represent a 64-bit word.
pub const U64_LIMBS: usize = 64 / BITS_PER_LIMB;

/// Number of rate bits in Keccak-f[1600] used for absorbing/squeezing.
const RATE_BITS: usize = 1088;
/// Number of limbs needed to represent the rate portion of the state.
const RATE_LIMBS: usize = RATE_BITS / BITS_PER_LIMB;

pub const R: [[u8; 5]; 5] = [
    [0, 36, 3, 41, 18],
    [1, 44, 10, 45, 2],
    [62, 6, 43, 15, 61],
    [28, 55, 25, 21, 56],
    [27, 20, 39, 8, 14],
];

pub const RC: [u64; 24] = [
    0x0000000000000001,
    0x0000000000008082,
    0x800000000000808A,
    0x8000000080008000,
    0x000000000000808B,
    0x0000000080000001,
    0x8000000080008081,
    0x8000000000008009,
    0x000000000000008A,
    0x0000000000000088,
    0x0000000080008009,
    0x000000008000000A,
    0x000000008000808B,
    0x800000000000008B,
    0x8000000000008089,
    0x8000000000008003,
    0x8000000000008002,
    0x8000000000000080,
    0x000000000000800A,
    0x800000008000000A,
    0x8000000080008081,
    0x8000000000008080,
    0x0000000080000001,
    0x8000000080008008,
];

#[inline(always)]
pub(crate) const fn rc_value_bit(round: usize, bit_index: usize) -> u8 {
    ((RC[round] >> bit_index) & 1) as u8
}

/// Note: The ordering of each array is based on the input mapping.
///
/// The Keccak spec uses `s[w(5y + x) + z] = a[x][y][z]`, so we store in `y, x, z` order.
#[derive(Debug)]
#[repr(C)]
pub struct KeccakCols<T> {
    /// The `i`th value is set to 1 if we are in the `i`th round, otherwise 0.
    pub step_flags: [T; NUM_ROUNDS],

    /// Export flag: should only be enabled on final-step rows (`step_flags[23] = 1`).
    pub export: T,

    /// Permutation inputs, stored in y-major order.
    pub preimage: [[[T; U64_LIMBS]; 5]; 5],

    /// Round input limbs.
    pub a: [[[T; U64_LIMBS]; 5]; 5],

    /// C[x, z] bits.
    pub c: [[T; 64]; 5],

    /// C'[x, z] bits.
    pub c_prime: [[T; 64]; 5],

    /// A'[y, x, z] bits.
    pub a_prime: [[[T; 64]; 5]; 5],

    /// A''[y, x] limbs.
    pub a_prime_prime: [[[T; U64_LIMBS]; 5]; 5],

    /// The bits of `A''[0, 0]`.
    pub a_prime_prime_0_0_bits: [T; 64],

    /// Limbs of `A'''[0, 0] = A''[0, 0] XOR RC`.
    pub a_prime_prime_prime_0_0_limbs: [T; U64_LIMBS],
}

impl<T: Clone> KeccakCols<T> {
    #[inline(always)]
    pub fn b(&self, x: usize, y: usize, z: usize) -> T {
        debug_assert!(x < 5);
        debug_assert!(y < 5);
        debug_assert!(z < 64);

        // B is just a rotation of A', so these are aliases for A' registers.
        // From the spec, B[y, (2x + 3y) % 5] = ROT(A'[x, y], r[x, y]).
        // So, B[x, y] = ROT(A'[(x + 3y) % 5, x], r[(x + 3y) % 5, x]).
        let a = (x + 3 * y) % 5;
        let b = x;
        let rot = R[a][b] as usize;
        self.a_prime[b][a][(z + 64 - rot) % 64].clone()
    }

    #[inline(always)]
    pub fn a_prime_prime_prime(&self, y: usize, x: usize, limb: usize) -> T {
        debug_assert!(y < 5);
        debug_assert!(x < 5);
        debug_assert!(limb < U64_LIMBS);

        if y == 0 && x == 0 {
            self.a_prime_prime_prime_0_0_limbs[limb].clone()
        } else {
            self.a_prime_prime[y][x][limb].clone()
        }
    }
}

pub fn input_limb(i: usize) -> usize {
    debug_assert!(i < RATE_LIMBS);
    let i_u64 = i / U64_LIMBS;
    let limb_index = i % U64_LIMBS;
    let y = i_u64 / 5;
    let x = i_u64 % 5;
    KECCAK_COL_MAP.preimage[y][x][limb_index]
}

pub fn output_limb(i: usize) -> usize {
    debug_assert!(i < RATE_LIMBS);
    let i_u64 = i / U64_LIMBS;
    let limb_index = i % U64_LIMBS;
    let y = i_u64 / 5;
    let x = i_u64 % 5;
    KECCAK_COL_MAP.a_prime_prime_prime(y, x, limb_index)
}

pub const NUM_KECCAK_COLS: usize = size_of::<KeccakCols<u8>>();
pub(crate) const KECCAK_COL_MAP: KeccakCols<usize> = make_col_map();

const fn make_col_map() -> KeccakCols<usize> {
    unsafe { transmute(indices_arr::<NUM_KECCAK_COLS>()) }
}

impl<T> Borrow<KeccakCols<T>> for [T] {
    fn borrow(&self) -> &KeccakCols<T> {
        debug_assert_eq!(self.len(), NUM_KECCAK_COLS);
        let (prefix, shorts, suffix) = unsafe { self.align_to::<KeccakCols<T>>() };
        debug_assert!(prefix.is_empty(), "Alignment should match");
        debug_assert!(suffix.is_empty(), "Alignment should match");
        debug_assert_eq!(shorts.len(), 1);
        &shorts[0]
    }
}

impl<T> BorrowMut<KeccakCols<T>> for [T] {
    fn borrow_mut(&mut self) -> &mut KeccakCols<T> {
        debug_assert_eq!(self.len(), NUM_KECCAK_COLS);
        let (prefix, shorts, suffix) = unsafe { self.align_to_mut::<KeccakCols<T>>() };
        debug_assert!(prefix.is_empty(), "Alignment should match");
        debug_assert!(suffix.is_empty(), "Alignment should match");
        debug_assert_eq!(shorts.len(), 1);
        &mut shorts[0]
    }
}

/// An AIR for the Keccak-f permutation. Assumes field size is at least 16 bits.
#[derive(Debug, Default, Clone, Copy)]
pub struct KeccakAir<EF> {
    _phantom: PhantomData<EF>,
}

impl<EF> KeccakAir<EF> {
    pub fn new() -> Self {
        Self { _phantom: PhantomData }
    }
}

impl<EF: Send + Sync + 'static> Air for KeccakAir<EF> {
    type ExtraData = Vec<EF>;

    fn n_columns_f_air(&self) -> usize {
        NUM_KECCAK_COLS
    }

    fn n_columns_ef_air(&self) -> usize {
        0
    }

    fn degree(&self) -> usize {
        // xor3 is implemented as two xors => degree up to 4.
        4
    }

    fn n_constraints(&self) -> usize {
        // Counted from the constraint loops in `eval` below.
        3183
    }

    fn down_column_indexes_f(&self) -> Vec<usize> {
        // Easiest compatibility mode: expose the shifted ("next-row") value for every column
        // so we can index `down_f()` by the same column index as `up_f()`.
        (0..NUM_KECCAK_COLS).collect()
    }

    fn down_column_indexes_ef(&self) -> Vec<usize> {
        vec![]
    }

    #[inline]
    fn eval<AB: AirBuilder>(&self, builder: &mut AB, _: &Self::ExtraData) {
        // IMPORTANT: we must not hold references to `up_f()` / `down_f()` across `assert_zero` calls,
        // otherwise we'd keep an immutable borrow of `builder` while mutably borrowing it.
        // We therefore clone individual values as needed.

        // --- Round flags schedule (one-hot + rotation) ---
        let mut sum_flags = AB::F::ZERO;
        for i in 0..NUM_ROUNDS {
            let idx = KECCAK_COL_MAP.step_flags[i];
            let f_i = builder.up_f()[idx].clone();
            builder.assert_zero(f_i.bool_check());
            sum_flags += f_i;
        }
        builder.assert_zero(sum_flags - AB::F::ONE);

        // Rotate: local.flag[i] == next.flag[i+1] (mod 24)
        for i in 0..NUM_ROUNDS {
            let idx_local = KECCAK_COL_MAP.step_flags[i];
            let idx_next = KECCAK_COL_MAP.step_flags[(i + 1) % NUM_ROUNDS];
            let local_i = builder.up_f()[idx_local].clone();
            let next_ip1 = builder.down_f()[idx_next].clone();
            builder.assert_zero(local_i - next_ip1);
        }

        let first_step = builder.up_f()[KECCAK_COL_MAP.step_flags[0]].clone();
        let final_step = builder.up_f()[KECCAK_COL_MAP.step_flags[NUM_ROUNDS_MIN_1]].clone();
        let not_final_step = AB::F::ONE - final_step.clone();

        // --- Export flag ---
        let export = builder.up_f()[KECCAK_COL_MAP.export].clone();
        builder.assert_zero(export.clone().bool_check());
        // Enforce "off unless final step".
        builder.assert_zero(not_final_step.clone() * export);

        // --- Preimage constraints ---
        // If this is the first step, input A must match the preimage.
        for y in 0..5 {
            for x in 0..5 {
                for limb in 0..U64_LIMBS {
                    let pre_idx = KECCAK_COL_MAP.preimage[y][x][limb];
                    let a_idx = KECCAK_COL_MAP.a[y][x][limb];
                    let pre = builder.up_f()[pre_idx].clone();
                    let a = builder.up_f()[a_idx].clone();
                    builder.assert_zero(first_step.clone() * (pre - a));
                }
            }
        }

        // If this is not the final step, the local and next preimages must match.
        for y in 0..5 {
            for x in 0..5 {
                for limb in 0..U64_LIMBS {
                    let pre_idx = KECCAK_COL_MAP.preimage[y][x][limb];
                    let pre_local = builder.up_f()[pre_idx].clone();
                    let pre_next = builder.down_f()[pre_idx].clone();
                    builder.assert_zero(not_final_step.clone() * (pre_local - pre_next));
                }
            }
        }

        // --- C / C' ---
        for x in 0..5 {
            for z in 0..64 {
                let c_idx = KECCAK_COL_MAP.c[x][z];
                let c = builder.up_f()[c_idx].clone();
                builder.assert_zero(c.bool_check());
            }
            for z in 0..64 {
                let c0 = builder.up_f()[KECCAK_COL_MAP.c[x][z]].clone();
                let c1 = builder.up_f()[KECCAK_COL_MAP.c[(x + 4) % 5][z]].clone();
                let c2 = builder.up_f()[KECCAK_COL_MAP.c[(x + 1) % 5][(z + 63) % 64]].clone();
                let xor = c0.xor3(&c1, &c2);
                let c_prime = builder.up_f()[KECCAK_COL_MAP.c_prime[x][z]].clone();
                builder.assert_zero(c_prime - xor);
            }
        }

        // --- Check A limbs are consistent with A' and D ---
        // Also enforces A' bits are boolean.
        for y in 0..5 {
            for x in 0..5 {
                for z in 0..64 {
                    let ap = builder.up_f()[KECCAK_COL_MAP.a_prime[y][x][z]].clone();
                    builder.assert_zero(ap.bool_check());
                }
                for limb in 0..U64_LIMBS {
                    let mut acc = AB::F::ZERO;
                    for z in (limb * BITS_PER_LIMB..(limb + 1) * BITS_PER_LIMB).rev() {
                        let ap = builder.up_f()[KECCAK_COL_MAP.a_prime[y][x][z]].clone();
                        let c = builder.up_f()[KECCAK_COL_MAP.c[x][z]].clone();
                        let cp = builder.up_f()[KECCAK_COL_MAP.c_prime[x][z]].clone();
                        let bit = ap.xor3(&c, &cp);
                        acc = acc.double() + bit;
                    }
                    let a = builder.up_f()[KECCAK_COL_MAP.a[y][x][limb]].clone();
                    builder.assert_zero(acc - a);
                }
            }
        }

        // xor_{i=0}^4 A'[x, i, z] = C'[x, z] (in a generalized sense).
        for x in 0..5 {
            for z in 0..64 {
                let mut sum = AB::F::ZERO;
                for y in 0..5 {
                    sum += builder.up_f()[KECCAK_COL_MAP.a_prime[y][x][z]].clone();
                }
                let diff = sum - builder.up_f()[KECCAK_COL_MAP.c_prime[x][z]].clone();
                let four = AB::F::TWO.double();
                builder.assert_zero(diff.clone() * (diff.clone() - AB::F::TWO) * (diff - four));
            }
        }

        // --- A'' constraints (range check via boolean ops on B) ---
        for y in 0..5 {
            for x in 0..5 {
                for limb in 0..U64_LIMBS {
                    let mut acc = AB::F::ZERO;
                    for z in (limb * BITS_PER_LIMB..(limb + 1) * BITS_PER_LIMB).rev() {
                        // b(...) is derived from a_prime (up columns only).
                        let a = (x + 1 + 3 * y) % 5;
                        let b = (x + 1) % 5;
                        let rot1 = R[a][b] as usize;
                        let b1 = builder.up_f()[KECCAK_COL_MAP.a_prime[b][a][(z + 64 - rot1) % 64]].clone();

                        let a = (x + 2 + 3 * y) % 5;
                        let b = (x + 2) % 5;
                        let rot2 = R[a][b] as usize;
                        let b2 = builder.up_f()[KECCAK_COL_MAP.a_prime[b][a][(z + 64 - rot2) % 64]].clone();

                        let a = (x + 3 * y) % 5;
                        let b = x;
                        let rot0 = R[a][b] as usize;
                        let b0 = builder.up_f()[KECCAK_COL_MAP.a_prime[b][a][(z + 64 - rot0) % 64]].clone();

                        let andn = b1.andn(&b2);
                        let bit = andn.xor(&b0);
                        acc = acc.double() + bit;
                    }
                    let app = builder.up_f()[KECCAK_COL_MAP.a_prime_prime[y][x][limb]].clone();
                    builder.assert_zero(acc - app);
                }
            }
        }

        // A'''[0, 0] = A''[0, 0] XOR RC for this round.
        for z in 0..64 {
            let bit = builder.up_f()[KECCAK_COL_MAP.a_prime_prime_0_0_bits[z]].clone();
            builder.assert_zero(bit.bool_check());
        }

        for limb in 0..U64_LIMBS {
            let mut acc = AB::F::ZERO;
            for z in (limb * BITS_PER_LIMB..(limb + 1) * BITS_PER_LIMB).rev() {
                let bit = builder.up_f()[KECCAK_COL_MAP.a_prime_prime_0_0_bits[z]].clone();
                acc = acc.double() + bit;
            }
            let app = builder.up_f()[KECCAK_COL_MAP.a_prime_prime[0][0][limb]].clone();
            builder.assert_zero(acc - app);
        }

        for limb in 0..U64_LIMBS {
            let mut acc = AB::F::ZERO;
            for z in (limb * BITS_PER_LIMB..(limb + 1) * BITS_PER_LIMB).rev() {
                let mut rc_bit = AB::F::ZERO;
                for r in 0..NUM_ROUNDS {
                    let this_round = builder.up_f()[KECCAK_COL_MAP.step_flags[r]].clone();
                    let this_round_constant = AB::F::from_bool(rc_value_bit(r, z) != 0);
                    rc_bit += this_round * this_round_constant;
                }
                let a00 = builder.up_f()[KECCAK_COL_MAP.a_prime_prime_0_0_bits[z]].clone();
                let xored = rc_bit.xor(&a00);
                acc = acc.double() + xored;
            }
            let a000 = builder.up_f()[KECCAK_COL_MAP.a_prime_prime_prime_0_0_limbs[limb]].clone();
            builder.assert_zero(acc - a000);
        }

        // Enforce that this round's output equals the next round's input (except final step).
        for y in 0..5 {
            for x in 0..5 {
                for limb in 0..U64_LIMBS {
                    let out_idx = if y == 0 && x == 0 {
                        KECCAK_COL_MAP.a_prime_prime_prime_0_0_limbs[limb]
                    } else {
                        KECCAK_COL_MAP.a_prime_prime[y][x][limb]
                    };
                    let out = builder.up_f()[out_idx].clone();
                    let next_a = builder.down_f()[KECCAK_COL_MAP.a[y][x][limb]].clone();
                    builder.assert_zero(not_final_step.clone() * (out - next_a));
                }
            }
        }
    }
}

/// Subset of columns we need access to on the "next row" for the optimized AIR.
///
/// This matches exactly what `KeccakAirOptimizedDown` requests via `down_column_indexes_f()`.
#[derive(Debug)]
#[repr(C)]
pub struct KeccakDownCols<T> {
    pub step_flags: [T; NUM_ROUNDS],
    pub preimage: [[[T; U64_LIMBS]; 5]; 5],
    pub a: [[[T; U64_LIMBS]; 5]; 5],
}

pub const NUM_KECCAK_DOWN_COLS: usize = size_of::<KeccakDownCols<u8>>();

impl<T> Borrow<KeccakDownCols<T>> for [T] {
    fn borrow(&self) -> &KeccakDownCols<T> {
        debug_assert_eq!(self.len(), NUM_KECCAK_DOWN_COLS);
        let (prefix, shorts, suffix) = unsafe { self.align_to::<KeccakDownCols<T>>() };
        debug_assert!(prefix.is_empty(), "Alignment should match");
        debug_assert!(suffix.is_empty(), "Alignment should match");
        debug_assert_eq!(shorts.len(), 1);
        &shorts[0]
    }
}

/// Optimized version of the Keccak AIR: only requests the "next row" columns that are actually
/// used in constraints (instead of shifting every column).
#[derive(Debug, Default, Clone, Copy)]
pub struct KeccakAirOptimizedDown<EF> {
    _phantom: PhantomData<EF>,
}

impl<EF> KeccakAirOptimizedDown<EF> {
    pub fn new() -> Self {
        Self { _phantom: PhantomData }
    }

    /// Down-column indices in the same order as `KeccakDownCols<T>`.
    pub fn down_indices() -> Vec<usize> {
        let mut res = Vec::with_capacity(NUM_KECCAK_DOWN_COLS);
        for i in 0..NUM_ROUNDS {
            res.push(KECCAK_COL_MAP.step_flags[i]);
        }
        for y in 0..5 {
            for x in 0..5 {
                for limb in 0..U64_LIMBS {
                    res.push(KECCAK_COL_MAP.preimage[y][x][limb]);
                }
            }
        }
        for y in 0..5 {
            for x in 0..5 {
                for limb in 0..U64_LIMBS {
                    res.push(KECCAK_COL_MAP.a[y][x][limb]);
                }
            }
        }
        debug_assert_eq!(res.len(), NUM_KECCAK_DOWN_COLS);
        res
    }
}

impl<EF: Send + Sync + 'static> Air for KeccakAirOptimizedDown<EF> {
    type ExtraData = Vec<EF>;

    fn n_columns_f_air(&self) -> usize {
        NUM_KECCAK_COLS
    }

    fn n_columns_ef_air(&self) -> usize {
        0
    }

    fn degree(&self) -> usize {
        4
    }

    fn n_constraints(&self) -> usize {
        // Same constraints as `KeccakAir`.
        3183
    }

    fn down_column_indexes_f(&self) -> Vec<usize> {
        Self::down_indices()
    }

    fn down_column_indexes_ef(&self) -> Vec<usize> {
        vec![]
    }

    #[inline]
    fn eval<AB: AirBuilder>(&self, builder: &mut AB, _: &Self::ExtraData) {
        // Copy the down values once (small: 224 elements), so we can access them without borrowing `builder`.
        let down_vec = builder.down_f().to_vec();
        let next: &KeccakDownCols<AB::F> = down_vec.as_slice().borrow();

        // --- Round flags schedule (one-hot + rotation) ---
        let mut sum_flags = AB::F::ZERO;
        for i in 0..NUM_ROUNDS {
            let idx = KECCAK_COL_MAP.step_flags[i];
            let f_i = builder.up_f()[idx].clone();
            builder.assert_zero(f_i.bool_check());
            sum_flags += f_i;
        }
        builder.assert_zero(sum_flags - AB::F::ONE);

        // Rotate: local.flag[i] == next.flag[i+1] (mod 24)
        for i in 0..NUM_ROUNDS {
            let idx_local = KECCAK_COL_MAP.step_flags[i];
            let local_i = builder.up_f()[idx_local].clone();
            let next_ip1 = next.step_flags[(i + 1) % NUM_ROUNDS].clone();
            builder.assert_zero(local_i - next_ip1);
        }

        let first_step = builder.up_f()[KECCAK_COL_MAP.step_flags[0]].clone();
        let final_step = builder.up_f()[KECCAK_COL_MAP.step_flags[NUM_ROUNDS_MIN_1]].clone();
        let not_final_step = AB::F::ONE - final_step.clone();

        // --- Export flag ---
        let export = builder.up_f()[KECCAK_COL_MAP.export].clone();
        builder.assert_zero(export.clone().bool_check());
        builder.assert_zero(not_final_step.clone() * export);

        // --- Preimage constraints ---
        for y in 0..5 {
            for x in 0..5 {
                for limb in 0..U64_LIMBS {
                    let pre = builder.up_f()[KECCAK_COL_MAP.preimage[y][x][limb]].clone();
                    let a = builder.up_f()[KECCAK_COL_MAP.a[y][x][limb]].clone();
                    builder.assert_zero(first_step.clone() * (pre - a));
                }
            }
        }

        for y in 0..5 {
            for x in 0..5 {
                for limb in 0..U64_LIMBS {
                    let pre_local = builder.up_f()[KECCAK_COL_MAP.preimage[y][x][limb]].clone();
                    let pre_next = next.preimage[y][x][limb].clone();
                    builder.assert_zero(not_final_step.clone() * (pre_local - pre_next));
                }
            }
        }

        // --- C / C' ---
        for x in 0..5 {
            for z in 0..64 {
                let c = builder.up_f()[KECCAK_COL_MAP.c[x][z]].clone();
                builder.assert_zero(c.bool_check());
            }
            for z in 0..64 {
                let c0 = builder.up_f()[KECCAK_COL_MAP.c[x][z]].clone();
                let c1 = builder.up_f()[KECCAK_COL_MAP.c[(x + 4) % 5][z]].clone();
                let c2 = builder.up_f()[KECCAK_COL_MAP.c[(x + 1) % 5][(z + 63) % 64]].clone();
                let xor = c0.xor3(&c1, &c2);
                let c_prime = builder.up_f()[KECCAK_COL_MAP.c_prime[x][z]].clone();
                builder.assert_zero(c_prime - xor);
            }
        }

        // --- Check A limbs are consistent with A' and D ---
        for y in 0..5 {
            for x in 0..5 {
                for z in 0..64 {
                    let ap = builder.up_f()[KECCAK_COL_MAP.a_prime[y][x][z]].clone();
                    builder.assert_zero(ap.bool_check());
                }
                for limb in 0..U64_LIMBS {
                    let mut acc = AB::F::ZERO;
                    for z in (limb * BITS_PER_LIMB..(limb + 1) * BITS_PER_LIMB).rev() {
                        let ap = builder.up_f()[KECCAK_COL_MAP.a_prime[y][x][z]].clone();
                        let c = builder.up_f()[KECCAK_COL_MAP.c[x][z]].clone();
                        let cp = builder.up_f()[KECCAK_COL_MAP.c_prime[x][z]].clone();
                        let bit = ap.xor3(&c, &cp);
                        acc = acc.double() + bit;
                    }
                    let a = builder.up_f()[KECCAK_COL_MAP.a[y][x][limb]].clone();
                    builder.assert_zero(acc - a);
                }
            }
        }

        for x in 0..5 {
            for z in 0..64 {
                let mut sum = AB::F::ZERO;
                for y in 0..5 {
                    sum += builder.up_f()[KECCAK_COL_MAP.a_prime[y][x][z]].clone();
                }
                let diff = sum - builder.up_f()[KECCAK_COL_MAP.c_prime[x][z]].clone();
                let four = AB::F::TWO.double();
                builder.assert_zero(diff.clone() * (diff.clone() - AB::F::TWO) * (diff - four));
            }
        }

        // --- A'' constraints (range check via boolean ops on B) ---
        for y in 0..5 {
            for x in 0..5 {
                for limb in 0..U64_LIMBS {
                    let mut acc = AB::F::ZERO;
                    for z in (limb * BITS_PER_LIMB..(limb + 1) * BITS_PER_LIMB).rev() {
                        let a = (x + 1 + 3 * y) % 5;
                        let b = (x + 1) % 5;
                        let rot1 = R[a][b] as usize;
                        let b1 = builder.up_f()[KECCAK_COL_MAP.a_prime[b][a][(z + 64 - rot1) % 64]].clone();

                        let a = (x + 2 + 3 * y) % 5;
                        let b = (x + 2) % 5;
                        let rot2 = R[a][b] as usize;
                        let b2 = builder.up_f()[KECCAK_COL_MAP.a_prime[b][a][(z + 64 - rot2) % 64]].clone();

                        let a = (x + 3 * y) % 5;
                        let b = x;
                        let rot0 = R[a][b] as usize;
                        let b0 = builder.up_f()[KECCAK_COL_MAP.a_prime[b][a][(z + 64 - rot0) % 64]].clone();

                        let andn = b1.andn(&b2);
                        let bit = andn.xor(&b0);
                        acc = acc.double() + bit;
                    }
                    let app = builder.up_f()[KECCAK_COL_MAP.a_prime_prime[y][x][limb]].clone();
                    builder.assert_zero(acc - app);
                }
            }
        }

        // A'''[0, 0] = A''[0, 0] XOR RC for this round.
        for z in 0..64 {
            let bit = builder.up_f()[KECCAK_COL_MAP.a_prime_prime_0_0_bits[z]].clone();
            builder.assert_zero(bit.bool_check());
        }

        for limb in 0..U64_LIMBS {
            let mut acc = AB::F::ZERO;
            for z in (limb * BITS_PER_LIMB..(limb + 1) * BITS_PER_LIMB).rev() {
                let bit = builder.up_f()[KECCAK_COL_MAP.a_prime_prime_0_0_bits[z]].clone();
                acc = acc.double() + bit;
            }
            let app = builder.up_f()[KECCAK_COL_MAP.a_prime_prime[0][0][limb]].clone();
            builder.assert_zero(acc - app);
        }

        for limb in 0..U64_LIMBS {
            let mut acc = AB::F::ZERO;
            for z in (limb * BITS_PER_LIMB..(limb + 1) * BITS_PER_LIMB).rev() {
                let mut rc_bit = AB::F::ZERO;
                for r in 0..NUM_ROUNDS {
                    let this_round = builder.up_f()[KECCAK_COL_MAP.step_flags[r]].clone();
                    let this_round_constant = AB::F::from_bool(rc_value_bit(r, z) != 0);
                    rc_bit += this_round * this_round_constant;
                }
                let a00 = builder.up_f()[KECCAK_COL_MAP.a_prime_prime_0_0_bits[z]].clone();
                let xored = rc_bit.xor(&a00);
                acc = acc.double() + xored;
            }
            let a000 = builder.up_f()[KECCAK_COL_MAP.a_prime_prime_prime_0_0_limbs[limb]].clone();
            builder.assert_zero(acc - a000);
        }

        // Enforce that this round's output equals the next round's input (except final step).
        for y in 0..5 {
            for x in 0..5 {
                for limb in 0..U64_LIMBS {
                    let out_idx = if y == 0 && x == 0 {
                        KECCAK_COL_MAP.a_prime_prime_prime_0_0_limbs[limb]
                    } else {
                        KECCAK_COL_MAP.a_prime_prime[y][x][limb]
                    };
                    let out = builder.up_f()[out_idx].clone();
                    let next_a = next.a[y][x][limb].clone();
                    builder.assert_zero(not_final_step.clone() * (out - next_a));
                }
            }
        }
    }
}
