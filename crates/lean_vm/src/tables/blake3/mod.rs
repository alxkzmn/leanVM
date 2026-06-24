use crate::{execution::memory::MemoryAccess, *};
use backend::*;
use std::{array, mem::size_of};

mod trace_gen;
pub use trace_gen::{blake3_hash_64_u16, fill_trace_blake3};

pub const BLAKE3_HASH_64_NAME: &str = "blake3_hash_64";
pub const BLAKE3_DOMAINSEP: usize = 6;

const BITS_PER_LIMB: usize = 16;
const U32_LIMBS: usize = 2;
const INPUT_WORDS: usize = 16;
pub const INPUT_LIMBS: usize = INPUT_WORDS * U32_LIMBS;
const OUTPUT_WORDS: usize = 8;
pub const OUTPUT_LIMBS: usize = OUTPUT_WORDS * U32_LIMBS;
const FULL_ROUNDS: usize = 7;
const QUARTER_ROUND_CONSTRAINTS: usize = 144;
const ROUND_CONSTRAINTS: usize = 8 * QUARTER_ROUND_CONSTRAINTS;
const FINAL_OUTPUT_CONSTRAINTS: usize = 528;
const INPUT_CONSTRAINTS: usize = INPUT_WORDS * (32 + U32_LIMBS);
const OUTPUT_CONSTRAINTS: usize = OUTPUT_WORDS * U32_LIMBS;

const IV: [u32; 8] = [
    0x6A09_E667,
    0xBB67_AE85,
    0x3C6E_F372,
    0xA54F_F53A,
    0x510E_527F,
    0x9B05_688C,
    0x1F83_D9AB,
    0x5BE0_CD19,
];

const CHUNK_START: u32 = 1;
const CHUNK_END: u32 = 2;
const ROOT: u32 = 8;
pub(super) const BLOCK_LEN: u32 = 64;
pub(super) const FLAGS: u32 = CHUNK_START | CHUNK_END | ROOT;

const MSG_PERMUTATION: [usize; 16] = [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8];

pub const BLAKE3_COL_MULTIPLICITY: ColIndex = 0;
pub const BLAKE3_COL_NU_A: ColIndex = 1;
pub const BLAKE3_COL_NU_B: ColIndex = 2;
pub const BLAKE3_COL_NU_C: ColIndex = 3;
pub const BLAKE3_COL_INPUT_LIMBS: ColIndex = 4;
pub const BLAKE3_COL_OUTPUT_LIMBS: ColIndex = BLAKE3_COL_INPUT_LIMBS + INPUT_LIMBS;
pub const BLAKE3_COL_P3_START: ColIndex = BLAKE3_COL_OUTPUT_LIMBS + OUTPUT_LIMBS;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Blake3Precompile<const BUS: bool>;

impl<const BUS: bool> TableT for Blake3Precompile<BUS> {
    fn name(&self) -> &'static str {
        "blake3"
    }

    fn table(&self) -> Table {
        Table::blake3()
    }

    fn n_columns_total(&self) -> usize {
        num_cols_blake3()
    }

    fn bus_interactions(&self) -> Vec<BusInteraction> {
        let mut buses = vec![BusInteraction {
            direction: BusDirection::Pull,
            multiplicity: BusMultiplicity::Column(BLAKE3_COL_MULTIPLICITY),
            domainsep: BusData::Constant(BLAKE3_DOMAINSEP),
            data: vec![
                BusData::Column(BLAKE3_COL_NU_A),
                BusData::Column(BLAKE3_COL_NU_B),
                BusData::Column(BLAKE3_COL_NU_C),
            ],
        }];
        buses.extend(memory_lookups_consecutive(
            BLAKE3_COL_NU_A,
            BLAKE3_COL_INPUT_LIMBS,
            INPUT_LIMBS / 2,
        ));
        buses.extend(memory_lookups_consecutive(
            BLAKE3_COL_NU_B,
            BLAKE3_COL_INPUT_LIMBS + INPUT_LIMBS / 2,
            INPUT_LIMBS / 2,
        ));
        buses.extend(memory_lookups_consecutive(
            BLAKE3_COL_NU_C,
            BLAKE3_COL_OUTPUT_LIMBS,
            OUTPUT_LIMBS,
        ));
        buses
    }

    fn padding_row(&self, zero_vec_ptr: usize, _null_hash_ptr: usize, _ending_pc: usize) -> Vec<F> {
        let mut row = vec![F::ZERO; num_cols_blake3()];
        row[BLAKE3_COL_NU_A] = F::from_usize(zero_vec_ptr);
        row[BLAKE3_COL_NU_B] = F::from_usize(zero_vec_ptr);
        row[BLAKE3_COL_NU_C] = F::from_usize(zero_vec_ptr);
        row
    }

    #[inline(always)]
    fn execute<M: MemoryAccess>(
        &self,
        arg_a: F,
        arg_b: F,
        arg_c: F,
        args: PrecompileCompTimeArgs<usize>,
        ctx: &mut InstructionContext<'_, M>,
    ) -> Result<(), RunnerError> {
        let PrecompileCompTimeArgs::Blake3Hash64 = args else {
            unreachable!("Blake3 table called with non-Blake3 args");
        };

        let mut input_limbs = [F::ZERO; INPUT_LIMBS];
        ctx.memory
            .get_slice_into(arg_a.to_usize(), &mut input_limbs[..INPUT_LIMBS / 2])?;
        ctx.memory
            .get_slice_into(arg_b.to_usize(), &mut input_limbs[INPUT_LIMBS / 2..])?;

        let mut words = [0u32; INPUT_WORDS];
        for (word, limbs) in words.iter_mut().zip(input_limbs.chunks_exact(2)) {
            *word = limbs[0].as_canonical_u32() | (limbs[1].as_canonical_u32() << 16);
        }
        let output_limbs = blake3_hash_64_u16(words);
        let output_fields = output_limbs.map(F::from_u16);
        ctx.memory.set_slice(arg_c.to_usize(), &output_fields)?;

        let trace = ctx.traces.get_mut(&self.table()).unwrap();
        trace.columns[BLAKE3_COL_MULTIPLICITY].push(F::ONE);
        trace.columns[BLAKE3_COL_NU_A].push(arg_a);
        trace.columns[BLAKE3_COL_NU_B].push(arg_b);
        trace.columns[BLAKE3_COL_NU_C].push(arg_c);
        for (i, value) in input_limbs.iter().enumerate() {
            trace.columns[BLAKE3_COL_INPUT_LIMBS + i].push(*value);
        }
        for (i, value) in output_fields.iter().enumerate() {
            trace.columns[BLAKE3_COL_OUTPUT_LIMBS + i].push(*value);
        }
        for i in BLAKE3_COL_P3_START..num_cols_blake3() {
            trace.columns[i].push(F::ZERO);
        }
        Ok(())
    }
}

impl<const BUS: bool> Air for Blake3Precompile<BUS> {
    type ExtraData = ExtraDataForBuses<EF>;

    fn degree_air(&self) -> usize {
        // The BLAKE3 AIR gates its constraints by multiplicity so padding rows do not need a
        // BLAKE3-specific null-hash memory row. This keeps padding simple but raises the degree by
        // one compared with Poseidon-style valid padding rows.
        4
    }

    fn n_columns(&self) -> usize {
        num_cols_blake3()
    }

    fn n_constraints(&self) -> usize {
        2 * BUS as usize
            + 1 // multiplicity is boolean
            + INPUT_CONSTRAINTS
            + FULL_ROUNDS * ROUND_CONSTRAINTS
            + FINAL_OUTPUT_CONSTRAINTS
            + OUTPUT_CONSTRAINTS
    }

    fn n_shift_columns(&self) -> usize {
        0
    }

    fn eval<AB: AirBuilder>(&self, builder: &mut AB, extra_data: &Self::ExtraData) {
        let (multiplicity, nu_a, nu_b, nu_c, input_limbs, output_limbs, cols_ptr) = {
            let flat = builder.flat();
            let input_limbs: [AB::IF; INPUT_LIMBS] = flat[BLAKE3_COL_INPUT_LIMBS..BLAKE3_COL_INPUT_LIMBS + INPUT_LIMBS]
                .try_into()
                .unwrap();
            let output_limbs: [AB::IF; OUTPUT_LIMBS] = flat
                [BLAKE3_COL_OUTPUT_LIMBS..BLAKE3_COL_OUTPUT_LIMBS + OUTPUT_LIMBS]
                .try_into()
                .unwrap();
            let cols: *const Blake3Cols<AB::IF> = {
                let local = &flat[BLAKE3_COL_P3_START..];
                let (prefix, shorts, suffix) = unsafe { local.align_to::<Blake3Cols<AB::IF>>() };
                debug_assert!(prefix.is_empty(), "Alignment should match");
                debug_assert!(suffix.is_empty(), "Alignment should match");
                debug_assert_eq!(shorts.len(), 1);
                shorts.as_ptr()
            };
            (
                flat[BLAKE3_COL_MULTIPLICITY],
                flat[BLAKE3_COL_NU_A],
                flat[BLAKE3_COL_NU_B],
                flat[BLAKE3_COL_NU_C],
                input_limbs,
                output_limbs,
                cols,
            )
        };

        if BUS {
            eval_bus_virtual::<AB, EF>(
                builder,
                extra_data,
                multiplicity,
                AB::IF::from_usize(BLAKE3_DOMAINSEP),
                &[nu_a, nu_b, nu_c],
            );
        } else {
            builder.declare_values(&[multiplicity, nu_a, nu_b, nu_c]);
        }

        builder.assert_bool(multiplicity);

        let cols = unsafe { &*cols_ptr };

        for word in 0..INPUT_WORDS {
            for bit in cols.inputs[word] {
                assert_zero_gated(builder, multiplicity, bit.bool_check());
            }
            let lo = pack_bits_le(cols.inputs[word][..BITS_PER_LIMB].iter().copied());
            let hi = pack_bits_le(cols.inputs[word][BITS_PER_LIMB..].iter().copied());
            assert_eq_gated(builder, multiplicity, input_limbs[2 * word], lo);
            assert_eq_gated(builder, multiplicity, input_limbs[2 * word + 1], hi);
        }

        eval_blake3(builder, multiplicity, cols);

        for word in 0..OUTPUT_WORDS {
            let bits = if word < 4 {
                cols.outputs[0][word]
            } else {
                cols.outputs[1][word - 4]
            };
            let lo = pack_bits_le(bits[..BITS_PER_LIMB].iter().copied());
            let hi = pack_bits_le(bits[BITS_PER_LIMB..].iter().copied());
            assert_eq_gated(builder, multiplicity, output_limbs[2 * word], lo);
            assert_eq_gated(builder, multiplicity, output_limbs[2 * word + 1], hi);
        }
    }
}

#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct Blake3Cols<T> {
    pub inputs: [[T; 32]; INPUT_WORDS],
    pub full_rounds: [FullRound<T>; FULL_ROUNDS],
    pub final_round_helpers: [[T; 32]; 4],
    pub outputs: [[[T; 32]; 4]; 2],
}

#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct Blake3State<T> {
    pub row0: [[T; U32_LIMBS]; 4],
    pub row1: [[T; 32]; 4],
    pub row2: [[T; U32_LIMBS]; 4],
    pub row3: [[T; 32]; 4],
}

#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct FullRound<T> {
    pub state_prime: Blake3State<T>,
    pub state_middle: Blake3State<T>,
    pub state_middle_prime: Blake3State<T>,
    pub state_output: Blake3State<T>,
}

struct QuarterRound<'a, T> {
    a: &'a [T; U32_LIMBS],
    b: &'a [T; 32],
    c: &'a [T; U32_LIMBS],
    d: &'a [T; 32],
    m_two_i: &'a [T; U32_LIMBS],
    a_prime: &'a [T; U32_LIMBS],
    b_prime: &'a [T; 32],
    c_prime: &'a [T; U32_LIMBS],
    d_prime: &'a [T; 32],
    m_two_i_plus_one: &'a [T; U32_LIMBS],
    a_output: &'a [T; U32_LIMBS],
    b_output: &'a [T; 32],
    c_output: &'a [T; U32_LIMBS],
    d_output: &'a [T; 32],
}

pub const fn num_cols_blake3_core() -> usize {
    size_of::<Blake3Cols<u8>>()
}

pub const fn num_cols_blake3() -> usize {
    BLAKE3_COL_P3_START + num_cols_blake3_core()
}

fn eval_blake3<AB: AirBuilder>(builder: &mut AB, multiplicity: AB::IF, local: &Blake3Cols<AB::IF>) {
    let mut m_values = local.inputs.map(|bits| {
        [
            pack_bits_le(bits[..BITS_PER_LIMB].iter().copied()),
            pack_bits_le(bits[BITS_PER_LIMB..].iter().copied()),
        ]
    });

    let mut initial_state = Blake3State {
        row0: array::from_fn(|i| u32_limbs_if::<AB::IF>(IV[i])),
        row1: array::from_fn(|i| u32_bits_if::<AB::IF>(IV[4 + i])),
        row2: array::from_fn(|i| u32_limbs_if::<AB::IF>(IV[i])),
        row3: [
            u32_bits_if(0),
            u32_bits_if(0),
            u32_bits_if(BLOCK_LEN),
            u32_bits_if(FLAGS),
        ],
    };

    for round in 0..FULL_ROUNDS {
        verify_round(
            builder,
            multiplicity,
            &initial_state,
            &local.full_rounds[round],
            &m_values,
        );
        initial_state = local.full_rounds[round].state_output;
        permute(&mut m_values);
    }

    for i in 0..4 {
        let bits = local.final_round_helpers[i];
        for bit in bits {
            assert_zero_gated(builder, multiplicity, bit.bool_check());
        }
        let word = local.full_rounds[FULL_ROUNDS - 1].state_output.row2[i];
        assert_eq_gated(
            builder,
            multiplicity,
            pack_bits_le(bits[..BITS_PER_LIMB].iter().copied()),
            word[0],
        );
        assert_eq_gated(
            builder,
            multiplicity,
            pack_bits_le(bits[BITS_PER_LIMB..].iter().copied()),
            word[1],
        );
    }

    for i in 0..4 {
        let out_bits = local.outputs[0][i];
        for bit in out_bits {
            assert_zero_gated(builder, multiplicity, bit.bool_check());
        }
        xor_32_shift(
            builder,
            multiplicity,
            &local.full_rounds[FULL_ROUNDS - 1].state_output.row0[i],
            &out_bits,
            &local.final_round_helpers[i],
            0,
        );
    }

    for i in 0..4 {
        let out_bits = local.outputs[1][i];
        for j in 0..32 {
            assert_eq_gated(
                builder,
                multiplicity,
                out_bits[j],
                xor(
                    local.full_rounds[FULL_ROUNDS - 1].state_output.row1[i][j],
                    local.full_rounds[FULL_ROUNDS - 1].state_output.row3[i][j],
                ),
            );
        }
    }
}

fn verify_round<AB: AirBuilder>(
    builder: &mut AB,
    multiplicity: AB::IF,
    input: &Blake3State<AB::IF>,
    round_data: &FullRound<AB::IF>,
    m_vector: &[[AB::IF; 2]; INPUT_WORDS],
) {
    for i in 0..4 {
        quarter_round_function(
            builder,
            multiplicity,
            &QuarterRound {
                a: &input.row0[i],
                b: &input.row1[i],
                c: &input.row2[i],
                d: &input.row3[i],
                m_two_i: &m_vector[2 * i],
                a_prime: &round_data.state_prime.row0[i],
                b_prime: &round_data.state_prime.row1[i],
                c_prime: &round_data.state_prime.row2[i],
                d_prime: &round_data.state_prime.row3[i],
                m_two_i_plus_one: &m_vector[2 * i + 1],
                a_output: &round_data.state_middle.row0[i],
                b_output: &round_data.state_middle.row1[i],
                c_output: &round_data.state_middle.row2[i],
                d_output: &round_data.state_middle.row3[i],
            },
        );
    }

    for i in 0..4 {
        quarter_round_function(
            builder,
            multiplicity,
            &QuarterRound {
                a: &round_data.state_middle.row0[i],
                b: &round_data.state_middle.row1[(i + 1) % 4],
                c: &round_data.state_middle.row2[(i + 2) % 4],
                d: &round_data.state_middle.row3[(i + 3) % 4],
                m_two_i: &m_vector[8 + 2 * i],
                a_prime: &round_data.state_middle_prime.row0[i],
                b_prime: &round_data.state_middle_prime.row1[(i + 1) % 4],
                c_prime: &round_data.state_middle_prime.row2[(i + 2) % 4],
                d_prime: &round_data.state_middle_prime.row3[(i + 3) % 4],
                m_two_i_plus_one: &m_vector[9 + 2 * i],
                a_output: &round_data.state_output.row0[i],
                b_output: &round_data.state_output.row1[(i + 1) % 4],
                c_output: &round_data.state_output.row2[(i + 2) % 4],
                d_output: &round_data.state_output.row3[(i + 3) % 4],
            },
        );
    }
}

fn quarter_round_function<AB: AirBuilder>(builder: &mut AB, multiplicity: AB::IF, trace: &QuarterRound<'_, AB::IF>) {
    let b_0_16 = pack_bits_le(trace.b[..BITS_PER_LIMB].iter().copied());
    let b_16_32 = pack_bits_le(trace.b[BITS_PER_LIMB..].iter().copied());
    add3(
        builder,
        multiplicity,
        trace.a_prime,
        trace.a,
        &[b_0_16, b_16_32],
        trace.m_two_i,
    );

    xor_32_shift(builder, multiplicity, trace.a_prime, trace.d, trace.d_prime, 16);

    let d_prime_0_16 = pack_bits_le(trace.d_prime[..BITS_PER_LIMB].iter().copied());
    let d_prime_16_32 = pack_bits_le(trace.d_prime[BITS_PER_LIMB..].iter().copied());
    add2(
        builder,
        multiplicity,
        trace.c_prime,
        trace.c,
        &[d_prime_0_16, d_prime_16_32],
    );

    xor_32_shift(builder, multiplicity, trace.c_prime, trace.b, trace.b_prime, 12);

    let b_prime_0_16 = pack_bits_le(trace.b_prime[..BITS_PER_LIMB].iter().copied());
    let b_prime_16_32 = pack_bits_le(trace.b_prime[BITS_PER_LIMB..].iter().copied());
    add3(
        builder,
        multiplicity,
        trace.a_output,
        trace.a_prime,
        &[b_prime_0_16, b_prime_16_32],
        trace.m_two_i_plus_one,
    );

    xor_32_shift(builder, multiplicity, trace.a_output, trace.d_prime, trace.d_output, 8);

    let d_output_0_16 = pack_bits_le(trace.d_output[..BITS_PER_LIMB].iter().copied());
    let d_output_16_32 = pack_bits_le(trace.d_output[BITS_PER_LIMB..].iter().copied());
    add2(
        builder,
        multiplicity,
        trace.c_output,
        trace.c_prime,
        &[d_output_0_16, d_output_16_32],
    );

    xor_32_shift(builder, multiplicity, trace.c_output, trace.b_prime, trace.b_output, 7);
}

fn add3<AB: AirBuilder>(
    builder: &mut AB,
    multiplicity: AB::IF,
    a: &[AB::IF; 2],
    b: &[AB::IF; 2],
    c: &[AB::IF; 2],
    d: &[AB::IF; 2],
) {
    let two_16 = AB::IF::from_u32(1 << 16);
    let two_32 = two_16.square();
    let acc_16 = a[0] - b[0] - c[0] - d[0];
    let acc_32 = a[1] - b[1] - c[1] - d[1];
    let acc = acc_16 + two_16 * acc_32;
    assert_zero_gated(builder, multiplicity, acc * (acc + two_32) * (acc + two_32.double()));
    assert_zero_gated(
        builder,
        multiplicity,
        acc_16 * (acc_16 + two_16) * (acc_16 + two_16.double()),
    );
}

fn add2<AB: AirBuilder>(builder: &mut AB, multiplicity: AB::IF, a: &[AB::IF; 2], b: &[AB::IF; 2], c: &[AB::IF; 2]) {
    let two_16 = AB::IF::from_u32(1 << 16);
    let two_32 = two_16.square();
    let acc_16 = a[0] - b[0] - c[0];
    let acc_32 = a[1] - b[1] - c[1];
    let acc = acc_16 + two_16 * acc_32;
    assert_zero_gated(builder, multiplicity, acc * (acc + two_32));
    assert_zero_gated(builder, multiplicity, acc_16 * (acc_16 + two_16));
}

fn xor_32_shift<AB: AirBuilder>(
    builder: &mut AB,
    multiplicity: AB::IF,
    a: &[AB::IF; 2],
    b: &[AB::IF; 32],
    c: &[AB::IF; 32],
    shift: usize,
) {
    for bit in c {
        assert_zero_gated(builder, multiplicity, bit.bool_check());
    }

    let shifted: [AB::IF; 32] = array::from_fn(|i| c[(i + 32 - shift) % 32]);
    let xored: [AB::IF; 32] = array::from_fn(|i| xor(b[i], shifted[i]));
    assert_eq_gated(
        builder,
        multiplicity,
        a[0],
        pack_bits_le(xored[..BITS_PER_LIMB].iter().copied()),
    );
    assert_eq_gated(
        builder,
        multiplicity,
        a[1],
        pack_bits_le(xored[BITS_PER_LIMB..].iter().copied()),
    );
}

fn pack_bits_le<R: PrimeCharacteristicRing>(bits: impl DoubleEndedIterator<Item = R>) -> R {
    let mut output = R::ZERO;
    for bit in bits.rev() {
        output = output.double() + bit;
    }
    output
}

fn xor<R: PrimeCharacteristicRing>(x: R, y: R) -> R {
    x + y - x * y.double()
}

fn assert_eq_gated<AB: AirBuilder>(builder: &mut AB, multiplicity: AB::IF, x: AB::IF, y: AB::IF) {
    assert_zero_gated(builder, multiplicity, x - y);
}

fn assert_zero_gated<AB: AirBuilder>(builder: &mut AB, multiplicity: AB::IF, x: AB::IF) {
    builder.assert_zero(multiplicity * x);
}

fn u32_limbs_if<R: PrimeCharacteristicRing>(value: u32) -> [R; 2] {
    [R::from_u16(value as u16), R::from_u16((value >> 16) as u16)]
}

fn u32_bits_if<R: PrimeCharacteristicRing>(value: u32) -> [R; 32] {
    array::from_fn(|i| R::from_bool(((value >> i) & 1) == 1))
}

pub fn permute<T: Copy>(m: &mut [T; 16]) {
    let old = *m;
    for i in 0..16 {
        m[i] = old[MSG_PERMUTATION[i]];
    }
}
