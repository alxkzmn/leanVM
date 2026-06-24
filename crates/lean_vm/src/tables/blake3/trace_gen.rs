use crate::{
    F,
    tables::blake3::{
        BLAKE3_COL_INPUT_LIMBS, BLAKE3_COL_OUTPUT_LIMBS, BLAKE3_COL_P3_START, BLOCK_LEN, Blake3Cols, Blake3State,
        FLAGS, FullRound, INPUT_LIMBS, INPUT_WORDS, IV, OUTPUT_LIMBS, OUTPUT_WORDS, permute,
    },
};
use backend::*;
use std::array;
use tracing::instrument;

#[instrument(name = "generate Blake3 AIR trace", skip_all)]
pub fn fill_trace_blake3(trace: &mut [ArenaVec<F>]) {
    let n = trace.iter().map(|col| col.len()).max().unwrap();
    for col in trace.iter_mut() {
        if col.len() != n {
            col.resize(n, F::ZERO);
        }
    }

    for row_idx in 0..n {
        let mut input_limbs = [F::ZERO; INPUT_LIMBS];
        for (i, limb) in input_limbs.iter_mut().enumerate() {
            *limb = trace[BLAKE3_COL_INPUT_LIMBS + i][row_idx];
        }
        let mut input_words = [0u32; INPUT_WORDS];
        for (word, limbs) in input_words.iter_mut().zip(input_limbs.chunks_exact(2)) {
            *word = limbs[0].as_canonical_u32() | (limbs[1].as_canonical_u32() << 16);
        }

        let ptrs: Vec<*mut F> = (BLAKE3_COL_P3_START..super::num_cols_blake3())
            .map(|c| unsafe { trace[c].as_mut_ptr().add(row_idx) })
            .collect();
        let cols: &mut Blake3Cols<&mut F> = unsafe { &mut *(ptrs.as_ptr() as *mut Blake3Cols<&mut F>) };
        generate_trace_rows_for_hash(cols, input_words);

        let output = blake3_hash_64_u16(input_words);
        for i in 0..OUTPUT_LIMBS {
            trace[BLAKE3_COL_OUTPUT_LIMBS + i][row_idx] = F::from_u16(output[i]);
        }
    }
}

pub fn blake3_hash_64_u16(input_words: [u32; INPUT_WORDS]) -> [u16; OUTPUT_LIMBS] {
    let output_words = blake3_hash_64_words(input_words);
    let mut limbs = [0u16; OUTPUT_LIMBS];
    for (word, out) in output_words.iter().zip(limbs.chunks_exact_mut(2)) {
        out[0] = *word as u16;
        out[1] = (word >> 16) as u16;
    }
    limbs
}

fn blake3_hash_64_words(input_words: [u32; INPUT_WORDS]) -> [u32; OUTPUT_WORDS] {
    compress(input_words)
}

pub fn generate_trace_rows_for_hash<F: PrimeCharacteristicRing>(
    row: &mut Blake3Cols<&mut F>,
    input: [u32; INPUT_WORDS],
) {
    for (dst, word) in row.inputs.iter_mut().zip(input) {
        write_bits(dst, u32_to_bits_le(word));
    }

    let mut m_vec = input;
    let mut state = initial_state();

    for round in 0..7 {
        generate_trace_row_for_round(&mut row.full_rounds[round], &mut state, &m_vec);
        permute(&mut m_vec);
    }

    let output = first_output_words(&state);
    for i in 0..4 {
        write_bits(&mut row.final_round_helpers[i], u32_to_bits_le(state[2][i]));
        write_bits(&mut row.outputs[0][i], u32_to_bits_le(output[i]));
        write_bits(&mut row.outputs[1][i], u32_to_bits_le(output[4 + i]));
    }
}

fn compress(input: [u32; INPUT_WORDS]) -> [u32; OUTPUT_WORDS] {
    let mut m_vec = input;
    let mut state = initial_state();

    for _ in 0..7 {
        round(&mut state, &m_vec);
        permute(&mut m_vec);
    }

    first_output_words(&state)
}

fn initial_state() -> [[u32; 4]; 4] {
    [
        [IV[0], IV[1], IV[2], IV[3]],
        [IV[4], IV[5], IV[6], IV[7]],
        [IV[0], IV[1], IV[2], IV[3]],
        [0, 0, BLOCK_LEN, FLAGS],
    ]
}

fn first_output_words(state: &[[u32; 4]; 4]) -> [u32; OUTPUT_WORDS] {
    [
        state[0][0] ^ state[2][0],
        state[0][1] ^ state[2][1],
        state[0][2] ^ state[2][2],
        state[0][3] ^ state[2][3],
        state[1][0] ^ state[3][0],
        state[1][1] ^ state[3][1],
        state[1][2] ^ state[3][2],
        state[1][3] ^ state[3][3],
    ]
}

fn generate_trace_row_for_round<F: PrimeCharacteristicRing>(
    round_data: &mut FullRound<&mut F>,
    state: &mut [[u32; 4]; 4],
    m_vec: &[u32; INPUT_WORDS],
) {
    for i in 0..4 {
        (state[0][i], state[1][i], state[2][i], state[3][i]) =
            verifiable_half_round(state[0][i], state[1][i], state[2][i], state[3][i], m_vec[2 * i], false);
    }
    save_state_to_trace(&mut round_data.state_prime, state);

    for i in 0..4 {
        (state[0][i], state[1][i], state[2][i], state[3][i]) = verifiable_half_round(
            state[0][i],
            state[1][i],
            state[2][i],
            state[3][i],
            m_vec[2 * i + 1],
            true,
        );
    }
    save_state_to_trace(&mut round_data.state_middle, state);

    for i in 0..4 {
        (
            state[0][i],
            state[1][(i + 1) % 4],
            state[2][(i + 2) % 4],
            state[3][(i + 3) % 4],
        ) = verifiable_half_round(
            state[0][i],
            state[1][(i + 1) % 4],
            state[2][(i + 2) % 4],
            state[3][(i + 3) % 4],
            m_vec[8 + 2 * i],
            false,
        );
    }
    save_state_to_trace(&mut round_data.state_middle_prime, state);

    for i in 0..4 {
        (
            state[0][i],
            state[1][(i + 1) % 4],
            state[2][(i + 2) % 4],
            state[3][(i + 3) % 4],
        ) = verifiable_half_round(
            state[0][i],
            state[1][(i + 1) % 4],
            state[2][(i + 2) % 4],
            state[3][(i + 3) % 4],
            m_vec[9 + 2 * i],
            true,
        );
    }
    save_state_to_trace(&mut round_data.state_output, state);
}

fn round(state: &mut [[u32; 4]; 4], m_vec: &[u32; INPUT_WORDS]) {
    for i in 0..4 {
        (state[0][i], state[1][i], state[2][i], state[3][i]) =
            verifiable_half_round(state[0][i], state[1][i], state[2][i], state[3][i], m_vec[2 * i], false);
        (state[0][i], state[1][i], state[2][i], state[3][i]) = verifiable_half_round(
            state[0][i],
            state[1][i],
            state[2][i],
            state[3][i],
            m_vec[2 * i + 1],
            true,
        );
    }

    for i in 0..4 {
        (
            state[0][i],
            state[1][(i + 1) % 4],
            state[2][(i + 2) % 4],
            state[3][(i + 3) % 4],
        ) = verifiable_half_round(
            state[0][i],
            state[1][(i + 1) % 4],
            state[2][(i + 2) % 4],
            state[3][(i + 3) % 4],
            m_vec[8 + 2 * i],
            false,
        );
        (
            state[0][i],
            state[1][(i + 1) % 4],
            state[2][(i + 2) % 4],
            state[3][(i + 3) % 4],
        ) = verifiable_half_round(
            state[0][i],
            state[1][(i + 1) % 4],
            state[2][(i + 2) % 4],
            state[3][(i + 3) % 4],
            m_vec[9 + 2 * i],
            true,
        );
    }
}

fn verifiable_half_round(mut a: u32, mut b: u32, mut c: u32, mut d: u32, m: u32, flag: bool) -> (u32, u32, u32, u32) {
    let (rot_1, rot_2) = if flag { (8, 7) } else { (16, 12) };
    a = a.wrapping_add(b).wrapping_add(m);
    d = (d ^ a).rotate_right(rot_1);
    c = c.wrapping_add(d);
    b = (b ^ c).rotate_right(rot_2);
    (a, b, c, d)
}

fn save_state_to_trace<F: PrimeCharacteristicRing>(trace: &mut Blake3State<&mut F>, state: &[[u32; 4]; 4]) {
    for i in 0..4 {
        write_limbs(&mut trace.row0[i], u32_to_limbs(state[0][i]));
        write_bits(&mut trace.row1[i], u32_to_bits_le(state[1][i]));
        write_limbs(&mut trace.row2[i], u32_to_limbs(state[2][i]));
        write_bits(&mut trace.row3[i], u32_to_bits_le(state[3][i]));
    }
}

fn write_limbs<F: PrimeCharacteristicRing>(dst: &mut [&mut F; 2], values: [F; 2]) {
    for (slot, value) in dst.iter_mut().zip(values) {
        **slot = value;
    }
}

fn write_bits<F: PrimeCharacteristicRing>(dst: &mut [&mut F; 32], values: [F; 32]) {
    for (slot, value) in dst.iter_mut().zip(values) {
        **slot = value;
    }
}

fn u32_to_limbs<F: PrimeCharacteristicRing>(value: u32) -> [F; 2] {
    [F::from_u16(value as u16), F::from_u16((value >> 16) as u16)]
}

fn u32_to_bits_le<F: PrimeCharacteristicRing>(value: u32) -> [F; 32] {
    array::from_fn(|i| F::from_bool(((value >> i) & 1) == 1))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn blake3_hash_64_matches_reference_crate() {
        let input_words = array::from_fn(|i| 0x1020_3040u32.wrapping_mul(i as u32 + 1));

        let mut input_bytes = [0u8; 64];
        for (word, bytes) in input_words.iter().zip(input_bytes.chunks_exact_mut(4)) {
            bytes.copy_from_slice(&word.to_le_bytes());
        }

        let output_limbs = blake3_hash_64_u16(input_words);
        let mut output_bytes = [0u8; 32];
        for (limb, bytes) in output_limbs.iter().zip(output_bytes.chunks_exact_mut(2)) {
            bytes.copy_from_slice(&limb.to_le_bytes());
        }

        assert_eq!(output_bytes, *blake3::hash(&input_bytes).as_bytes());
    }
}
