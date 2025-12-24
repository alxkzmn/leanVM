use core::mem::transmute;

use air::keccak_air::{KeccakAirOptimizedDown, KeccakCols, NUM_KECCAK_COLS, NUM_ROUNDS, U64_LIMBS};
use air_snark::{prove_single_air_with_whir, verify_single_air_with_whir, AirSnarkConfig};
use multilinear_toolkit::prelude::*;
use p3_field::PrimeField64;
use p3_koala_bear::{KoalaBear, QuinticExtensionFieldKB};
use rand::{rngs::StdRng, Rng, SeedableRng};
use utils::{build_challenger, FSVerifier};
use whir_p3::{precompute_dft_twiddles, FoldingFactor, SecurityAssumption, WhirConfigBuilder};

type F = KoalaBear;
type EF = QuinticExtensionFieldKB;

const UNIVARIATE_SKIPS: usize = 3;
const LOG_SMALLEST_DECOMPOSITION_CHUNK: usize = 12;

fn whir_config_builder() -> WhirConfigBuilder {
    WhirConfigBuilder {
        folding_factor: FoldingFactor::new(7, 4),
        soundness_type: SecurityAssumption::CapacityBound,
        pow_bits: 16,
        max_num_variables_to_send_coeffs: 6,
        rs_domain_initial_reduction_factor: 5,
        security_level: 128,
        starting_log_inv_rate: 1,
    }
}

fn u64_to_bits_le<Ff: PrimeField64>(x: u64) -> [Ff; 64] {
    core::array::from_fn(|i| Ff::from_bool(((x >> i) & 1) == 1))
}

fn u64_to_16_bit_limbs<Ff: PrimeField64>(x: u64) -> [Ff; U64_LIMBS] {
    core::array::from_fn(|i| {
        let limb = ((x >> (16 * i)) & 0xFFFF) as u16;
        Ff::from_u16(limb)
    })
}

fn generate_trace_rows_for_perm<Ff: PrimeField64>(rows: &mut [KeccakCols<Ff>], input: [u64; 25]) {
    let mut current_state: [[u64; 5]; 5] = unsafe { transmute(input) };

    let initial_state: [[[Ff; U64_LIMBS]; 5]; 5] =
        core::array::from_fn(|y| core::array::from_fn(|x| u64_to_16_bit_limbs(current_state[x][y])));

    rows[0].a = initial_state;
    rows[0].preimage = initial_state;

    generate_trace_row_for_round(&mut rows[0], 0, &mut current_state);

    for round in 1..rows.len() {
        rows[round].preimage = initial_state;

        for y in 0..5 {
            for x in 0..5 {
                for limb in 0..U64_LIMBS {
                    rows[round].a[y][x][limb] = rows[round - 1].a_prime_prime_prime(y, x, limb);
                }
            }
        }

        generate_trace_row_for_round(&mut rows[round], round, &mut current_state);
    }
}

fn generate_trace_row_for_round<Ff: PrimeField64>(
    row: &mut KeccakCols<Ff>,
    round: usize,
    current_state: &mut [[u64; 5]; 5],
) {
    use air::keccak_air::{R, RC};

    row.step_flags[round] = Ff::ONE;

    let state_c: [u64; 5] = current_state.map(|row| row.iter().fold(0, |acc, y| acc ^ y));
    for (x, elem) in state_c.iter().enumerate() {
        row.c[x] = u64_to_bits_le(*elem);
    }

    let state_c_prime: [u64; 5] =
        core::array::from_fn(|x| state_c[x] ^ state_c[(x + 4) % 5] ^ state_c[(x + 1) % 5].rotate_left(1));
    for (x, elem) in state_c_prime.iter().enumerate() {
        row.c_prime[x] = u64_to_bits_le(*elem);
    }

    *current_state =
        core::array::from_fn(|i| core::array::from_fn(|j| current_state[i][j] ^ state_c[i] ^ state_c_prime[i]));
    for (x, x_row) in current_state.iter().enumerate() {
        for (y, elem) in x_row.iter().enumerate() {
            row.a_prime[y][x] = u64_to_bits_le(*elem);
        }
    }

    *current_state = core::array::from_fn(|i| {
        core::array::from_fn(|j| {
            let new_i = (i + 3 * j) % 5;
            let new_j = i;
            current_state[new_i][new_j].rotate_left(R[new_i][new_j] as u32)
        })
    });

    *current_state = core::array::from_fn(|i| {
        core::array::from_fn(|j| {
            current_state[i][j] ^ ((!current_state[(i + 1) % 5][j]) & current_state[(i + 2) % 5][j])
        })
    });
    for (x, x_row) in current_state.iter().enumerate() {
        for (y, elem) in x_row.iter().enumerate() {
            row.a_prime_prime[y][x] = u64_to_16_bit_limbs(*elem);
        }
    }

    row.a_prime_prime_0_0_bits = u64_to_bits_le(current_state[0][0]);
    current_state[0][0] ^= RC[round];
    row.a_prime_prime_prime_0_0_limbs = u64_to_16_bit_limbs(current_state[0][0]);
}

fn transpose_row_major_to_columns<Ff: Copy>(row_major: &[Ff], n_rows: usize, n_cols: usize) -> Vec<Vec<Ff>> {
    assert_eq!(row_major.len(), n_rows * n_cols);
    let mut cols = vec![vec![row_major[0]; n_rows]; n_cols];
    for r in 0..n_rows {
        for c in 0..n_cols {
            cols[c][r] = row_major[r * n_cols + c];
        }
    }
    cols
}

fn generate_trace<Ff: PrimeField64>(n_rows_plus_one: usize) -> Vec<Ff> {
    let num_perms = n_rows_plus_one.div_ceil(NUM_ROUNDS);
    let mut rng = StdRng::seed_from_u64(1);
    let inputs: Vec<[u64; 25]> = (0..num_perms)
        .map(|_| {
            let mut a = [0u64; 25];
            for i in 0..25 {
                a[i] = rng.random();
            }
            a
        })
        .collect();

    let total_rows = num_perms * NUM_ROUNDS;
    let mut trace = vec![Ff::ZERO; total_rows * NUM_KECCAK_COLS];
    let (prefix, rows, suffix) = unsafe { trace.align_to_mut::<KeccakCols<Ff>>() };
    assert!(prefix.is_empty());
    assert!(suffix.is_empty());
    assert_eq!(rows.len(), total_rows);

    for (p, input) in inputs.into_iter().enumerate() {
        let start = p * NUM_ROUNDS;
        let end = start + NUM_ROUNDS;
        generate_trace_rows_for_perm(&mut rows[start..end], input);
        rows[end - 1].export = Ff::ONE;
    }

    trace.truncate(n_rows_plus_one * NUM_KECCAK_COLS);
    trace
}

#[test]
fn test_keccak_air_snark_with_whir() {
    // Not required, but avoids first-run DFT setup dominating.
    precompute_dft_twiddles::<F>(1 << 24);

    let log_n_rows = 10;
    let n_rows = 1usize << log_n_rows;
    let n_rows_plus_one = n_rows + 1;

    let trace_rm: Vec<F> = generate_trace::<F>(n_rows_plus_one);
    let columns_plus_one = transpose_row_major_to_columns(&trace_rm, n_rows_plus_one, NUM_KECCAK_COLS);
    let columns_ref_f = columns_plus_one.iter().map(|c| &c[..n_rows]).collect::<Vec<_>>();

    let air = KeccakAirOptimizedDown::<EF>::new();
    let down_idxs = KeccakAirOptimizedDown::<EF>::down_indices();
    let last_row_shifted_f = down_idxs
        .iter()
        .map(|&col| columns_plus_one[col][n_rows])
        .collect::<Vec<_>>();

    let config = AirSnarkConfig {
        univariate_skips: UNIVARIATE_SKIPS,
        log_smallest_decomposition_chunk: LOG_SMALLEST_DECOMPOSITION_CHUNK,
        whir_config_builder: whir_config_builder(),
    };

    let prover_state = utils::build_prover_state::<EF>(false);
    let proof = prove_single_air_with_whir(
        prover_state,
        &air,
        vec![],
        &config,
        &columns_ref_f,
        &[] as &[&[EF]],
        &last_row_shifted_f,
        &[] as &[EF],
    );

    let mut verifier_state: FSVerifier<EF, _> = VerifierState::new(proof, build_challenger());
    verify_single_air_with_whir(&mut verifier_state, &air, vec![], &config).unwrap();
}


