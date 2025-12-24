use core::mem::transmute;

use air::keccak_air::{KeccakAir, KeccakAirOptimizedDown, KeccakCols, NUM_KECCAK_COLS, NUM_ROUNDS, U64_LIMBS};
use air::{check_air_validity, prove_air, verify_air};
use multilinear_toolkit::prelude::*;
use p3_field::PrimeField64;
use p3_koala_bear::{KoalaBear, QuinticExtensionFieldKB};
use rand::{Rng, SeedableRng, rngs::StdRng};
use std::time::Instant;
use utils::{build_prover_state, build_verifier_state};

const UNIVARIATE_SKIPS: usize = 3;

type F = KoalaBear;
type EF = QuinticExtensionFieldKB;

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

    // Populate the round input for the first round.
    rows[0].a = initial_state;
    rows[0].preimage = initial_state;

    generate_trace_row_for_round(&mut rows[0], 0, &mut current_state);

    for round in 1..rows.len() {
        rows[round].preimage = initial_state;

        // Copy previous row's output to next row's input.
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

    // Populate C[x] = xor(A[x, 0], ..., A[x, 4]).
    let state_c: [u64; 5] = current_state.map(|row| row.iter().fold(0, |acc, y| acc ^ y));
    for (x, elem) in state_c.iter().enumerate() {
        row.c[x] = u64_to_bits_le(*elem);
    }

    // Populate C'[x, z] = xor(C[x, z], C[x - 1, z], C[x + 1, z - 1]).
    let state_c_prime: [u64; 5] =
        core::array::from_fn(|x| state_c[x] ^ state_c[(x + 4) % 5] ^ state_c[(x + 1) % 5].rotate_left(1));
    for (x, elem) in state_c_prime.iter().enumerate() {
        row.c_prime[x] = u64_to_bits_le(*elem);
    }

    // Populate A'.
    *current_state =
        core::array::from_fn(|i| core::array::from_fn(|j| current_state[i][j] ^ state_c[i] ^ state_c_prime[i]));
    for (x, x_row) in current_state.iter().enumerate() {
        for (y, elem) in x_row.iter().enumerate() {
            row.a_prime[y][x] = u64_to_bits_le(*elem);
        }
    }

    // Rotate the current state to get the B array.
    *current_state = core::array::from_fn(|i| {
        core::array::from_fn(|j| {
            let new_i = (i + 3 * j) % 5;
            let new_j = i;
            current_state[new_i][new_j].rotate_left(R[new_i][new_j] as u32)
        })
    });

    // Populate A''.
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

    // A''[0,0] XOR RC.
    current_state[0][0] ^= RC[round];
    row.a_prime_prime_prime_0_0_limbs = u64_to_16_bit_limbs(current_state[0][0]);
}

fn generate_trace<Ff: PrimeField64>(n_rows_plus_one: usize) -> Vec<Ff> {
    // Generate enough full permutations to cover `n_rows_plus_one`, then truncate.
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
        // Set export=1 on final round for visibility (not required by constraints).
        rows[end - 1].export = Ff::ONE;
    }

    // Truncate to exactly `n_rows_plus_one` rows.
    trace.truncate(n_rows_plus_one * NUM_KECCAK_COLS);
    trace
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

#[test]
fn test_air_keccak_prove_verify() {
    let log_n_rows = 8;
    let n_rows = 1usize << log_n_rows;
    let n_rows_plus_one = n_rows + 1;

    let mut prover_state = build_prover_state::<EF>(false);

    // Build row-major trace for n_rows+1, then transpose to columns.
    let trace_rm: Vec<F> = generate_trace::<F>(n_rows_plus_one);
    let columns_plus_one = transpose_row_major_to_columns(&trace_rm, n_rows_plus_one, NUM_KECCAK_COLS);

    let columns_ref_f = columns_plus_one.iter().map(|c| &c[..n_rows]).collect::<Vec<_>>();
    let columns_ref_ef: Vec<&[EF]> = vec![];
    let last_row_shifted_f = (0..NUM_KECCAK_COLS)
        .map(|col| columns_plus_one[col][n_rows])
        .collect::<Vec<_>>();
    let last_row_shifted_ef: Vec<EF> = vec![];

    let air = KeccakAir::<EF>::new();
    check_air_validity::<_, EF>(
        &air,
        &vec![],
        &columns_ref_f,
        &columns_ref_ef,
        &last_row_shifted_f,
        &last_row_shifted_ef,
    )
    .unwrap();

    let (point_p, evals_f_p, evals_ef_p) = prove_air(
        &mut prover_state,
        &air,
        vec![],
        UNIVARIATE_SKIPS,
        &columns_ref_f,
        &columns_ref_ef,
        &last_row_shifted_f,
        &last_row_shifted_ef,
        None,
        true,
    );

    let mut verifier_state = build_verifier_state(prover_state);
    let (point_v, evals_f_v, evals_ef_v) = verify_air(
        &mut verifier_state,
        &air,
        vec![],
        UNIVARIATE_SKIPS,
        log_n_rows,
        &last_row_shifted_f,
        &last_row_shifted_ef,
        None,
    )
    .unwrap();

    assert_eq!(point_p, point_v);
    assert_eq!(evals_f_p, evals_f_v);
    assert_eq!(evals_ef_p, evals_ef_v);

    // Spot check: opened evaluations match actual column evals at the returned point.
    assert_eq!(columns_ref_f[0].evaluate(&point_p), evals_f_v[0]);
}

#[test]
fn test_air_keccak_prove_verify_optimized_down() {
    let log_n_rows = 8;
    let n_rows = 1usize << log_n_rows;
    let n_rows_plus_one = n_rows + 1;

    let mut prover_state = build_prover_state::<EF>(false);

    let trace_rm: Vec<F> = generate_trace::<F>(n_rows_plus_one);
    let columns_plus_one = transpose_row_major_to_columns(&trace_rm, n_rows_plus_one, NUM_KECCAK_COLS);
    let columns_ref_f = columns_plus_one.iter().map(|c| &c[..n_rows]).collect::<Vec<_>>();

    let columns_ref_ef: Vec<&[EF]> = vec![];
    let last_row_shifted_ef: Vec<EF> = vec![];

    let air = KeccakAirOptimizedDown::<EF>::new();
    let down_idxs = KeccakAirOptimizedDown::<EF>::down_indices();
    let last_row_shifted_f = down_idxs
        .iter()
        .map(|&col| columns_plus_one[col][n_rows])
        .collect::<Vec<_>>();

    check_air_validity::<_, EF>(
        &air,
        &vec![],
        &columns_ref_f,
        &columns_ref_ef,
        &last_row_shifted_f,
        &last_row_shifted_ef,
    )
    .unwrap();

    let (point_p, evals_f_p, evals_ef_p) = prove_air(
        &mut prover_state,
        &air,
        vec![],
        UNIVARIATE_SKIPS,
        &columns_ref_f,
        &columns_ref_ef,
        &last_row_shifted_f,
        &last_row_shifted_ef,
        None,
        true,
    );

    let mut verifier_state = build_verifier_state(prover_state);
    let (point_v, evals_f_v, evals_ef_v) = verify_air(
        &mut verifier_state,
        &air,
        vec![],
        UNIVARIATE_SKIPS,
        log_n_rows,
        &last_row_shifted_f,
        &last_row_shifted_ef,
        None,
    )
    .unwrap();

    assert_eq!(point_p, point_v);
    assert_eq!(evals_f_p, evals_f_v);
    assert_eq!(evals_ef_p, evals_ef_v);
}

/// Compare proving times between baseline (all columns shifted) and optimized-down variant.
///
/// Run with:
/// `cargo test -p air --test keccak_air --release -- --ignored --nocapture`
#[test]
#[ignore]
fn bench_compare_keccak_air_down_columns() {
    let log_n_rows = 12;
    let n_rows = 1usize << log_n_rows;
    let n_rows_plus_one = n_rows + 1;

    let trace_rm: Vec<F> = generate_trace::<F>(n_rows_plus_one);
    let columns_plus_one = transpose_row_major_to_columns(&trace_rm, n_rows_plus_one, NUM_KECCAK_COLS);
    let columns_ref_f = columns_plus_one.iter().map(|c| &c[..n_rows]).collect::<Vec<_>>();
    let columns_ref_ef: Vec<&[EF]> = vec![];
    let last_row_shifted_ef: Vec<EF> = vec![];

    // Baseline: all columns.
    let air_full = KeccakAir::<EF>::new();
    let last_row_full = (0..NUM_KECCAK_COLS)
        .map(|col| columns_plus_one[col][n_rows])
        .collect::<Vec<_>>();

    // Optimized: only required down columns.
    let air_opt = KeccakAirOptimizedDown::<EF>::new();
    let down_idxs = KeccakAirOptimizedDown::<EF>::down_indices();
    let last_row_opt = down_idxs
        .iter()
        .map(|&col| columns_plus_one[col][n_rows])
        .collect::<Vec<_>>();

    // Warm-up (avoid first-run effects from dominating).
    {
        let mut ps = build_prover_state::<EF>(false);
        let _ = prove_air(
            &mut ps,
            &air_opt,
            vec![],
            UNIVARIATE_SKIPS,
            &columns_ref_f,
            &columns_ref_ef,
            &last_row_opt,
            &last_row_shifted_ef,
            None,
            false,
        );
    }

    let mut ps_full = build_prover_state::<EF>(false);
    let t0 = Instant::now();
    let _ = prove_air(
        &mut ps_full,
        &air_full,
        vec![],
        UNIVARIATE_SKIPS,
        &columns_ref_f,
        &columns_ref_ef,
        &last_row_full,
        &last_row_shifted_ef,
        None,
        false,
    );
    let dt_full = t0.elapsed();

    let mut ps_opt = build_prover_state::<EF>(false);
    let t1 = Instant::now();
    let _ = prove_air(
        &mut ps_opt,
        &air_opt,
        vec![],
        UNIVARIATE_SKIPS,
        &columns_ref_f,
        &columns_ref_ef,
        &last_row_opt,
        &last_row_shifted_ef,
        None,
        false,
    );
    let dt_opt = t1.elapsed();

    println!("Keccak prove time (full down cols):   {:?}", dt_full);
    println!("Keccak prove time (optimized down):  {:?}", dt_opt);
    if dt_opt.as_nanos() > 0 {
        println!("Speedup: {:.2}x", (dt_full.as_secs_f64() / dt_opt.as_secs_f64()));
    }
}
