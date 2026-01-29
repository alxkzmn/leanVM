use air_snark::{
    AirSnarkConfig, AirSnarkTraceLayout, prove_single_air_with_whir_base, verify_single_air_with_whir_base,
};
use multilinear_toolkit::prelude::*;
use p3_air::{Air, AirBuilder};
use p3_koala_bear::{KoalaBear, QuinticExtensionFieldKB};
use sub_protocols::ColDims;
use whir_p3::{FoldingFactor, SecurityAssumption, WhirConfigBuilder, precompute_dft_twiddles};

type F = KoalaBear;
type EF = QuinticExtensionFieldKB;

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

/// Demonstrates lean-style public-prefix columns:
/// column 1 has a public prefix and a committed suffix.
#[derive(Debug, Clone, Copy)]
struct PrefixAir;

impl Air for PrefixAir {
    type ExtraData = Vec<EF>;

    fn n_columns_f_air(&self) -> usize {
        2
    }
    fn n_columns_ef_air(&self) -> usize {
        0
    }
    fn degree(&self) -> usize {
        1
    }
    fn n_constraints(&self) -> usize {
        1
    }
    fn down_column_indexes_f(&self) -> Vec<usize> {
        vec![0]
    }
    fn down_column_indexes_ef(&self) -> Vec<usize> {
        vec![]
    }

    fn eval<AB: AirBuilder>(&self, builder: &mut AB, _: &Self::ExtraData) {
        // col0 transitions: x_{r+1} = x_r + 1
        let x_up = builder.up_f()[0].clone();
        let x_down = builder.down_f()[0].clone();
        builder.assert_eq(x_down, x_up + AB::F::ONE);
        // col1 is intentionally unconstrained; it exists only to exercise public-prefix commitments.
    }
}

#[test]
fn test_air_snark_with_public_prefix_column() {
    precompute_dft_twiddles::<F>(1 << 20);

    let log_n_rows = 8;
    let n_rows = 1usize << log_n_rows;

    // Column 0: 0..N (plus one extra for last_row_shifted)
    let col0_plus_one: Vec<F> = (0..=n_rows).map(F::from_usize).collect();
    let col0: &[F] = &col0_plus_one[..n_rows];

    // Column 1: prefix is public, suffix committed.
    let log_public = 4; // 16 public rows
    let public_len = 1usize << log_public;
    let mut col1 = vec![F::ZERO; n_rows];
    for i in 0..n_rows {
        col1[i] = F::from_usize(1000 + i);
    }
    let col1_public = col1[..public_len].to_vec();

    let columns_f: Vec<&[F]> = vec![col0, &col1];
    let last_row_shifted_f: Vec<F> = vec![col0_plus_one[n_rows]];

    let air = PrefixAir;
    let config = AirSnarkConfig {
        univariate_skips: 3,
        // Must be <= any public-prefix size (packed_pcs requires log_public >= log_smallest_decomposition_chunk).
        log_smallest_decomposition_chunk: 4,
        security_bits: 128,
        whir_config_builder: whir_config_builder(),
    };

    // Layout:
    // - col0 fully committed
    // - col1 has public prefix of length 2^log_public, committed suffix of size (n_rows - public_len)
    let mut dims = vec![ColDims::full(log_n_rows); 2];
    dims[1] = ColDims::padded_with_public_data(Some(log_public), n_rows - public_len, F::ZERO);
    let mut layout = AirSnarkTraceLayout {
        dims_f: dims,
        public_data_f: Default::default(),
    };
    layout.insert_public_data(1, col1_public);

    let prover_state = air_snark::build_prover_state::<EF>(false);
    let proof = prove_single_air_with_whir_base(
        prover_state,
        &air,
        vec![],
        &config,
        &layout,
        &columns_f,
        &last_row_shifted_f,
    );

    let mut verifier_state = VerifierState::new(proof, air_snark::build_challenger());
    verify_single_air_with_whir_base(&mut verifier_state, &air, vec![], &config, &layout).unwrap();
}
