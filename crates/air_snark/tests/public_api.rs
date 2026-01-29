use air_snark::{AirSnarkConfig, prove_single_air_with_whir_base, verify_single_air_with_whir_base};
use multilinear_toolkit::prelude::*;
use p3_air::{Air, AirBuilder};
use p3_koala_bear::{KoalaBear, QuinticExtensionFieldKB};
use whir_p3::{precompute_dft_twiddles, FoldingFactor, SecurityAssumption, WhirConfigBuilder};

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

/// A tiny AIR used to ensure `air_snark`'s public API stays usable.
#[derive(Debug, Clone, Copy)]
struct Add1Air;

impl Air for Add1Air {
    type ExtraData = Vec<EF>;

    fn n_columns_f_air(&self) -> usize {
        1
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
        let up = builder.up_f()[0].clone();
        let down = builder.down_f()[0].clone();
        builder.assert_eq(down, up + AB::F::ONE);
    }
}

#[test]
fn test_public_api_smoke() {
    // Optional, but makes the test faster on first run.
    precompute_dft_twiddles::<F>(1 << 20);

    let log_n_rows = 8;
    let n_rows = 1usize << log_n_rows;

    // Trace col: 0,1,2,... (mod p)
    let col_plus_one: Vec<F> = (0..=n_rows).map(F::from_usize).collect();
    let columns_f: Vec<&[F]> = vec![&col_plus_one[..n_rows]];
    let last_row_shifted_f: Vec<F> = vec![col_plus_one[n_rows]];

    let air = Add1Air;
    let config = AirSnarkConfig {
        univariate_skips: 3,
        log_smallest_decomposition_chunk: 12,
        whir_config_builder: whir_config_builder(),
    };

    let prover_state = air_snark::build_prover_state::<EF>(false);
    let proof = prove_single_air_with_whir_base(
        prover_state,
        &air,
        vec![],
        &config,
        &columns_f,
        &last_row_shifted_f,
    );

    let mut verifier_state = VerifierState::new(proof, air_snark::build_challenger());
    verify_single_air_with_whir_base(&mut verifier_state, &air, vec![], &config).unwrap();
}

