use air_snark::{AirSnarkConfig, AirSnarkPreprocessing};
use p3_air::{Air, AirBuilder};
use p3_koala_bear::{KoalaBear, QuinticExtensionFieldKB};
use whir_p3::{FoldingFactor, SecurityAssumption, WhirConfigBuilder};

type F = KoalaBear;
type EF = QuinticExtensionFieldKB;

#[derive(Debug, Clone, Copy)]
struct DummyAir;

impl Air for DummyAir {
    type ExtraData = Vec<EF>;

    fn degree(&self) -> usize {
        1
    }
    fn n_columns_f_air(&self) -> usize {
        3
    }
    fn n_columns_ef_air(&self) -> usize {
        0
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
        builder.assert_eq(builder.up_f()[0].clone(), builder.up_f()[0].clone());
    }
}

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

#[test]
fn test_preprocessing_roundtrip() {
    let cfg = AirSnarkConfig {
        univariate_skips: 3,
        log_smallest_decomposition_chunk: 12,
        security_bits: 128,
        whir_config_builder: whir_config_builder(),
    };

    let pre = AirSnarkPreprocessing::build_for_air_base::<F, _>(&DummyAir, 10, &cfg);
    let bytes = pre.to_bytes_bincode();
    let pre2 = AirSnarkPreprocessing::from_bytes_bincode(&bytes);
    assert_eq!(pre, pre2);

    // Should not panic.
    pre2.apply_precompute::<F>();

    // Should reconstruct a config.
    let _cfg2 = pre2.to_config();
}
