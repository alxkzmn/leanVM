use p3_air::Air;
use p3_field::TwoAdicField;
use serde::{Deserialize, Serialize};
use sub_protocols::{ColDims, MultilinearChunks};

use crate::AirSnarkConfig;

const PREPROC_VERSION: u32 = 1;

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
pub enum SecurityAssumptionSerde {
    UniqueDecoding,
    JohnsonBound,
    CapacityBound,
}

impl From<whir_p3::SecurityAssumption> for SecurityAssumptionSerde {
    fn from(v: whir_p3::SecurityAssumption) -> Self {
        match v {
            whir_p3::SecurityAssumption::UniqueDecoding => Self::UniqueDecoding,
            whir_p3::SecurityAssumption::JohnsonBound => Self::JohnsonBound,
            whir_p3::SecurityAssumption::CapacityBound => Self::CapacityBound,
        }
    }
}

impl From<SecurityAssumptionSerde> for whir_p3::SecurityAssumption {
    fn from(v: SecurityAssumptionSerde) -> Self {
        match v {
            SecurityAssumptionSerde::UniqueDecoding => whir_p3::SecurityAssumption::UniqueDecoding,
            SecurityAssumptionSerde::JohnsonBound => whir_p3::SecurityAssumption::JohnsonBound,
            SecurityAssumptionSerde::CapacityBound => whir_p3::SecurityAssumption::CapacityBound,
        }
    }
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
pub struct FoldingFactorSerde {
    pub first_round: usize,
    pub subsequent_round: usize,
}

impl From<whir_p3::FoldingFactor> for FoldingFactorSerde {
    fn from(v: whir_p3::FoldingFactor) -> Self {
        // FoldingFactor fields are private; mirror by probing with at_round(0/1).
        Self {
            first_round: v.at_round(0),
            subsequent_round: v.at_round(1),
        }
    }
}

impl From<FoldingFactorSerde> for whir_p3::FoldingFactor {
    fn from(v: FoldingFactorSerde) -> Self {
        whir_p3::FoldingFactor::new(v.first_round, v.subsequent_round)
    }
}

/// A serde-friendly version of `whir_p3::WhirConfigBuilder`.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct WhirParamsSerde {
    pub starting_log_inv_rate: usize,
    pub max_num_variables_to_send_coeffs: usize,
    pub rs_domain_initial_reduction_factor: usize,
    pub folding_factor: FoldingFactorSerde,
    pub soundness_type: SecurityAssumptionSerde,
    pub security_level: usize,
    pub pow_bits: usize,
}

impl From<&whir_p3::WhirConfigBuilder> for WhirParamsSerde {
    fn from(v: &whir_p3::WhirConfigBuilder) -> Self {
        Self {
            starting_log_inv_rate: v.starting_log_inv_rate,
            max_num_variables_to_send_coeffs: v.max_num_variables_to_send_coeffs,
            rs_domain_initial_reduction_factor: v.rs_domain_initial_reduction_factor,
            folding_factor: v.folding_factor.into(),
            soundness_type: v.soundness_type.into(),
            security_level: v.security_level,
            pow_bits: v.pow_bits,
        }
    }
}

impl From<&WhirParamsSerde> for whir_p3::WhirConfigBuilder {
    fn from(v: &WhirParamsSerde) -> Self {
        whir_p3::WhirConfigBuilder {
            starting_log_inv_rate: v.starting_log_inv_rate,
            max_num_variables_to_send_coeffs: v.max_num_variables_to_send_coeffs,
            rs_domain_initial_reduction_factor: v.rs_domain_initial_reduction_factor,
            folding_factor: v.folding_factor.into(),
            soundness_type: v.soundness_type.into(),
            security_level: v.security_level,
            pow_bits: v.pow_bits,
        }
    }
}

/// Serializable preprocessing artifact for a fixed AIR/trace shape.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct AirSnarkPreprocessing {
    pub version: u32,
    pub log_n_rows: usize,
    pub n_columns_f: usize,
    pub log_smallest_decomposition_chunk: usize,
    pub univariate_skips: usize,
    pub whir_params: WhirParamsSerde,
    pub packed_n_vars: usize,
    pub required_dft_twiddles_n: usize,
    pub n_constraints: usize,
}

impl AirSnarkPreprocessing {
    /// Build preprocessing info for a base-field-only AIR of fixed height.
    pub fn build_for_air_base<PF, A>(air: &A, log_n_rows: usize, config: &AirSnarkConfig) -> Self
    where
        PF: p3_field::Field,
        A: Air,
    {
        let n_columns_f = air.n_columns_f_air();
        let dims = vec![ColDims::<PF>::full(log_n_rows); n_columns_f];
        let chunks = MultilinearChunks::compute(&dims, config.log_smallest_decomposition_chunk);
        let packed_n_vars = chunks.packed_n_vars;

        // WHIR commit does reorder_and_dft(..., folding_factor_0, starting_log_inv_rate) and needs twiddles
        // up to dft_size = 2^(packed_n_vars + starting_log_inv_rate - folding_factor_0).
        let folding_factor_0 = config.whir_config_builder.folding_factor.at_round(0);
        let required_log = packed_n_vars + config.whir_config_builder.starting_log_inv_rate - folding_factor_0;
        let required_dft_twiddles_n = 1usize << required_log;

        Self {
            version: PREPROC_VERSION,
            log_n_rows,
            n_columns_f,
            log_smallest_decomposition_chunk: config.log_smallest_decomposition_chunk,
            univariate_skips: config.univariate_skips,
            whir_params: WhirParamsSerde::from(&config.whir_config_builder),
            packed_n_vars,
            required_dft_twiddles_n,
            n_constraints: air.n_constraints(),
        }
    }

    pub fn to_bytes_bincode(&self) -> Vec<u8> {
        bincode::serialize(self).expect("bincode serialize preprocessing")
    }

    pub fn from_bytes_bincode(bytes: &[u8]) -> Self {
        bincode::deserialize(bytes).expect("bincode deserialize preprocessing")
    }

    /// Convert preprocessing into a runtime config.
    pub fn to_config(&self) -> AirSnarkConfig {
        AirSnarkConfig {
            univariate_skips: self.univariate_skips,
            log_smallest_decomposition_chunk: self.log_smallest_decomposition_chunk,
            whir_config_builder: whir_p3::WhirConfigBuilder::from(&self.whir_params),
        }
    }

    /// Apply the preprocessing to the global WHIR DFT cache so proving can start immediately.
    pub fn apply_precompute<F: TwoAdicField>(&self) {
        whir_p3::precompute_dft_twiddles::<F>(self.required_dft_twiddles_n);
    }
}

