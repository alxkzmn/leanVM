use p3_air::Air;
use p3_field::TwoAdicField;
use serde::{Deserialize, Serialize};
use sub_protocols::{ColDims, MultilinearChunks};

use crate::{AirSnarkConfig, AirSnarkTraceLayout};

const PREPROC_VERSION: u32 = 2;

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

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ColDimsSerde {
    pub n_vars: usize,
    pub log_public_data_size: Option<usize>,
    pub committed_size: usize,
    pub default_value_u64: u64,
}

impl<PF: p3_field::PrimeField64> From<&ColDims<PF>> for ColDimsSerde {
    fn from(v: &ColDims<PF>) -> Self {
        Self {
            n_vars: v.n_vars,
            log_public_data_size: v.log_public_data_size,
            committed_size: v.committed_size,
            default_value_u64: v.default_value.as_canonical_u64(),
        }
    }
}

impl ColDimsSerde {
    pub fn to_coldims<PF: p3_field::PrimeField64>(&self) -> ColDims<PF> {
        ColDims {
            n_vars: self.n_vars,
            log_public_data_size: self.log_public_data_size,
            committed_size: self.committed_size,
            default_value: PF::from_u64(self.default_value_u64),
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
    pub security_bits: usize,
    pub whir_params: WhirParamsSerde,
    pub dims_f: Vec<ColDimsSerde>,
    pub packed_n_vars: usize,
    pub required_dft_twiddles_n: usize,
    pub n_constraints: usize,
}

impl AirSnarkPreprocessing {
    /// Build preprocessing info for a base-field-only AIR of fixed height.
    pub fn build_for_air_base<PF, A>(air: &A, log_n_rows: usize, config: &AirSnarkConfig) -> Self
    where
        PF: p3_field::PrimeField64,
        A: Air,
    {
        let n_columns_f = air.n_columns_f_air();
        let layout = AirSnarkTraceLayout::<PF>::all_committed(log_n_rows, n_columns_f);
        Self::build_for_air_base_with_layout(air, log_n_rows, config, &layout)
    }

    pub fn build_for_air_base_with_layout<PF, A>(
        air: &A,
        log_n_rows: usize,
        config: &AirSnarkConfig,
        layout: &AirSnarkTraceLayout<PF>,
    ) -> Self
    where
        PF: p3_field::PrimeField64,
        A: Air,
    {
        let n_columns_f = air.n_columns_f_air();
        assert_eq!(layout.dims_f.len(), n_columns_f);
        let chunks = MultilinearChunks::compute(&layout.dims_f, config.log_smallest_decomposition_chunk);
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
            security_bits: config.security_bits,
            whir_params: WhirParamsSerde::from(&config.whir_config_builder),
            dims_f: layout.dims_f.iter().map(ColDimsSerde::from).collect(),
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
        let whir_config_builder = whir_p3::WhirConfigBuilder::from(&self.whir_params);
        AirSnarkConfig {
            univariate_skips: self.univariate_skips,
            log_smallest_decomposition_chunk: self.log_smallest_decomposition_chunk,
            security_bits: self.security_bits,
            whir_config_builder,
        }
    }

    /// Reconstruct the trace layout metadata (without the actual public data values).
    pub fn to_layout<PF: p3_field::PrimeField64>(&self) -> AirSnarkTraceLayout<PF> {
        AirSnarkTraceLayout {
            dims_f: self.dims_f.iter().map(|d| d.to_coldims::<PF>()).collect(),
            public_data_f: Default::default(),
        }
    }

    /// Apply the preprocessing to the global WHIR DFT cache so proving can start immediately.
    pub fn apply_precompute<F: TwoAdicField>(&self) {
        whir_p3::precompute_dft_twiddles::<F>(self.required_dft_twiddles_n);
    }
}
