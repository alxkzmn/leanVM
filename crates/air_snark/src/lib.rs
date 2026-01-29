//! A minimal SNARK wrapper around this repo's AIR proof system, using WHIR as the PCS.
//!
//! High-level structure (mirrors the zkVM prover, but for a single AIR):
//! - Commit to the AIR trace columns using `packed_pcs_commit` (WHIR).
//! - Prove the AIR constraints using `air::prove_air`.
//! - Open the committed columns at the point/output of the AIR proof using WHIR.
//!
//! This is currently **non-ZK** (no blinding/hiding).

use std::collections::BTreeMap;

use air::{prove_air, verify_air};
use multilinear_toolkit::prelude::*;
use p3_air::Air;
use p3_field::PrimeField64;
use p3_util::{log2_ceil_usize, log2_strict_usize};
use sub_protocols::{
    ColDims, packed_pcs_commit, packed_pcs_global_statements_for_prover, packed_pcs_global_statements_for_verifier,
    packed_pcs_parse_commitment,
};
pub use utils::{FSProver, FSVerifier, build_challenger, build_prover_state};
use whir_p3::WhirConfig;
use whir_p3::WhirConfigBuilder;

pub mod preprocessing;
pub use preprocessing::*;

/// Trace layout information for `air_snark` commitments/openings.
///
/// This is where Whirlaway/lean-style “preprocessed columns” / “public prefix” columns are modeled:
/// - `dims_f[i]` defines which parts of column `i` are committed vs public.
/// - `public_data_f[i]` provides the verifier-known slice (length must be `2^log_public_data_size`).
#[derive(Debug, Clone)]
pub struct AirSnarkTraceLayout<F: p3_field::Field> {
    pub dims_f: Vec<ColDims<F>>,
    pub public_data_f: BTreeMap<usize, Vec<F>>,
}

impl<F: p3_field::Field> AirSnarkTraceLayout<F> {
    /// All columns are fully committed (current default behavior).
    pub fn all_committed(log_n_rows: usize, n_columns_f: usize) -> Self {
        Self {
            dims_f: vec![ColDims::full(log_n_rows); n_columns_f],
            public_data_f: BTreeMap::new(),
        }
    }

    /// Add verifier-known public data for a column (prefix or full column).
    pub fn insert_public_data(&mut self, col: usize, data: Vec<F>) {
        self.public_data_f.insert(col, data);
    }
}

/// Configuration for proving/verifying a single AIR with WHIR-backed commitments.
#[derive(Debug, Clone)]
pub struct AirSnarkConfig {
    pub univariate_skips: usize,
    pub log_smallest_decomposition_chunk: usize,
    /// Target soundness security (Whirlaway-style).
    pub security_bits: usize,
    pub whir_config_builder: WhirConfigBuilder,
}

fn pow_bits_auto<EF: p3_field::Field>(security_bits: usize, degree: usize) -> usize {
    security_bits.saturating_sub(EF::bits().saturating_sub(log2_ceil_usize(degree + 1)))
}

fn whir_builder_with_security(mut b: WhirConfigBuilder, security_bits: usize) -> WhirConfigBuilder {
    b.security_level = security_bits;
    b
}

/// Prove a single AIR (base-field trace columns only) and bind it to a WHIR commitment.
///
/// This is the external-consumer-friendly API: no `columns_ef` / `last_row_shifted_ef`.
pub fn prove_single_air_with_whir_base<EF, A>(
    prover_state: FSProver<EF, impl FSChallenger<EF>>,
    air: &A,
    extra_data: A::ExtraData,
    config: &AirSnarkConfig,
    layout: &AirSnarkTraceLayout<PF<EF>>,
    columns_f: &[impl AsRef<[PF<EF>]>],
    last_row_shifted_f: &[PF<EF>],
) -> Proof<PF<EF>>
where
    EF: ExtensionField<PF<EF>> + TwoAdicField,
    PF<EF>: PrimeField64 + TwoAdicField,
    A: Air,
    A::ExtraData: AlphaPowersMut<EF> + AlphaPowers<EF>,
{
    let empty_columns_ef: Vec<&[EF]> = vec![];
    let empty_last_row_shifted_ef: Vec<EF> = vec![];
    prove_single_air_with_whir(
        prover_state,
        air,
        extra_data,
        config,
        layout,
        columns_f,
        &empty_columns_ef,
        last_row_shifted_f,
        &empty_last_row_shifted_ef,
    )
}

/// Verify a single AIR proof produced by [`prove_single_air_with_whir_base`].
pub fn verify_single_air_with_whir_base<EF, A>(
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    air: &A,
    extra_data: A::ExtraData,
    config: &AirSnarkConfig,
    layout: &AirSnarkTraceLayout<PF<EF>>,
) -> Result<(), ProofError>
where
    EF: ExtensionField<PF<EF>> + TwoAdicField,
    PF<EF>: PrimeField64 + TwoAdicField,
    A: Air,
    A::ExtraData: AlphaPowersMut<EF> + AlphaPowers<EF>,
{
    verify_single_air_with_whir(verifier_state, air, extra_data, config, layout)
}

/// Prove a single AIR and bind it to a WHIR commitment to the trace columns.
///
/// The prover must supply the trace columns and the "last shifted row" values required by the AIR.
/// These last-row values are recorded in the transcript (so the verifier can recover them) but are
/// not hidden.
pub fn prove_single_air_with_whir<EF, A>(
    mut prover_state: FSProver<EF, impl FSChallenger<EF>>,
    air: &A,
    extra_data: A::ExtraData,
    config: &AirSnarkConfig,
    layout: &AirSnarkTraceLayout<PF<EF>>,
    columns_f: &[impl AsRef<[PF<EF>]>],
    columns_ef: &[impl AsRef<[EF]>],
    last_row_shifted_f: &[PF<EF>],
    last_row_shifted_ef: &[EF],
) -> Proof<PF<EF>>
where
    EF: ExtensionField<PF<EF>> + TwoAdicField,
    PF<EF>: PrimeField64 + TwoAdicField,
    A: Air,
    A::ExtraData: AlphaPowersMut<EF> + AlphaPowers<EF>,
{
    let columns_f: Vec<&[PF<EF>]> = columns_f.iter().map(|c| c.as_ref()).collect();
    let columns_ef: Vec<&[EF]> = columns_ef.iter().map(|c| c.as_ref()).collect();
    assert!(
        columns_ef.is_empty(),
        "air_snark currently supports only base-field trace columns; EF trace columns are not yet supported"
    );
    assert!(
        last_row_shifted_ef.is_empty(),
        "air_snark currently supports only base-field trace columns; last_row_shifted_ef must be empty"
    );

    let n_rows = if !columns_f.is_empty() {
        columns_f[0].len()
    } else {
        columns_ef[0].len()
    };
    assert!(columns_f.iter().all(|c| c.len() == n_rows));
    assert!(columns_ef.iter().all(|c| c.len() == n_rows));
    assert_eq!(columns_f.len(), air.n_columns_f_air());
    assert_eq!(
        air.n_columns_ef_air(),
        0,
        "air_snark currently supports only base-field AIRs"
    );
    let log_n_rows = log2_strict_usize(n_rows);

    // Public metadata required by the verifier.
    prover_state.add_base_scalars(&[PF::<EF>::from_usize(n_rows)]);

    // Provide the last-row shifted values via the transcript (so verifier can recover them).
    assert_eq!(last_row_shifted_f.len(), air.down_column_indexes_f().len());
    prover_state.add_base_scalars(last_row_shifted_f);
    assert!(air.down_column_indexes_ef().is_empty());

    // Coarse Whirlaway-style grinding: one checkpoint at SNARK entry.
    prover_state.pow_grinding(pow_bits_auto::<EF>(config.security_bits, air.n_constraints()));

    // Commit to the trace columns with WHIR.
    assert_eq!(
        layout.dims_f.len(),
        columns_f.len(),
        "layout.dims_f must match columns_f"
    );
    assert!(layout.dims_f.iter().all(|d| d.n_vars == log_n_rows));
    assert!(
        layout.dims_f.iter().all(|d| d.committed_size > 0),
        "air_snark (scoped) only supports columns with committed_size > 0 (public-prefix is ok, fully-public is not)"
    );
    for (&col, data) in &layout.public_data_f {
        let d = &layout.dims_f[col];
        let Some(log_public) = d.log_public_data_size else {
            panic!("public_data_f provided for col {col}, but dims_f[{col}] has no public data");
        };
        assert!(
            d.committed_size > 0,
            "public-prefix column {col} must have committed_size > 0"
        );
        assert_eq!(
            data.len(),
            1usize << log_public,
            "public_data_f[{col}] has wrong length"
        );
        assert_eq!(
            &columns_f[col][..data.len()],
            data.as_slice(),
            "public_data_f[{col}] must match the column prefix"
        );
    }
    let dims_base = layout.dims_f.clone();
    let whir_builder = whir_builder_with_security(config.whir_config_builder.clone(), config.security_bits);
    let witness_base = packed_pcs_commit::<PF<EF>, EF>(
        &whir_builder,
        &columns_f,
        &dims_base,
        &mut prover_state,
        config.log_smallest_decomposition_chunk,
    );

    // Prove the AIR constraints.
    let (point, evals_f, _evals_ef) = prove_air(
        &mut prover_state,
        air,
        extra_data,
        config.univariate_skips,
        &columns_f,
        &columns_ef,
        last_row_shifted_f,
        last_row_shifted_ef,
        None,
        false,
    );

    // Build opening statements: each committed column evaluated at `point`.
    let statements_base: Vec<Vec<Evaluation<EF>>> = evals_f
        .iter()
        .map(|&value| vec![Evaluation::new(point.clone(), value)])
        .collect();

    // Translate to packed statements and prove openings with WHIR.
    let packed_statements_base = packed_pcs_global_statements_for_prover(
        &columns_f,
        &dims_base,
        config.log_smallest_decomposition_chunk,
        &statements_base,
        &mut prover_state,
    );
    WhirConfig::new(whir_builder.clone(), witness_base.packed_polynomial.by_ref().n_vars()).prove(
        &mut prover_state,
        packed_statements_base,
        witness_base.inner_witness,
        &witness_base.packed_polynomial.by_ref(),
    );

    prover_state.into_proof()
}

/// Verify a single-AIR proof produced by [`prove_single_air_with_whir`].
pub fn verify_single_air_with_whir<EF, A>(
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    air: &A,
    extra_data: A::ExtraData,
    config: &AirSnarkConfig,
    layout: &AirSnarkTraceLayout<PF<EF>>,
) -> Result<(), ProofError>
where
    EF: ExtensionField<PF<EF>> + TwoAdicField,
    PF<EF>: PrimeField64 + TwoAdicField,
    A: Air,
    A::ExtraData: AlphaPowersMut<EF> + AlphaPowers<EF>,
{
    if air.n_columns_ef_air() != 0 || !air.down_column_indexes_ef().is_empty() {
        return Err(ProofError::InvalidProof);
    }

    // Read public metadata.
    let n_rows = verifier_state.next_base_scalars_vec(1)?[0].as_canonical_u64() as usize;
    let log_n_rows = log2_strict_usize(n_rows);

    // Recover last-row shifted values.
    let last_row_shifted_f = verifier_state.next_base_scalars_vec(air.down_column_indexes_f().len())?;
    let last_row_shifted_ef: Vec<EF> = vec![];

    // Reconstruct commitment dimensions and parse commitment from transcript.
    assert_eq!(
        layout.dims_f.len(),
        air.n_columns_f_air(),
        "layout.dims_f must match AIR width"
    );
    assert!(layout.dims_f.iter().all(|d| d.n_vars == log_n_rows));
    if !layout.dims_f.iter().all(|d| d.committed_size > 0) {
        return Err(ProofError::InvalidProof);
    }
    for (&col, data) in &layout.public_data_f {
        let d = &layout.dims_f[col];
        let Some(log_public) = d.log_public_data_size else {
            return Err(ProofError::InvalidProof);
        };
        if d.committed_size == 0 {
            return Err(ProofError::InvalidProof);
        }
        if data.len() != (1usize << log_public) {
            return Err(ProofError::InvalidProof);
        }
    }
    let dims_base = layout.dims_f.clone();
    let whir_builder = whir_builder_with_security(config.whir_config_builder.clone(), config.security_bits);
    let parsed_commitment_base = packed_pcs_parse_commitment::<PF<EF>, EF>(
        &whir_builder,
        verifier_state,
        &dims_base,
        config.log_smallest_decomposition_chunk,
    )?;

    // Coarse Whirlaway-style grinding: one checkpoint at SNARK entry.
    verifier_state.check_pow_grinding(pow_bits_auto::<EF>(config.security_bits, air.n_constraints()))?;

    // Verify the AIR transcript and obtain the evaluation point + claimed evals.
    let (point, evals_f, _evals_ef) = verify_air(
        verifier_state,
        air,
        extra_data,
        config.univariate_skips,
        log_n_rows,
        &last_row_shifted_f,
        &last_row_shifted_ef,
        None,
    )?;

    // Build opening statements for verifier.
    let statements_base: Vec<Vec<Evaluation<EF>>> = evals_f
        .iter()
        .map(|&value| vec![Evaluation::new(point.clone(), value)])
        .collect();

    let packed_statements_base = packed_pcs_global_statements_for_verifier(
        &dims_base,
        config.log_smallest_decomposition_chunk,
        &statements_base,
        verifier_state,
        &layout.public_data_f,
    )?;

    // Verify WHIR openings.
    WhirConfig::new(whir_builder, parsed_commitment_base.num_variables).verify::<PF<EF>>(
        verifier_state,
        &parsed_commitment_base,
        packed_statements_base,
    )?;

    Ok(())
}
