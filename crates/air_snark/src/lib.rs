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
use p3_util::log2_strict_usize;
use sub_protocols::{
    ColDims, packed_pcs_commit, packed_pcs_global_statements_for_prover, packed_pcs_global_statements_for_verifier,
    packed_pcs_parse_commitment,
};
use utils::{FSProver, FSVerifier};
use whir_p3::WhirConfig;
use whir_p3::WhirConfigBuilder;

/// Configuration for proving/verifying a single AIR with WHIR-backed commitments.
#[derive(Debug, Clone)]
pub struct AirSnarkConfig {
    pub univariate_skips: usize,
    pub log_smallest_decomposition_chunk: usize,
    pub whir_config_builder: WhirConfigBuilder,
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

    // Commit to the trace columns with WHIR.
    let dims_base = vec![ColDims::full(log_n_rows); columns_f.len()];
    let witness_base = packed_pcs_commit::<PF<EF>, EF>(
        &config.whir_config_builder,
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
    WhirConfig::new(
        config.whir_config_builder.clone(),
        witness_base.packed_polynomial.by_ref().n_vars(),
    )
    .prove(
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
    let dims_base = vec![ColDims::full(log_n_rows); air.n_columns_f_air()];
    let parsed_commitment_base = packed_pcs_parse_commitment::<PF<EF>, EF>(
        &config.whir_config_builder,
        verifier_state,
        &dims_base,
        config.log_smallest_decomposition_chunk,
    )?;

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

    let public_data: BTreeMap<usize, Vec<PF<EF>>> = BTreeMap::new();
    let packed_statements_base = packed_pcs_global_statements_for_verifier(
        &dims_base,
        config.log_smallest_decomposition_chunk,
        &statements_base,
        verifier_state,
        &public_data,
    )?;

    // Verify WHIR openings.
    WhirConfig::new(config.whir_config_builder.clone(), parsed_commitment_base.num_variables).verify::<PF<EF>>(
        verifier_state,
        &parsed_commitment_base,
        packed_statements_base,
    )?;

    Ok(())
}
