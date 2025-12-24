## `air_snark`

Minimal **single-AIR Whirlaway-style SNARK wrapper**.

### What it does

Given:

- an AIR (`p3_air::Air`, the forked “Whirlaway-style” trait used in this repo),
- base-field trace columns (`columns_f`) and their last-row “shift” values,

it produces a non-interactive proof that:

- **commits** to the trace columns via WHIR, and
- proves the AIR constraints via `air::prove_air`, and
- **opens** the committed columns at the AIR’s random evaluation point, again via WHIR.

### Important notes

- **128-bit security / EF**: the proof system uses an extension field `EF` for Fiat–Shamir challenges and sumcheck arithmetic. This is independent from whether your trace columns are stored in `EF`.
- **Trace columns in `EF`**: currently **not supported** here (intentionally). For “normal” AIRs like the Keccak AIR in this repo, you typically don’t need EF-valued trace columns.
- **Non‑ZK**: this wrapper doesn’t do witness hiding/blinding yet.

### Example

See the integration test `tests/keccak_whir.rs` for a full end-to-end example proving the Keccak AIR with WHIR commitments.
