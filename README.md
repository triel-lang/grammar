# TRIEL
**An open specification language for deterministic, verifiable compilation.**

TRIEL lets a single, human-readable specification compile deterministically
into multiple downstream artifacts — including executable code, formal
proofs, and structured documentation — from one authoritative source.

## The problem

Software specifications and their implementations tend to drift apart over
time. A specification is written once; the implementation is built,
maintained, and modified separately — and the two slowly diverge. This gap
is a common source of costly failures, compliance issues, and audit
findings.

## The approach

TRIEL treats specification-to-implementation translation as the point
where correctness evidence should be generated — not recovered afterward
through separate testing or review.

## Status

This repository contains the core language grammar (EBNF), released as an
open specification. The grammar is a work in progress and will evolve.

Current version: **v2.4** ([`TRIEL-grammar-v2_4-core.ebnf`](TRIEL-grammar-v2_4-core.ebnf)).
The previous version remains available for reference: [`TRIEL-grammar-v2.3.3-core.ebnf`](TRIEL-grammar-v2.3.3-core.ebnf).

v2.4 adds three backward-compatible extensions:
- `REPLACES` in the declaration block, for chaining specification versions
- an optional `WITHIN` deadline on `EVENTUALLY(...)` invariants, for bounded liveness properties
- a `Progress<T>` composite type, for expressing graduated status (not just boolean done/not-done)

## Examples

The `examples/` directory contains sample TRIEL specifications:

- [`hello_triel.triel`](examples/hello_triel.triel) — minimal valid specification
- [`delivery_agreement.triel`](examples/delivery_agreement.triel) — obligations, deadlines, and breach handling
- [`age_verification.triel`](examples/age_verification.triel) — privacy-preserving verification using native zero-knowledge constraints
- [`eudi/eudi_driving_license.triel`](examples/eudi/eudi_driving_license.triel) — EUDI Wallet-style issuance and presentation policy for a driving license credential, combining conditional obligations and a zero-knowledge age predicate

## License

The TRIEL specification is made available under the [Open Web Foundation
Agreement 1.0 (OWFa 1.0)](LICENSE.md).

## Contact

Dmitri Chistyakov
