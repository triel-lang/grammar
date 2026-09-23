# TRIEL

An open specification language for deterministic, verifiable compilation.

Website: https://triel.dev

Interactive demo: https://triel.ai (illustrative examples, not a live compiler)

TRIEL is designed so that a single, human-readable specification can compile deterministically into multiple downstream artifacts — including executable code, formal proofs, and structured documentation — from one authoritative source. This repository contains the language definition; no compiler is published here (see `TECHNICAL_REPORT.md` §4).

## The problem

Software specifications and their implementations tend to drift apart over time. A specification is written once; the implementation is built, maintained, and modified separately — and the two slowly diverge. This gap is a common source of costly failures, compliance issues, and audit findings.

## The approach

TRIEL treats specification-to-implementation translation as the point where correctness evidence should be generated — not recovered afterward through separate testing or review.

## Status

This repository contains the core language grammar (EBNF), released as an open specification. The grammar is a work in progress and will evolve.

Current version: v2.4 (`TRIEL-grammar-v2_4-core.ebnf`). The previous version remains available for reference: `TRIEL-grammar-v2.3.3-core.ebnf`.

Since its first publication, v2.4 has been revised in response to an independent technical audit, and some of these revisions are not backward-compatible (see `TECHNICAL_REPORT.md` §2.8–§2.11).

Relative to v2.3.3, v2.4 adds three extensions:

* `REPLACES` in the declaration block, for chaining specification versions
* an optional `WITHIN` deadline on `EVENTUALLY(...)` invariants, for bounded liveness properties
* a `Progress<T>` composite type, for expressing graduated status (not just boolean done/not-done)

## Examples

The `examples/` directory contains sample TRIEL specifications:

* `hello_triel.triel` — minimal valid specification
* `delivery_agreement.triel` — obligations, deadlines, and breach handling
* `age_verification.triel` — privacy-preserving verification using native zero-knowledge constraints
* `eudi/eudi_driving_license.triel` — EUDI Wallet-style issuance and presentation policy for a driving license credential, combining conditional obligations and a zero-knowledge age predicate
* `semantics/` — small specifications accompanying the semantics in `TECHNICAL_REPORT.md` §2.5 and §2.9: obligations and deadlines, `UNLESS` and its laws, missing and stale data, hierarchical names, and `EXECUTE` bindings

Every example is parsed against the grammar, with an ambiguity check, on every push (`.github/workflows/parse-examples.yml`).

Of these, `age_verification.triel` and `eudi_driving_license.triel` — privacy-preserving identity and credential verification — are the most thoroughly worked through and tested; see `TECHNICAL_REPORT.md` §4 for the fuller scope statement.

## License

The TRIEL specification is made available under the [Open Web Foundation Agreement 1.0 (OWFa 1.0)](https://github.com/triel-lang/grammar/blob/main/LICENSE.md).

## Contact

Dmitri Chistyakov
