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

## Examples

The `examples/` directory contains sample TRIEL specifications:

- [`hello_triel.triel`](examples/hello_triel.triel) — minimal valid specification
- [`delivery_agreement.triel`](examples/delivery_agreement.triel) — obligations, deadlines, and breach handling
- [`age_verification.triel`](examples/age_verification.triel) — privacy-preserving verification using native zero-knowledge constraints

## License

The TRIEL specification is made available under the [Open Web Foundation
Agreement 1.0 (OWFa 1.0)](LICENSE.md).

## Contact

Dmitri Chistyakov
