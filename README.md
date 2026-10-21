# TRIEL

[![Parse examples against grammar](https://github.com/triel-lang/grammar/actions/workflows/parse-examples.yml/badge.svg)](https://github.com/triel-lang/grammar/actions/workflows/parse-examples.yml)
[![Isabelle build of formal/core](https://github.com/triel-lang/grammar/actions/workflows/isabelle.yml/badge.svg)](https://github.com/triel-lang/grammar/actions/workflows/isabelle.yml)
[![Evaluator exported from formal/core](https://github.com/triel-lang/grammar/actions/workflows/evaluator.yml/badge.svg)](https://github.com/triel-lang/grammar/actions/workflows/evaluator.yml)

An open specification language for rules with one precise, checkable meaning.

Website: https://triel.dev

Interactive demo: https://triel.ai (illustrative examples only)

A TRIEL specification states who must, may or must not do what, by when, on which data, and what follows a breach. Its meaning is defined precisely: for the fragment covered by the formal core, the verdict of every obligation on a finite trace of events is computed mechanically. This repository contains the language and its machine-checked core; `TECHNICAL_REPORT.md` §4 states its scope.

## The problem

Software specifications and their implementations tend to drift apart over time. A specification is written once; the implementation is built, maintained, and modified separately — and the two slowly diverge. This gap is a common source of costly failures, compliance issues, and audit findings.

## The approach

TRIEL gives the rules one authoritative meaning that a machine can check, so that an implementation and an audit are checked against the same text rather than against separate readings of it.

## Status

This repository contains the core language grammar (EBNF), released as an open specification, together with a formal semantics of its core in Isabelle/HOL.

Current version: v2.5 (`TRIEL-grammar-v2_5-core.ebnf`). Version 2.5 is frozen: the grammar and the semantics of the formal core change only in a new version. Earlier versions are in the history of this repository; `TRIEL-grammar-v2.3.3-core.ebnf` is kept for reference.

Version 2.5 is version 2.4, first published in July 2026, with the revisions made since in response to an independent technical audit and while formalising the core. Some of them are not backward-compatible:

* `REPLACES` names the specification whose version it replaces, and `IMPORT`, `EXECUTE` and `REPLACES` must pin the content they refer to with `HASH` (`TECHNICAL_REPORT.md` §2.10)
* `UNTIL` is no longer part of an obligation (§2.2)
* there is no `Float` type and no exponent notation: every numeric literal is exact (§2.9)
* semantic rules make optional fields required where they matter: `PROOF_SYSTEM` and `CURVE` with zero-knowledge factors, `BOUND_TO` on a zero-knowledge factor whose source has a `DID` (§2.8), `ON_STALE` with `MAX_AGE`, `PROVENANCE_REQUIRED: true` for data from an `ORACLE`, and `CURRENCY` with a `PENALTY` (§2.9)

Version 2.5 also adds `PRESENT`, `DEFAULT` and `CAP` (§2.9), signed literals and trailing separators (§2.11), and gives the language a trace semantics (§2.5), a breach and deadline semantics (§2.6) and an information-flow rule for zero-knowledge factors (§2.7).

Relative to v2.3.3, v2.4 added three extensions:

* `REPLACES` in the declaration block, for chaining specification versions
* an optional `WITHIN` deadline on `EVENTUALLY(...)` invariants, for bounded liveness properties
* a `Progress<T>` composite type, for expressing graduated status (not just boolean done/not-done)

## Formal core

[`formal/core`](formal/core/CORE.md) formalises the semantics of a core of TRIEL in Isabelle/HOL: its definitions, the theorems proved about them, and the design decisions they forced. An evaluator exported from these theories ([`evaluator/`](evaluator/README.md)) computes the verdicts of a specification on a trace. [`parser/triel_to_core.py`](parser/README.md) translates a specification into the core and checks the semantic rules that apply to it, or rejects by name the constructs that lie outside it. [`examples/core/`](examples/core/README.md) holds specifications and scenarios with their expected reports; `examples/core/classification.expected` lists which examples the core accepts.

## Examples

The `examples/` directory contains sample TRIEL specifications:

* `hello_triel.triel` — minimal valid specification
* `delivery_agreement.triel` — obligations, deadlines, and breach handling
* `age_verification.triel` — an age check whose `age` factor is declared hidden (`ZK<Integer> PROVES(self >= 18)`): the specification states what must be provable about it and, by the flow rule, may not read its value; the proof itself is produced and checked outside TRIEL
* `eudi/eudi_driving_license.triel` — EUDI Wallet-style issuance and presentation policy for a driving license credential, combining conditional obligations and a zero-knowledge age predicate
* `semantics/` — small specifications accompanying the semantics in `TECHNICAL_REPORT.md` §2.5 and §2.9: obligations and deadlines, `UNLESS` and its laws, missing and stale data, hierarchical names, and `EXECUTE` bindings
* `core/` — specifications inside the formal core, with scenarios and expected reports

Every example is parsed against the grammar, with an ambiguity check, on every push (`.github/workflows/parse-examples.yml`). The same workflow checks the grammar for ambiguity: one derivation for every example and probe input (Earley, `lexer=dynamic`), and an LALR(1) table whose only conflicts are four that, by an argument made by hand, are not ambiguities (`TECHNICAL_REPORT.md` §2.12). It also checks that every TRIEL excerpt of the documents and of the grammar file conforms to the grammar (`parser/test_documents.py`).

Of these, `age_verification.triel` and `eudi_driving_license.triel` — identity and credential checks with hidden zero-knowledge factors — are the most thoroughly worked through and tested; see `TECHNICAL_REPORT.md` §4 for the fuller scope statement.

## Foundations

TRIEL's semantics builds on the composition-nominative approach to program logics developed by M. Nikitchenko, S. Shkilniak and colleagues at Taras Shevchenko National University of Kyiv, in particular *Applied Logic* (2013), *Algebras and logics of partial quasiary predicates* (2017) and *Composition-Nominative Methods and Models in Program Development* (2022). `FOUNDATIONS.md` gives the full references and states, for each construct, which results it rests on and which questions remain open.

## License

- The TRIEL Language Specification, version 2.5 (`TRIEL-grammar-v2_5-core.ebnf`, `TECHNICAL_REPORT.md`, `formal/core/CORE.md`), is made available under the Open Web Foundation Final Specification Agreement 1.0 (OWFa 1.0).
- The code (the Isabelle theories in `formal/core/`, `evaluator/`, `parser/`, `examples/`, `.github/`) is licensed under the [Apache License 2.0](LICENSE-APACHE).
- Contributions are accepted under the [TRIEL Contributor License Agreement](CLA.md); see [CONTRIBUTING.md](CONTRIBUTING.md).

[LICENSE.md](LICENSE.md) governs, including what the specification does not cover.

## Contact

Dmitri Chistyakov
