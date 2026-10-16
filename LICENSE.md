# License

This repository contains material under different terms: the TRIEL Language Specification (section 1), code (section 2), and other files (section 3). This file governs; the summary in `README.md` does not.

## 1. TRIEL Language Specification, version 2.5: OWFa 1.0

The TRIEL Language Specification is made available under the Open Web Foundation Final Specification Agreement 1.0 (OWFa 1.0).

Bound Entity: Dmitri Chistyakov
Specification: TRIEL Language Specification, version 2.5 (Core Language Edition)
Date: October 16, 2026

The Specification consists of exactly these files, in the state of tag `v2.5` (commit `57c5410`):

- `TRIEL-grammar-v2_5-core.ebnf`
- `TECHNICAL_REPORT.md`
- `formal/core/CORE.md`

No other file in this repository is part of the Specification.

**What the Specification covers.** The Specification defines the TRIEL language: its syntax, its semantic rules and the meaning of its core. It does not define any method of compiling a TRIEL specification. Compilation, intermediate representations, the generation of output artifacts, and the hashing or signing of output artifacts are outside the Specification. Where the Specification says that a behavior is compiler-defined, it refers to that behavior and does not describe it. The `HASH` values that the Specification requires on `IMPORT`, `EXECUTE` and `REPLACES` pin the content of inputs only.

Full text of the agreement: https://www.openwebfoundation.org/the-agreements/the-owf-1-0-agreements-granted-claims/owfa-1-0

**Earlier version.** The OWFa 1.0 statement made on July 17, 2026 for the TRIEL Language Specification, version 2.4 (Core Language Edition), remains in effect for that version.

## 2. Code: Apache License 2.0

The following are licensed under the Apache License, Version 2.0. The full text is in `LICENSE-APACHE`; the notice to keep when redistributing is in `NOTICE`.

- `formal/core/`: the Isabelle theories, `ROOT`, `document/` and the build log. `formal/core/CORE.md` is not code; it is part of the Specification (section 1).
- `evaluator/`: the evaluator, including the Haskell code exported from `formal/core/`.
- `parser/`: the reference parser, the translator to the core and their tests.
- `examples/`: example specifications, scenarios and expected results.
- `.github/`: the CI workflows.

Copyright 2026 Dmitri Chistyakov.

## 3. Other files

All other files, including `README.md`, `RELATED_WORK.md`, `FOUNDATIONS.md` and `TRIEL-grammar-v2.3.3-core.ebnf` (an earlier grammar kept for reference), are not licensed under this file. © 2026 Dmitri Chistyakov.

## 4. Patents and trademarks

No patent rights are granted other than those stated in OWFa 1.0 for the Specification and in section 3 of the Apache License 2.0 for the code. No trademark rights are granted.

## 5. Contributions

Contributions are accepted under the TRIEL Contributor License Agreement (`CLA.md`). How to sign it is described in `CONTRIBUTING.md`.
