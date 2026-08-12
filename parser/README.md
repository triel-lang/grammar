# TRIEL reference parser

A reference parser for TRIEL v2.4, built from the published grammar
(`TRIEL-grammar-v2_4-core.ebnf`) using [Lark](https://github.com/lark-parser/lark)
(Earley, dynamic lexer).

## What this is

- A faithful translation of the EBNF into a runnable grammar, used to check
  that files under `examples/` actually conform to the grammar they're meant
  to demonstrate (audit finding A-01).
- A diagnostic tool: `--check-ambiguity` reports when the grammar admits more
  than one parse tree for a given input. This surfaces real ambiguities in
  the published grammar (see audit findings D-19, D-20, D-21) rather than
  silently picking one interpretation.

## What this is not

- **Not a compiler.** It checks syntax only. It does not check the
  semantic-analysis rules noted in the grammar's own SEMANTIC RULES section
  (e.g. `QUORUM_THRESHOLD` bounds, `Progress<T>` completion constraints),
  and it does not implement or check anything about the temporal-logic or
  zero-knowledge *semantics* of a specification — those are defined
  separately in `TECHNICAL_REPORT.md` §2.5, and no tool in this repository
  verifies trace satisfaction or ZK-constraint soundness against them.
- **Not a validator of well-formedness beyond syntax.** A file can parse
  successfully and still, for example, read a `WITHOUT REVEALING`-marked
  field directly in an invariant (see audit finding B-08) — the grammar as
  published does not forbid this, and neither does this parser.
- **Ambiguity is reported, not resolved.** Where the grammar is genuinely
  ambiguous, `ambiguity="resolve"` (the default mode used for pass/fail
  checks) picks *a* parse silently, the same way most parser generators
  would. `--check-ambiguity` is the only way to find out that a choice was
  made for you. Fixing the ambiguities themselves is a grammar change,
  tracked separately.

## Usage

```bash
pip install lark
python3 parser/triel_parser.py examples/*.triel examples/eudi/*.triel
python3 parser/triel_parser.py --check-ambiguity examples/hello_triel.triel
```

Exit code is non-zero if any file fails to parse. This is what
`.github/workflows/parse-examples.yml` runs on every push and pull request.
