# TRIEL reference parser

A reference parser for TRIEL v2.5, built from the published grammar
(`TRIEL-grammar-v2_5-core.ebnf`) using [Lark](https://github.com/lark-parser/lark)
1.3.1 (Earley, dynamic lexer).

## Files

- `triel.lark`: the grammar, a rule-for-rule translation of the EBNF. The two
  are kept in step by hand.
- `triel_parser.py`: parses specifications; `--check-ambiguity` counts their
  derivations.
- `test_ambiguity.py`: the ambiguity regression tests and the check of the
  LALR(1) table (`TECHNICAL_REPORT.md` §2.12).
- `test_documents.py`: every TRIEL excerpt of the documents, every grammar
  excerpt of `TECHNICAL_REPORT.md` and every usage example of the grammar file
  conforms to the grammar.
- `triel_to_core.py`: the translator to the formal core.
- `triel_eval.py`: the scenario driver of the evaluator.
- `test_triel_to_core.py`: the tests of the translator and of the driver.

## What the parser is

- A faithful translation of the EBNF into a runnable grammar, used to check
  that files under `examples/` actually conform to the grammar they're meant
  to demonstrate (audit finding A-01).
- A diagnostic tool: `--check-ambiguity` reports when the grammar admits more
  than one parse tree for a given input. Every example and every probe input
  of `test_ambiguity.py` has exactly one; `TECHNICAL_REPORT.md` §2.12 states
  what this establishes and what it does not.

## What the parser is not

- **Not a compiler.** It checks syntax only. It does not check the
  semantic-analysis rules noted in the grammar's own SEMANTIC RULES section
  (e.g. `QUORUM_THRESHOLD` bounds, `Progress<T>` completion constraints),
  and it does not implement or check anything about the temporal-logic or
  zero-knowledge *semantics* of a specification — those are defined
  separately in `TECHNICAL_REPORT.md` §2.5–§2.9. Trace satisfaction for the
  fragment inside the formal core is computed by the evaluator exported from
  `formal/core` (see below), and the semantic-analysis rules that apply to
  that fragment (`TECHNICAL_REPORT.md` §2.6–§2.9, declared names, the
  well-formedness of a `TERMS` block) are checked by `triel_to_core.py`.
  Nothing here produces or checks a zero-knowledge proof.
- **Not a validator of well-formedness beyond syntax.** A file can parse
  successfully and still, for example, read a `WITHOUT REVEALING`-marked
  field directly in an invariant (see audit finding B-08) — the grammar as
  published does not forbid this, and neither does this parser. The
  translator `triel_to_core.py` rejects it.

## Usage

```bash
pip install lark==1.3.1 pytest
python3 parser/triel_parser.py examples/*.triel examples/eudi/*.triel
python3 parser/triel_parser.py --check-ambiguity examples/hello_triel.triel
python3 parser/test_ambiguity.py
python3 parser/test_documents.py
```

Exit code is non-zero if any file fails to parse. This is what
`.github/workflows/parse-examples.yml` runs on every push and pull request.

## Translation to the formal core and the evaluator

`triel_to_core.py` translates a specification into the core of
[`formal/core`](../formal/core/CORE.md) (section 10). Every construct is
translated, printed as metadata, or rejected by name; only the outermost
unsupported construct is reported.

```bash
python3 parser/triel_to_core.py examples/core/core_deadline_cure.triel   # core AST
python3 parser/triel_to_core.py --classify examples                      # ACCEPTED / REJECTED
python3 parser/triel_eval.py examples/core/scenarios/deadline_cure_ok.scn
python3 -m pytest parser/test_triel_to_core.py
```

`triel_eval.py` runs a scenario through the evaluator built from
[`evaluator/`](../evaluator/README.md). The path in `(spec PATH)` is relative
to the root of the repository. Strings are read with the escapes of
`evaluator/Main.hs` (`\n`, `\t`, and `\c` for any other character c). The
driver does not check the order of the times: the evaluator rejects a trace
whose times decrease (`TIME ORDER REJECTED`). Exit codes: 0 accepted or
evaluated, 2 rejected, 1 parse or input error.
