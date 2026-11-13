# AGENTS.md

This repository holds TRIEL: the grammar of the language, the semantics of its core in Isabelle/HOL, an evaluator exported from the theories, a translator from specifications to the core, and examples. This file is for changing the repository. To use TRIEL instead (check an action against a specification, write a specification, read a report), read `.agents/skills/triel/SKILL.md`.

## Map

- `formal/core/`: the theories of the core (session `TRIEL_Core`) and `formal/core/CORE.md`.
- `formal/checks/`: the session `TRIEL_Core_Checks`, which checks the named theorems of `TRIEL_Core` for oracles.
- `evaluator/`: the evaluator, `evaluator/generated/TRIEL.hs` exported from `formal/core/` and `evaluator/Main.hs`.
- `parser/`: the reference parser, the translator to the core, the scenario driver, `triel check` and their tests (`parser/README.md`).
- `examples/`: example specifications; `examples/core/` holds those inside the core, with scenarios, expected reports and the conformance suite.
- `artifact/`: Docker image and `run.sh`, which repeats the CI checks in one command, except `parser/test_skill.py` and `parser/test_host.py`.
- `tools/`: helper scripts.
- `.github/workflows/`: the CI workflows.
- `.agents/skills/triel/`: the skill for agents that use TRIEL; `.claude/skills/triel` is a link to it.
- At the root: the grammar `TRIEL-grammar-v2_5-core.ebnf`, `TECHNICAL_REPORT.md`, `FOUNDATIONS.md`, `RELATED_WORK.md`, and the license files.

## Build and check

Run the commands from the root of the repository; they are the commands of the CI workflows.

`evaluator.yml` (Evaluator exported from formal/core): export the evaluator, build it with GHC 9.6.7, and check it.

```bash
isabelle build -e -v -D formal/core
git diff --exit-code -- evaluator/generated
ghc -O1 -ievaluator/generated -outputdir evaluator/build -o evaluator/triel-eval evaluator/Main.hs
pip install lark==1.3.1 pytest
python3 parser/triel_to_core.py --classify examples > /tmp/classification.txt
diff -u examples/core/classification.expected /tmp/classification.txt
python3 examples/core/conformance/run.py --level verdicts
python3 examples/core/conformance/run.py --level monitor
python3 -m pytest -q parser/test_triel_to_core.py
python3 -m pytest -q parser/test_triel_check.py
python3 -m pytest -q parser/test_skill.py
python3 -m pytest -q parser/test_host.py
```

The workflow also runs every scenario of `examples/core/scenarios/` with `python3 parser/triel_eval.py` and compares the report with its expected report, checks the sha256 of every file in `examples/core/conformance/manifest.json`, and checks the conformance runner itself. Before the Isabelle build it switches off the PDF document in its copy of `formal/core/ROOT`, since LaTeX is not installed; do the same locally without LaTeX, and do not commit that change.

`parse-examples.yml` (Parse examples against grammar):

```bash
pip install lark==1.3.1
python3 parser/triel_parser.py --check-ambiguity examples/*.triel examples/eudi/*.triel examples/semantics/*.triel examples/core/*.triel
python3 parser/test_ambiguity.py
python3 parser/test_documents.py
```

`isabelle.yml` (Isabelle build of formal/core), job `build`: no `sorry`, `oops` or `axiomatization` in `formal/core/*.thy`, then the session and the check for oracles.

```bash
isabelle build -b -v -D formal/core
isabelle build -e -v -d formal/core -D formal/checks
```

## What must not break

- `evaluator/generated/TRIEL.hs` is exported by Isabelle from `formal/core/TRIEL_Exec.thy` and is never edited by hand. Change the theories and export it again; CI checks that the committed file is exactly what Isabelle exports.
- `parser/triel.lark` and `TRIEL-grammar-v2_5-core.ebnf` are kept in step by hand: change both.
- The expected reports `examples/core/scenarios/*.expected` and the expected classification `examples/core/classification.expected` were written by hand from the text of the specifications, so that the evaluator is not checked against its own output. The exception is the four scenarios `examples/core/scenarios/purpose_*.scn`: their reports were derived by hand and then run before they were committed, and their expected outputs are the reports printed by the evaluator, which agreed with the derivation by hand (`examples/core/README.md`). Do not write an expected report from the output of the evaluator.
- The three files of the Specification are listed in `LICENSE.md`, section 1. The grammar and the semantics of the formal core change only in a new version (`README.md`, section "Status").
- Contributions are accepted under the Contributor License Agreement (`CLA.md`); `CONTRIBUTING.md` says how to sign it.
