# Artifact: the TRIEL 2.5 core in Isabelle/HOL

## What this is

This artifact reproduces the machine-checked results and the executable checks
behind the paper. It contains:

- `formal/core/`: the core of TRIEL 2.5 in Isabelle/HOL, 12 theories (session
  `TRIEL_Core`). All theorems are proved; there is no `sorry`, `oops` or
  `axiomatization`.
- `evaluator/`: an evaluator of the core. Its Haskell code
  (`evaluator/generated/TRIEL.hs`) is exported by Isabelle from
  `formal/core/TRIEL_Exec.thy`; `evaluator/Main.hs` only reads the input and
  prints the report.
- `parser/`: the reference parser of TRIEL 2.5, and the translator
  `parser/triel_to_core.py` from TRIEL specifications to terms of the core.
- `examples/`: 25 TRIEL specifications and 35 scenarios (implementation traces
  with hand-written expected reports).
- `artifact/`: the Docker image (`Dockerfile`), the script that runs every check
  (`run.sh`), and the Isabelle session `TRIEL_Paper`
  (`isabelle/Paper_Theorems.thy`), which lists by name the 34 theorems cited in
  the paper.

`artifact/run.sh` runs, in one command, every check of the repository's CI
(`isabelle.yml`, `evaluator.yml`, `parse-examples.yml`), builds `TRIEL_Paper`,
and prints a summary whose numbers are all computed by the run.

## Requirements

- x86-64 Linux host (or any Docker host that runs `linux/amd64` images) with
  Docker 20.10 or later.
- CPU: 4 cores recommended; Isabelle uses up to 4 threads.
- Memory: 8 GB. Peak resident memory of a run, measured as the sum of the
  resident set sizes of all processes in the container: about 6.5 GB, during
  the Isabelle build. The measured run had a limit of 8 GB (`--memory=8g`).
- Disk: about 10 GB for the image (3.1 GB compressed download), plus 1 GB
  for a run.
- Network: only to build the image (base images and Python wheels). Running
  the image needs no network.

Measured on a 4-core x86-64 virtual machine with 16 GB of memory:

| Phase | Time |
|---|---|
| Download of the base images | 2 min |
| Image build (`docker build`) | 3 min |
| `run.sh`, all steps | 13 min |
| of which: Isabelle build of `TRIEL_Core` (clean) | 1.5 min |
| of which: translator and driver tests (pytest) | 7 min |
| of which: 35 scenarios | 2.5 min |

## Running

From the root of the repository (or of the unpacked archive):

```bash
docker build -f artifact/Dockerfile -t triel-artifact .
docker run --rm triel-artifact
```

The second command runs `artifact/run.sh`. It copies the repository to a
scratch directory inside the container and runs every step there, so nothing
in the image is modified. It exits with 0 if every step passed. To keep the logs
on the host:

```bash
mkdir -p results && chmod 777 results
docker run --rm -e RESULTS_DIR=/results -v "$PWD/results:/results" triel-artifact
```

`results/` then holds one log per step, `summary.txt`, `classification.txt`,
`paper_theorems.txt` and the reports of the scenarios (`scenarios/*.out`).

Expected end of the output:

```
=== Summary
theories checked by Isabelle (TRIEL_Core)    12 (.thy files in formal/core: 12)
proved statements (lemma/theorem/corollary)  563
paper theorems found, without oracles        34 of 34
scenarios matching .expected                 35 of 35
examples accepted by the core                23 of 25
translator and driver tests (pytest)         243 passed in ...
...
RESULT: all 10 steps passed
```

For a shell in the image, with Isabelle, GHC and Python on the `PATH`:

```bash
docker run --rm -it --entrypoint bash triel-artifact
```

### The steps of run.sh

| Step | What it checks | CI workflow |
|---|---|---|
| 01-no-sorry | no `sorry`, `oops`, `axiomatization` in `formal/core/*.thy` and `artifact/isabelle/*.thy`; no `quick_and_dirty` or `skip_proofs` in the `ROOT` files | isabelle.yml |
| 02-isabelle-build | clean build of `TRIEL_Core` (`isabelle build -b -c -e -v -D formal/core`), which also exports the evaluator code | isabelle.yml, evaluator.yml |
| 03-exported-code | the exported code is identical to `evaluator/generated/` | evaluator.yml |
| 04-build-evaluator | GHC builds `evaluator/triel-eval` from the exported code and `Main.hs` | evaluator.yml |
| 05-classification | the translator classifies every example as in `examples/core/classification.expected` | evaluator.yml |
| 06-scenarios | every scenario gives exactly its `.expected` report | evaluator.yml |
| 07-pytest | the tests of the translator and the driver | evaluator.yml |
| 08-parse-examples | every example parses with exactly one derivation | parse-examples.yml |
| 09-ambiguity-tests | the ambiguity regression tests and the LALR(1) check of the grammar | parse-examples.yml |
| 10-paper-theorems | the session `TRIEL_Paper` builds: each of the 34 names is a theorem of `TRIEL_Core` that depends on no oracle | — |

As in CI, the PDF document of `TRIEL_Core` is switched off (it needs LaTeX):
step 02 applies the same `sed` to the scratch copy of `formal/core/ROOT` as the
CI workflows do. Proof checking is not affected.

The number of proved statements is counted by `artifact/count_statements.py`:
the commands `lemma`, `theorem` and `corollary` (and `proposition`,
`schematic_goal`, of which there are none) in `formal/core/*.thy`, outside
comments, quotations and text blocks.

## Claims of the paper

Every claim below is checked by `docker run --rm triel-artifact`. The commands
in the second column read the logs of a run with `RESULTS_DIR` (see Running).
Statements are printed in Isabelle's ASCII notation (`\<Longrightarrow>` is ⟹,
`\<sqsubseteq>` is ⊑); they are the statements in the theories, with schematic
variables `?x`.

| Claim | Command | Expected output |
|---|---|---|
| The core is machine-checked: 12 theories, 563 proved statements, no unproved or assumed results | `grep -E '^(theories\|proved)' results/summary.txt`; `cat results/01-no-sorry.log` | `12 (.thy files in formal/core: 12)`, `563`; `no sorry, oops or axiomatization ...` |
| The evaluator is the code exported from the checked theories | `cat results/03-exported-code.log` | `evaluator/generated is the exported code` |
| The evaluator gives the expected report on every scenario | `grep -c '^ok ' results/06-scenarios.log` | `35` |
| 23 of the 25 example specifications are inside the core | `grep -c ': ACCEPTED$' results/classification.txt`; `grep REJECTED results/classification.txt` | `23`; `execute_renaming.triel: REJECTED: EXECUTE` and `prohibition_continuation.triel: REJECTED: §2.6 defines continuations only for obligations` |
| Every cited theorem exists under its name and depends on no oracle | `tail -1 results/paper_theorems.txt` | `Paper theorems without oracles: 34` |
| Finality of verdicts: a definite verdict of an obligation, a prohibition or an invariant does not change when the trace is extended | `grep -A1 -E '\.(ob_verdict_final\|pr_verdict_final\|inv_final)$' results/paper_theorems.txt` | `TRIEL_Breach.ob_verdict_final`, `TRIEL_Breach.pr_verdict_final`, `TRIEL_Invariants.inv_final`, each with its statement, e.g. `inv_eval ?\<iota> ?\<pi> = Some ?b \<Longrightarrow> inv_eval ?\<iota> (?\<pi> @ ?\<rho>) = Some ?b` |
| Stability of verdicts under extension of the data, for conditions built from equitone atoms | `grep -A1 -E '\.(verdict_stable\|verdict_stable_nd\|cond_equitone)$' results/paper_theorems.txt` | `TRIEL_Indicators.verdict_stable`, `TRIEL_Indicators.verdict_stable_nd`, `TRIEL_Indicators.cond_equitone` with their statements |
| PRESENT, E and DEFAULT are the exceptions: each breaks monotonicity or stability | `grep -A1 -E '\.(T3_present_not_monotone\|Ex_breaks_stability\|T3_default_not_monotone\|default_breaks_stability\|T5_present)$' results/paper_theorems.txt` | the five theorems with their statements, e.g. `\<exists>\<sigma> \<sigma>' x. \<sigma> \<sqsubseteq> \<sigma>' \<and> eval (EPresent x) \<sigma> \<noteq> eval (EPresent x) \<sigma>'` |
| IF: denotation, classical reading when the data is complete, stability of the branch; UNLESS distributes over IF | `grep -A1 -E '\.(den_if\|if_classical\|if_branch_stable\|unless_if)$' results/paper_theorems.txt` | `TRIEL_Terms.term_semantics.den_if`, `...if_classical`, `...if_branch_stable`, `TRIEL_Trace.unless_if` with their statements |
| References between the elements of a block are acyclic, and resolving them preserves the denotation | `grep -A1 -E '\.(resolve_den\|block_den\|refs_ok_acyclic)$' results/paper_theorems.txt` | `TRIEL_Exec.term_semantics.resolve_den`, `TRIEL_Exec.term_semantics.block_den`, `TRIEL_Exec.refs_ok_acyclic` with their statements |
| An undefined guard does not make a prohibition breached | `grep -A2 -E '\.(undefined_guard_blocks_not_breach\|enforced_no_breach)$' results/paper_theorems.txt` | `TRIEL_Breach.undefined_guard_blocks_not_breach` (two conclusions), `TRIEL_Breach.enforced_no_breach` |
| Conditions are terms of the composition algebra, and equitonicity follows from closure under the base compositions | `grep -A1 -E '\.(comp_closure_equitone\|interp_equitone\|cond_fm_correct\|cond_equitone_from_closure\|Ex_R_is_not_eps)$' results/paper_theorems.txt` | the five theorems of `TRIEL_Compositions` with their statements |
| A missed deadline with ELSE puts the fallback in force instead of a breach; the verdict is final | `grep -A1 -E '\.else_(taken\|no_breach\|alt_breached\|final)$' results/paper_theorems.txt` | `TRIEL_Breach.else_taken`, `...else_no_breach`, `...else_alt_breached`, `...else_final` with their statements |
| Hidden data does not influence the report (noninterference) | `grep -A1 -E '\.(run_noninterference\|run_erase\|erase_flat\|flow_safe_eval\|flow_safe_evalV)$' results/paper_theorems.txt` | `TRIEL_Exec.run_noninterference`, e.g. `erase_obs (hidden ?fs) ?obs = erase_obs (hidden ?fs) ?obs' \<Longrightarrow> run (Spec ?fs ?blk ?invs) ?obs = run (Spec ?fs ?blk ?invs) ?obs'`, and the other four |

`artifact/isabelle/Paper_Theorems.thy` names each theorem with its theory
(`TRIEL_Breach.ob_verdict_final`). Theorems proved inside the locale
`term_semantics` carry the locale name too (`TRIEL_Terms.term_semantics.den_if`),
and their statements have the locale predicate `term_semantics ?interleave` as
a premise. If a name is renamed or removed in `formal/core`, `thm` fails and
so does the build of `TRIEL_Paper`. The ML block at the end of the theory
checks with `Thm_Deps.all_oracles` that no listed theorem depends on an oracle
(an unfinished proof would show up as the oracle `Pure.skip_proof`).

## Trusted base

The results rest on the following, which are not proved here:

- **Isabelle2025-2**: the kernel of Isabelle/HOL and Poly/ML. This is the
  usual trusted base of an Isabelle development.
- **Code export**: Isabelle's code generator, which turns the definitions of
  `TRIEL_Exec.thy` into `evaluator/generated/TRIEL.hs`. The correspondence of
  the Haskell code to the HOL definitions is the code generator's, not a theorem
  of this development.
- **GHC 9.6.7** and its runtime, which build and run the evaluator.
- **`evaluator/Main.hs`** (hand-written, 400 lines): reads the input
  S-expression and prints the report. Every verdict is computed by the exported
  function `run`, but the reading and the printing are not proved.
- **`parser/triel_to_core.py` is not proved.** It is the translator from TRIEL
  specifications to terms of the core, written in Python. Nothing proves that it
  translates a specification into the core term with the intended meaning, or
  that it rejects exactly the constructs outside the core. It is checked only
  by tests: the 243 tests of `parser/test_triel_to_core.py`, the classification
  of the 25 examples, and the 35 scenarios. The same holds for
  `parser/triel_eval.py`, which converts a scenario into the input of the
  evaluator, and for the grammar `parser/triel.lark` with the parser library
  lark 1.3.1.
- **The expected outputs** (`examples/core/classification.expected` and the
  `.expected` files of the scenarios) are written by hand. A scenario passes
  when the evaluator agrees with them.
- **The counting in the summary**: `artifact/count_statements.py` counts the
  statement commands syntactically. The number of theories is read from the
  build log of Isabelle.

## Working without a network

Building the image needs a network; running it does not. To move the image to
a machine without a network:

```bash
docker save triel-artifact | gzip > triel-artifact.tar.gz     # on a machine with network
docker load < triel-artifact.tar.gz                           # on the offline machine
docker run --rm --network none triel-artifact
```

The compressed file is about 3.1 GB. `--network none` shows that the run uses
no network.

## Versions

Both base images are pinned by digest in `artifact/Dockerfile`:

- `makarius/isabelle:Isabelle2025-2` (Ubuntu 24.04, Isabelle2025-2 with the HOL
  heap), which also provides Python 3.12.3;
- `haskell:9.6.7-slim`, from which only GHC 9.6.7 (`/opt/ghc/9.6.7`) is
  copied.

The Python packages are installed from `artifact/requirements.txt` with
`--require-hashes`: lark 1.3.1 (as in CI), pytest 9.1.1 and its dependencies.
The Ubuntu packages (C toolchain and libraries for GHC, `python3-venv`) come
from the Ubuntu 24.04 archive at build time and are not pinned.

## Anonymous archive

`artifact/anonymize.sh WORDS_FILE [OUTPUT.tar.gz]` writes a source archive of
the current commit for double-blind review, without `.git`, the contributor
license agreement and its workflow, and with every word listed in `WORDS_FILE`
replaced. It fails, and writes nothing, if any listed word is left in a file
or a file name. The list of words is kept outside the repository.
