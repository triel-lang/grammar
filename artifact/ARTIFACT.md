# Artifact: the TRIEL 2.5.1 core in Isabelle/HOL

## What this is

This artifact reproduces the machine-checked results and the executable checks
behind the paper. It contains:

- `formal/core/`: the core of TRIEL 2.5.1 (the errata to 2.5) in Isabelle/HOL, 12 theories (session
  `TRIEL_Core`). All theorems are proved; there is no `sorry`, `oops` or
  `axiomatization`.
- `evaluator/`: an evaluator of the core. Its Haskell code
  (`evaluator/generated/TRIEL.hs`) is exported by Isabelle from
  `formal/core/TRIEL_Exec.thy`; `evaluator/Main.hs` only reads the input and
  prints the report.
- `parser/`: the reference parser of TRIEL 2.5, and the translator
  `parser/triel_to_core.py` from TRIEL specifications to terms of the core.
- `examples/`: 27 TRIEL specifications and 47 scenarios (implementation traces
  with hand-written expected reports).
- `artifact/`: the Docker image (`Dockerfile`), the script that runs every check
  (`run.sh`), and the Isabelle session `TRIEL_Paper`
  (`isabelle/Paper_Theorems.thy`), which lists by name the 52 theorems cited in
  the paper.

`artifact/run.sh` runs, in one command, every check of the repository's CI
(`isabelle.yml`, `evaluator.yml`, `parse-examples.yml`), builds `TRIEL_Paper`,
and prints a summary whose numbers are all computed by the run.

## Requirements

- x86-64 Linux host (or any Docker host that runs `linux/amd64` images) with
  Docker 20.10 or later.
- CPU: 4 cores recommended; Isabelle uses up to 4 threads.
- Memory: 10 GB. The memory peak is the clean Isabelle build of `TRIEL_Core`
  with 4 threads (Poly/ML and the Isabelle/Scala process): the memory charged
  to the container (its cgroup, page cache included) reached 8.2 GiB in a run
  without a limit. With the container limited to 10 GiB (`--memory=10g`) the
  build passed in each of three runs, with peaks of 7.0 to 7.8 GiB; at 8 GiB it
  was killed for lack of memory in two of four runs. All other steps stay
  below 2 GiB.
- Docker Desktop (macOS, Windows): set Memory to at least 10 GB in
  Settings → Resources.
- Disk: 10 GB for the image (3.1 GB compressed download, the same size for
  `docker save | gzip`), and about 0.2 GB inside the container for a run.
- Network: only to build the image (base images, Ubuntu packages and Python
  wheels). Running the image needs no network; the measured run used
  `--network none`.

Measured on a 4-core x86-64 virtual machine with 16 GB of memory:

| Phase | Time |
|---|---|
| Download of the two base images | 2 min |
| Image build (`docker build`), without cache | 3 min |
| `run.sh`, all 11 steps | 18 min |
| of which: clean Isabelle build of `TRIEL_Core` | 2 min |
| of which: 47 scenarios | 3 min |
| of which: translator and driver tests (pytest) | 7.5 min |
| of which: parsing of the 27 examples with the ambiguity check | 3.5 min |
| of which: ambiguity regression tests | 2 min |
| of which: excerpts of the documents | 11 s |
| of which: session `TRIEL_Paper` (on the heap of `TRIEL_Core`) | 10 s |

The times of `run.sh` are those of version 2.5.1; the download and the image
build were measured for version 2.5, with the same `Dockerfile`. On a
GitHub-hosted runner (`ubuntu-latest`, workflow `.github/workflows/artifact.yml`)
the image of version 2.5 built in 1.5 min, base images included, and `run.sh`
took 10 min in one run and 16.5 min in another.

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
proved statements (lemma/theorem/corollary)  633
paper theorems found, without oracles        52 of 52
scenarios matching .expected                 47 of 47
examples accepted by the core                25 of 27
translator and driver tests (pytest)         305 passed in ...
examples parsed with one derivation          27 of 27
ambiguity regression checks passed           235
document excerpts conforming to the grammar  15
wall-clock time                              ...
...
RESULT: all 11 steps passed
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
| 10-document-excerpts | every TRIEL excerpt of the documents, every grammar excerpt of `TECHNICAL_REPORT.md` and every usage example of the grammar file conforms to the grammar | parse-examples.yml |
| 11-paper-theorems | the session `TRIEL_Paper` builds: each of the 52 names is a theorem of `TRIEL_Core` that depends on no oracle | — |

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
| The core is machine-checked: 12 theories, 633 proved statements, no unproved or assumed results | `grep -E '^(theories\|proved)' results/summary.txt`; `cat results/01-no-sorry.log` | `12 (.thy files in formal/core: 12)`, `633`; `no sorry, oops or axiomatization ...` |
| The evaluator is the code exported from the checked theories | `cat results/03-exported-code.log` | `evaluator/generated is the exported code` |
| The evaluator gives the expected report on every scenario | `grep -c '^ok ' results/06-scenarios.log` | `47` |
| 25 of the 27 example specifications are inside the core | `grep -c ': ACCEPTED$' results/classification.txt`; `grep REJECTED results/classification.txt` | `25`; `execute_renaming.triel: REJECTED: EXECUTE` and `prohibition_continuation.triel: REJECTED: §2.6 defines continuations only for obligations` |
| Every cited theorem exists under its name and depends on no oracle | `tail -1 results/paper_theorems.txt` | `Paper theorems without oracles: 52` |
| Finality of verdicts: on a trace (times that do not decrease) a definite verdict of an obligation, a prohibition or an invariant does not change when the trace is extended; the evaluator rejects a list of observations whose times decrease, so for `run` a decided line stays the same when observations are appended, unless the longer list is rejected for its time order or its types. A property of the design | `grep -A1 -E '\.(ob_verdict_final\|pr_verdict_final\|inv_final\|run_final\|time_order_rejected)$' results/paper_theorems.txt` | `TRIEL_Breach.ob_verdict_final`, `TRIEL_Breach.pr_verdict_final`, `TRIEL_Invariants.inv_final`, `TRIEL_Exec.run_final`, `TRIEL_Exec.time_order_rejected`, each with its statement, e.g. `inv_eval ?\<iota> ?\<pi> = Some ?b \<Longrightarrow> inv_eval ?\<iota> (?\<pi> @ ?\<rho>) = Some ?b` |
| Two obligations in sequence need two actions; a prohibition in a composite term can be violated, and its trace semantics agrees with its verdict; the status of a composite term (read on the first prefix that violates the term or completes it by an executed action; conservative when a prefix has several readings) is sound and final, Violated before Done is needed, and the modes of the traces refine the denotation; for a term without AND, a violated prefix is reported as a violation at that entry or before it unless the status is unknown or the observation ended earlier on a completion by an executed action before any reading had reached a prohibition, and the exception for an earlier completion cannot be dropped; consequences for a prohibition after a reading has reached one, at the end of a sequence (no exception when the first part has no UNLESS and no AND) and in a branch of OR (no exception but an unknown status) | `grep -A1 -E '\.(must_then_must_two_actions\|violated_reachable\|then_mustnot_violated\|mustnot_violated_breach\|breach_mustnot_violated\|status_final\|status_sound\|violation_over_done\|fden_den\|then_mustnot_held\|then_mustnot_status\|status_no_missed_violation\|reached_prohibition_watched\|then_mustnot_watched\|or_mustnot_watched\|violation_after_completion)$' results/paper_theorems.txt` | the sixteen theorems with their statements |
| Stability of the values of conditions: a definite value T or F of a condition built from equitone atoms does not change when the data is extended. This is about conditions, not about the verdicts of norms over time | `grep -A1 -E '\.(verdict_stable\|verdict_stable_nd\|cond_equitone)$' results/paper_theorems.txt` | `TRIEL_Indicators.verdict_stable`, `TRIEL_Indicators.verdict_stable_nd`, `TRIEL_Indicators.cond_equitone` with their statements |
| PRESENT, E and DEFAULT are the exceptions: each breaks monotonicity or stability | `grep -A1 -E '\.(T3_present_not_monotone\|Ex_breaks_stability\|T3_default_not_monotone\|default_breaks_stability\|T5_present)$' results/paper_theorems.txt` | the five theorems with their statements, e.g. `\<exists>\<sigma> \<sigma>' x. \<sigma> \<sqsubseteq> \<sigma>' \<and> eval (EPresent x) \<sigma> \<noteq> eval (EPresent x) \<sigma>'` |
| IF: denotation, classical reading when the data is complete, stability of the branch; UNLESS distributes over IF | `grep -A1 -E '\.(den_if\|if_classical\|if_branch_stable\|unless_if)$' results/paper_theorems.txt` | `TRIEL_Terms.term_semantics.den_if`, `...if_classical`, `...if_branch_stable`, `TRIEL_Trace.unless_if` with their statements |
| References between the elements of a block are acyclic, and resolving them preserves the denotation | `grep -A1 -E '\.(resolve_den\|block_den\|refs_ok_acyclic)$' results/paper_theorems.txt` | `TRIEL_Exec.term_semantics.resolve_den`, `TRIEL_Exec.term_semantics.block_den`, `TRIEL_Exec.refs_ok_acyclic` with their statements |
| An undefined guard does not make a prohibition breached | `grep -A2 -E '\.(undefined_guard_blocks_not_breach\|enforced_no_breach)$' results/paper_theorems.txt` | `TRIEL_Breach.undefined_guard_blocks_not_breach` (two conclusions), `TRIEL_Breach.enforced_no_breach` |
| Conditions are terms of the composition algebra, and equitonicity follows from closure under the base compositions | `grep -A1 -E '\.(comp_closure_equitone\|interp_equitone\|cond_fm_correct\|cond_equitone_from_closure\|Ex_R_is_not_eps)$' results/paper_theorems.txt` | the five theorems of `TRIEL_Compositions` with their statements |
| A missed deadline with ELSE puts the fallback in force instead of a breach; the verdict is final | `grep -A1 -E '\.else_(taken\|no_breach\|alt_breached\|final)$' results/paper_theorems.txt` | `TRIEL_Breach.else_taken`, `...else_no_breach`, `...else_alt_breached`, `...else_final` with their statements |
| Hidden data does not influence the report (noninterference). A property of the design: the evaluator removes the hidden factors before it reads anything | `grep -A1 -E '\.(run_noninterference\|run_erase\|erase_flat\|flow_safe_eval\|flow_safe_evalV)$' results/paper_theorems.txt` | `TRIEL_Exec.run_noninterference`, e.g. `erase_obs (hidden ?fs) ?obs = erase_obs (hidden ?fs) ?obs' \<Longrightarrow> run (Spec ?fs ?blk ?invs) ?obs = run (Spec ?fs ?blk ?invs) ?obs'`, and the other four |

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
  by tests: the 305 tests of `parser/test_triel_to_core.py`, the classification
  of the 27 examples, and the 47 scenarios. The same holds for
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

The compressed file is about 3.1 GB. With `--network none` the container has
no network at all; the run passes.

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

`artifact/anonymize.sh [-w WORDS_FILE] [OUTPUT.tar.gz]` writes a source archive
of the current commit for double-blind review. It leaves out `.git`, the
contributor license agreement with its workflow, and the script itself. The
name of the author is found without a list of words: the script reads it from
the places where the repository states it (`formal/core/document/root.tex`,
`NOTICE`, `LICENSE.md`, the headers of both EBNF files and the Contact section
of `README.md`) and replaces it, and each of its words, everywhere. The address
of the repository and of the project's sites are replaced too, and so is every
word listed in the optional `WORDS_FILE`, which is kept outside the repository.
Text that points to the history of the project is rewritten as well: the commit
hash of the tag v2.5 in `LICENSE.md` is removed, and the stages of the
development named in `formal/core/CORE.md` ("the independent review of stage 13")
become "an independent review" or "an earlier revision". The name of the
language is kept. The script fails, and writes nothing, if any of these words,
the hash or a stage is left in a file or a file name, or if `root.tex` or
`NOTICE` names no author.
