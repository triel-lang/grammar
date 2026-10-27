# Artifact: the TRIEL 2.5.1 core in Isabelle/HOL

## What this is

This artifact reproduces the machine-checked results and the executable checks
behind the paper. It contains:

- `formal/core/`: the core of TRIEL 2.5.1 (the errata to 2.5) in Isabelle/HOL, 13 theories (session
  `TRIEL_Core`). All theorems are proved; there is no `sorry`, `oops` or
  `axiomatization`.
- `evaluator/`: an evaluator of the core. Its Haskell code
  (`evaluator/generated/TRIEL.hs`) is exported by Isabelle from
  `formal/core/TRIEL_Exec.thy`; `evaluator/Main.hs` only reads the input and
  prints the report.
- `parser/`: the reference parser of the TRIEL 2.5 grammar (which 2.5.1 does
  not change), and the translator
  `parser/triel_to_core.py` from TRIEL specifications to terms of the core.
- `examples/`: 28 TRIEL specifications and 54 scenarios (implementation traces
  with hand-written expected reports).
- `artifact/`: the Docker image (`Dockerfile`), the script that runs every check
  (`run.sh`), and the Isabelle session `TRIEL_Paper`
  (`isabelle/Paper_Theorems.thy`), which lists by name the 57 theorems cited in
  the paper; and `bench.sh`, which measures the time and the memory of the
  translation of a trace and of the evaluator on generated traces (not a step
  of `run.sh`).

`artifact/run.sh` runs, in one command, every check of the repository's CI
(`isabelle.yml`, `evaluator.yml`, `parse-examples.yml`), builds `TRIEL_Paper`,
and prints a summary whose numbers are all computed by the run.

## Requirements

- x86-64 Linux host (or any Docker host that runs `linux/amd64` images) with
  Docker 20.10 or later.
- CPU: 4 cores recommended; Isabelle uses up to 4 threads.
- Memory: 10 GB. The memory peak is the clean Isabelle build of `TRIEL_Core`
  (Poly/ML and the Isabelle/Scala process); the memory measured is that charged
  to the container (its cgroup, page cache included). With Isabelle2025-2 using
  4 threads, for version 2.5.1 on a 4-core machine with 16 GB, it reached 8.2
  GiB in a run without a limit; with the container limited to 10 GiB
  (`--memory=10g`) the build passed in each of three runs, with peaks of 7.0 to
  7.8 GiB; at 8 GiB it was killed for lack of memory in two of four runs. All
  other steps stay below 2 GiB. On GitHub-hosted runners (4 cores, 15.6 GiB)
  without a limit, where Isabelle2025-2 used 2 threads (as the build logs
  state), the workflow `.github/workflows/artifact.yml` read peaks from 6.73 to
  7.15 GiB in the thirteen runs listed under "Times on GitHub-hosted runners"
  below; it keeps the value as `memory-peak.txt` with the logs of the run.
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
| `run.sh`, all 11 steps | 21 min |
| of which: clean Isabelle build of `TRIEL_Core` | 2 min |
| of which: the scenarios | 3.5 min |
| of which: translator and driver tests (pytest) | 8.5 min |
| of which: parsing of the examples with the ambiguity check | 4 min |
| of which: ambiguity regression tests | 2 min |
| of which: excerpts of the documents | 14 s |
| of which: session `TRIEL_Paper` (on the heap of `TRIEL_Core`) | 12 s |

The times of `run.sh` in the table are those of version 2.5.1 (47 scenarios, 27
examples), measured with the container limited to 10 GiB; the download and the
image build were measured for version 2.5, with the same `Dockerfile`.

### Times on GitHub-hosted runners

The job `artifact` of `.github/workflows/artifact.yml` builds the image and
runs `run.sh` on every push, on a GitHub-hosted runner (the label
`ubuntu-latest` in #56 to #59, `ubuntu-24.04` from #60), and reads the memory
peak of the container. The thirteen runs
below are those, from the first run that read the memory peak (#56) to the
run #71 of this version, in which `run.sh` passed all 11 steps; all of them
are of sources with 28 examples and 54 scenarios. Over these runs:

| Phase | Range over the thirteen runs |
|---|---|
| Job `artifact` (disk clean-up, image build and `run.sh`) | 16:14 to 23:39 min |
| Image build (`docker build`, base images included) | 1:14 to 2:18 min |
| `run.sh`, all 11 steps | 766 to 1214 s (12.8 to 20.2 min) |
| of which: clean Isabelle build of `TRIEL_Core` | 85 to 130 s |
| of which: the scenarios | 124 to 210 s |
| of which: translator and driver tests (pytest) | 318 to 518 s |
| of which: parsing of the examples with the ambiguity check | 123 to 217 s |
| of which: ambiguity regression tests | 80 to 118 s |
| Memory peak of the container | 6.73 to 7.15 GiB |

| Run | Date (UTC) | Theories | Job `artifact` | Image build | `run.sh` | Memory peak |
|---|---|---:|---:|---:|---:|---:|
| #56 | 2026-10-26 | 12 | 23:26 | 2:18 | 1175 s | 6.94 GiB |
| #57 | 2026-10-26 | 12 | 23:29 | 2:13 | 1213 s | 7.15 GiB |
| #58 | 2026-10-26 | 12 | 23:05 | 2:06 | 1202 s | 7.03 GiB |
| #59 | 2026-10-26 | 12 | 23:39 | 2:08 | 1186 s | 6.95 GiB |
| #60 | 2026-10-27 | 12 | 20:59 | 1:14 | 1141 s | 6.91 GiB |
| #61 | 2026-10-27 | 12 | 16:14 | 1:38 | 766 s | 6.93 GiB |
| #62 | 2026-10-27 | 12 | 21:17 | 1:15 | 1156 s | 7.02 GiB |
| #63 | 2026-10-27 | 12 | 22:34 | 1:14 | 1214 s | 7.05 GiB |
| #67 | 2026-10-27 | 13 | 19:53 | 1:42 | 931 s | 6.95 GiB |
| #68 | 2026-10-27 | 13 | 22:53 | 1:18 | 1201 s | 7.04 GiB |
| #69 | 2026-10-27 | 13 | 19:03 | 1:48 | 951 s | 6.74 GiB |
| #70 | 2026-10-27 | 13 | 18:42 | 1:44 | 889 s | 7.12 GiB |
| #71 | 2026-10-27 | 13 | 21:30 | 1:45 | 1054 s | 6.73 GiB |

Runs #61 to #63 are of the same commit; #67 to #71 are of this version, with
the new theory (#68 and #69 of one tree, #70 and #71 of another, which differ
from it in documentation and in the checks of the anonymous archive). In the runs #64 to #66 of drafts of this version, `run.sh` failed in
the step pytest: the test that every name in backquotes in `CORE.md` is defined
in the theories failed on the name of a file, since corrected; they are not in
the table. The time on a shared
runner varies from run to run, and so does its CPU.

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
theories checked by Isabelle (TRIEL_Core)    13 (.thy files in formal/core: 13)
proved statements (lemma/theorem/corollary)  646
paper theorems found, without oracles        57 of 57
scenarios matching .expected                 54 of 54
examples accepted by the core                26 of 28
translator and driver tests (pytest)         319 passed in ...
examples parsed with one derivation          28 of 28
ambiguity regression checks passed           237
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
| 11-paper-theorems | the session `TRIEL_Paper` builds: each of the 57 names is a theorem of `TRIEL_Core` that depends on no oracle | — |

As in CI, the PDF document of `TRIEL_Core` is switched off (it needs LaTeX):
step 02 applies the same `sed` to the scratch copy of `formal/core/ROOT` as the
CI workflows do. Proof checking is not affected.

The number of proved statements is counted by `artifact/count_statements.py`:
the commands `lemma`, `theorem` and `corollary` (and `proposition`,
`schematic_goal`, of which there are none) in `formal/core/*.thy`, outside
comments, quotations and text blocks.

## Speed of the translation and of the evaluator: bench.sh

`artifact/bench.sh` measures, on generated traces of growing length, the time
and the memory of the two programs that check a trace. It is not a step of
`run.sh`. In the image:

```bash
mkdir -p bench-results && chmod 777 bench-results
docker run --rm -e RESULTS_DIR=/results -v "$PWD/bench-results:/results" \
  --entrypoint artifact/bench.sh triel-artifact
```

- **Traces.** `artifact/bench_trace.py` writes, with the fixed seed 20261027,
  scenarios of 10^2, 10^3, 10^4, 10^5 and 10^6 entries for
  `examples/core/core_invoice_agent.triel` and for
  `examples/core/core_sequence.triel`, whose three terms are composite; the
  file describes what the entries contain. The traces are written to a scratch
  directory and removed, never committed; `traces.sha256` lists their SHA-256.
- **Two phases, measured apart.** *translate* is
  `python3 parser/triel_eval.py SCENARIO --input`: Python starts, the
  specification is parsed (lark) and translated (`triel_to_core.py`), both once
  whatever the length of the trace, and the scenario is read and the input of
  the evaluator written to a file. *evaluate* is `evaluator/triel-eval` on that
  file.
- **Statistics.** Each point is run 5 times: the median, the minimum and the
  maximum of the wall-clock times, and as peak memory the largest "Maximum
  resident set size" that `/usr/bin/time -v` reports over the runs.
- **Limit.** Every run is started under `timeout 120` (`timeout 60` from 10^6
  entries). A point that does not finish is reported as `timeout`, with no
  time, and all longer traces of that example are skipped (`skipped`) in both
  phases.
- **Output** in `RESULTS_DIR`: `bench.csv`, `bench.md` (the same as a Markdown
  table), `runs.csv` (every run), `machine.txt` (CPU, cores, memory, kernel,
  GHC, Python, lark), `traces.sha256` and the reports of the evaluator. The job
  `bench` of `.github/workflows/artifact.yml` runs it in the same image on every
  push, on a runner of its own, and keeps the results as the artifact
  `bench-results` of the run.

Results of the job `bench` in the six runs #66 to #71 of the workflow
(2026-10-27), on GitHub-hosted runners with 4 cores and 15.6 GiB: an AMD EPYC
7763 in #66 and #71, an AMD EPYC 9V74 in #67 and #70, an AMD EPYC 9V45 in #68
and #69; GHC 9.6.7, Python 3.12.3, lark 1.3.1. The runs #68 to #71 printed the
same `traces.sha256`; #66 and #67 ran the same `bench_trace.py` with the same
seed, before `bench.sh` printed the hashes. For each point the table gives the
median of its 5 runs as a range over the six CI runs, the minimum and maximum
of all 30 runs, and the peak memory:

| Example | Entries | Phase | Median, s | All runs, s | Peak memory, MiB |
|---|---:|---|---:|---:|---:|
| core_invoice_agent | 10^2 | translate | 2.19–3.98 | 2.16–4.08 | 52.0–52.2 |
| core_invoice_agent | 10^2 | evaluate | 0.012–0.014 | 0.012–0.015 | 9.2–9.5 |
| core_invoice_agent | 10^3 | translate | 2.24–3.98 | 2.19–4.02 | 56.5–56.9 |
| core_invoice_agent | 10^3 | evaluate | 0.093–0.174 | 0.093–0.185 | 15.7–15.9 |
| core_invoice_agent | 10^4 | translate | 2.73–4.75 | 2.67–4.81 | 92.1–92.3 |
| core_invoice_agent | 10^4 | evaluate | timeout (120 s) in all six | | |
| core_invoice_agent | 10^5, 10^6 | both | skipped | | |
| core_sequence | 10^2 | translate | 2.05–3.86 | 2.01–3.96 | 49.4–50.1 |
| core_sequence | 10^2 | evaluate | 0.022–0.053 | 0.022–0.063 | 10.0–10.2 |
| core_sequence | 10^3 | translate | 2.09–3.93 | 2.02–3.96 | 53.2–53.4 |
| core_sequence | 10^3 | evaluate | 13.0–28.6 | 12.5–29.1 | 12.7–12.9 |
| core_sequence | 10^4 | translate | 2.37–4.40 | 2.31–4.41 | 72.7–72.9 |
| core_sequence | 10^4 | evaluate | timeout (120 s) in all six | | |
| core_sequence | 10^5, 10^6 | both | skipped | | |

What these measurements show, and nothing beyond them:

- **On these traces, the time of the evaluator grows faster than linearly
  with their length.** For `core_invoice_agent`, ten times more entries took
  7.2 to 13.4 times longer from 10^2 to 10^3 entries (the ratio of the medians
  within each CI run; at 10^2 entries the medians are only 12 to 14 ms, so the
  ratio is coarse), and the trace of 10^4 entries did not finish within 120 s, more
  than 689 times the largest median at 10^3. For `core_sequence`, from 10^2 to
  10^3 entries the median grew 403 to 655 times within each CI run, and 10^4
  entries did not finish within 120 s. So no trace of 10^5 or 10^6 entries was
  run, and there is no time for them. The evaluator is not changed here.
- The peak memory of the evaluator stayed below 16 MiB up to 10^3 entries.
  `runs.csv` also records the memory a run had reached when it timed out.
- The translation took 2.0 to 4.8 s per run at every length measured, 10^2 to
  10^4 entries, already 2.0 to 4.1 s at 10^2; its peak memory grew from about
  50 MiB to 92 MiB.
- Between runners the medians differ by a factor of up to 1.9 (translation)
  and 2.4 (evaluation; 2.2 at 10^3 entries): the absolute times depend on the
  machine.

## Claims of the paper

Every claim below is checked by `docker run --rm triel-artifact`. The commands
in the second column read the logs of a run with `RESULTS_DIR` (see Running).
Statements are printed in Isabelle's ASCII notation (`\<Longrightarrow>` is ⟹,
`\<sqsubseteq>` is ⊑); they are the statements in the theories, with schematic
variables `?x`.

| Claim | Command | Expected output |
|---|---|---|
| The core is machine-checked: 13 theories, 646 proved statements, no unproved or assumed results | `grep -E '^(theories\|proved)' results/summary.txt`; `cat results/01-no-sorry.log` | `13 (.thy files in formal/core: 13)`, `646`; `no sorry, oops or axiomatization ...` |
| The evaluator is the code exported from the checked theories | `cat results/03-exported-code.log` | `evaluator/generated is the exported code` |
| The evaluator gives the expected report on every scenario | `grep -c '^ok ' results/06-scenarios.log` | `54` |
| 26 of the 28 example specifications are inside the core | `grep -c ': ACCEPTED$' results/classification.txt`; `grep REJECTED results/classification.txt` | `26`; `execute_renaming.triel: REJECTED: EXECUTE` and `prohibition_continuation.triel: REJECTED: §2.6 defines continuations only for obligations` |
| Every cited theorem exists under its name and depends on no oracle | `tail -1 results/paper_theorems.txt` | `Paper theorems without oracles: 57` |
| Finality of verdicts: on a trace (times that do not decrease) a definite verdict of an obligation, a prohibition or an invariant does not change when the trace is extended; the evaluator rejects a list of observations whose times decrease, so for `run` a decided line stays the same when observations are appended, unless the longer list is rejected for its time order or its types. A property of the design | `grep -A1 -E '\.(ob_verdict_final\|pr_verdict_final\|inv_final\|run_final\|time_order_rejected)$' results/paper_theorems.txt` | `TRIEL_Breach.ob_verdict_final`, `TRIEL_Breach.pr_verdict_final`, `TRIEL_Invariants.inv_final`, `TRIEL_Exec.run_final`, `TRIEL_Exec.time_order_rejected`, each with its statement, e.g. `inv_eval ?\<iota> ?\<pi> = Some ?b \<Longrightarrow> inv_eval ?\<iota> (?\<pi> @ ?\<rho>) = Some ?b` |
| Two obligations in sequence need two actions; a prohibition in a composite term can be violated, and its trace semantics agrees with its verdict; the status of a composite term (read on the first prefix that violates the term or completes it by an executed action; conservative when a prefix has several readings) is sound and final, Violated before Done is needed, and the modes of the traces refine the denotation; for a term without AND, a violated prefix is reported as a violation at that entry or before it unless the status is unknown or the observation ended earlier on a completion by an executed action before any reading had reached a prohibition, and the exception for an earlier completion cannot be dropped; consequences for a prohibition after a reading has reached one, at the end of a sequence (no exception when the first part has no UNLESS and no AND) and in a branch of OR (no exception but an unknown status) | `grep -A1 -E '\.(must_then_must_two_actions\|violated_reachable\|then_mustnot_violated\|mustnot_violated_breach\|breach_mustnot_violated\|status_final\|status_sound\|violation_over_done\|fden_den\|then_mustnot_held\|then_mustnot_status\|status_no_missed_violation\|reached_prohibition_watched\|then_mustnot_watched\|or_mustnot_watched\|violation_after_completion)$' results/paper_theorems.txt` | the sixteen theorems with their statements |
| Stability of the values of conditions: a definite value T or F of a condition built from equitone atoms does not change when the data is extended. This is about conditions, not about the verdicts of norms over time | `grep -A1 -E '\.(verdict_stable\|verdict_stable_nd\|cond_equitone)$' results/paper_theorems.txt` | `TRIEL_Indicators.verdict_stable`, `TRIEL_Indicators.verdict_stable_nd`, `TRIEL_Indicators.cond_equitone` with their statements |
| PRESENT, E and DEFAULT are the exceptions: each breaks monotonicity or stability | `grep -A1 -E '\.(T3_present_not_monotone\|Ex_breaks_stability\|T3_default_not_monotone\|default_breaks_stability\|T5_present)$' results/paper_theorems.txt` | the five theorems with their statements, e.g. `\<exists>\<sigma> \<sigma>' x. \<sigma> \<sqsubseteq> \<sigma>' \<and> eval (EPresent x) \<sigma> \<noteq> eval (EPresent x) \<sigma>'` |
| IF: denotation, classical reading when the data is complete, stability of the branch; UNLESS distributes over IF | `grep -A1 -E '\.(den_if\|if_classical\|if_branch_stable\|unless_if)$' results/paper_theorems.txt` | `TRIEL_Terms.term_semantics.den_if`, `...if_classical`, `...if_branch_stable`, `TRIEL_Trace.unless_if` with their statements |
| References between the elements of a block are acyclic, and resolving them preserves the denotation | `grep -A1 -E '\.(resolve_den\|block_den\|refs_ok_acyclic)$' results/paper_theorems.txt` | `TRIEL_Exec.term_semantics.resolve_den`, `TRIEL_Exec.term_semantics.block_den`, `TRIEL_Exec.refs_ok_acyclic` with their statements |
| An undefined guard does not make a prohibition breached | `grep -A2 -E '\.(undefined_guard_blocks_not_breach\|enforced_no_breach)$' results/paper_theorems.txt` | `TRIEL_Breach.undefined_guard_blocks_not_breach` (two conclusions), `TRIEL_Breach.enforced_no_breach` |
| Completions of the data (a completion is a total valuation that agrees with the state wherever the state is defined): for a condition without PRESENT and DEFAULT, if the fail-closed monitor does not block, the condition is false in every completion, and a true condition is true in every completion; allowing the action when the condition is not known to be true, or reading a comparison with an absent operand as false, can allow an action that the monitor blocks and whose condition is true in a completion; strong Kleene evaluation is not complete with respect to completions | `grep -A1 -E '\.(monitor_sound_completions\|breach_certain_completions\|skip_reading_unsound\|absent_false_unsound\|kleene_not_complete)$' results/paper_theorems.txt` | `TRIEL_Completions.monitor_sound_completions`, e.g. `\<lbrakk>present_free ?c; \<not> blocks ?c ?\<sigma>; completion ?\<sigma> ?\<sigma>'\<rbrakk> \<Longrightarrow> eval ?c ?\<sigma>' = Some False`, `...breach_certain_completions`, `...skip_reading_unsound`, `...absent_false_unsound`, `...kleene_not_complete` with their statements |
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
- **`evaluator/Main.hs`** (hand-written, 410 lines): reads the input
  S-expression and prints the report. Every verdict is computed by the exported
  function `run`, but the reading and the printing are not proved.
- **`parser/triel_to_core.py` is not proved.** It is the translator from TRIEL
  specifications to terms of the core, written in Python. Nothing proves that it
  translates a specification into the core term with the intended meaning, or
  that it rejects exactly the constructs outside the core. It is checked only
  by tests: the 319 tests of `parser/test_triel_to_core.py`, the classification
  of the 28 examples, and the 54 scenarios. The same holds for
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
The Ubuntu packages (C toolchain and libraries for GHC, `python3-venv`, and
`time`, the GNU time of `bench.sh`) come
from the Ubuntu 24.04 archive at build time and are not pinned.

## Anonymous archive

`artifact/anonymize.sh [-w WORDS_FILE] [OUTPUT.tar.gz]` writes a source archive
of the current commit (or of the commit `REF`, e.g. `REF=v2.5.1`) for
double-blind review. It leaves out `.git`, the contributor license agreement
with its workflow, the script itself and `artifact/check_anonymous.sh`. The
name of the author is found without a list of words: the script reads it from
the places where the repository states it (`formal/core/document/root.tex`,
`NOTICE`, `LICENSE.md`, the headers of both EBNF files and the Contact section
of `README.md`) and replaces it, and each of its words, everywhere; names of
other people, such as those of the authors of the works cited, are kept. The address
of the repository and of the project's sites are replaced too, as are the
account of the maintainer and the surname of the author, and every word listed
in the optional `WORDS_FILE`, which is kept outside the repository. Text that
points to the history of the project is rewritten as well: the commit hashes of
the tags v2.5.1 and v2.5 and of the commit archived are removed (`LICENSE.md`
of v2.5.1 cites the hash of v2.5), and where `formal/core/CORE.md` names a
review or a revision by the number of its stage of the development, the text
becomes "an independent review" or "an earlier revision". The name of the
language is kept. The script fails, and writes nothing, if any of these words,
a hash of a commit of the repository, an e-mail address or a stage is left in a
file or a file name, if a replacement is joined to letters (`ANONYMOUS` or
`ANONYMIZED` followed by a letter of any alphabet, or such a letter followed by
`ANONYM`: a word was replaced inside a longer word, such as the name of someone
else), if a name of another person that it keeps is joined directly to a
replacement, or if `root.tex` or `NOTICE` names no author.

The archive is reproducible: the same commit gives the same bytes, whoever
writes it, with GNU tar and GNU gzip. The files are listed sorted by name, with
the time 2000-01-01 00:00:00 UTC, owner and group 0 without names and the modes
644 and 755, and gzip stores no file name and no time. The script prints the
SHA-256 of the archive, so an archive written locally can be compared with the
one of the CI run of the same commit.

Both scripts need GNU grep built with PCRE (`grep -P`, used with the locale
`C.UTF-8` for the letters of any alphabet); without it they stop with an error
instead of skipping those checks.

`artifact/check_anonymous.sh ARCHIVE.tar.gz` searches a written archive again,
independently of the script that wrote it: the hashes of the tags, the name of
the author, the account of the maintainer, the address of the repository, the
sites of the project, e-mail addresses and replacements joined to letters of
any alphabet or to the name of another person that the archive keeps, in
the file names, the tar headers and the contents of every file. The workflow `.github/workflows/artifact.yml`
writes the archive of the commit pushed on every push, searches it, and keeps it
as the artifact `triel-artifact-anonymous` of the run; the result of the search
is the separate artifact `anonymous-archive-check`. The archive is not
committed.
