# TRIEL core conformance suite

A set of test cases against which an implementation of TRIEL compares its reports with those of the reference evaluator, the code exported from the Isabelle/HOL core in [`formal/core`](../../../formal/core/CORE.md). Each case is a scenario of [`../scenarios/`](../scenarios/), the specification it names, and its expected report. The files are not copied here: [`manifest.json`](manifest.json) lists them by their paths from the root of the repository, with their sha256.

The suite is not part of the TRIEL Language Specification. The Specification consists of exactly three files in the state of tag `v2.5.1` ([`LICENSE.md`](../../../LICENSE.md), section 1); nothing in this folder is one of them.

## Version

| Field of `manifest.json` | Value |
|---|---|
| `language_version` | `2.5.1` |
| `edition` | `Core Language Edition` |
| `revision` | `1` |
| `evaluator_sha256` | sha256 of `evaluator/generated/TRIEL.hs` as committed (LF line ends) |

A revision of the suite is identified by `language_version`, `revision`, `evaluator_sha256` and the sha256 of the files of its cases, and by nothing else. `evaluator_sha256` names the exported evaluator whose output CI compared with the `.expected` files of this revision. The sha256 of every file is computed on the file as committed, with LF line ends; a checkout that converts line ends gives other values. When a case, a file of a case or the evaluator changes, `manifest.json` is updated with a new revision.

## Cases

`manifest.json` has one entry in `cases` per scenario `examples/core/scenarios/*.scn`:

- `id`: the name of the scenario;
- `trace`, `spec`, `expected`: the scenario, the specification it names and its expected report, as paths from the root of the repository;
- `sha256`: the sha256 of each of the three files;
- `monitor_lines`: the number of `MONITOR` lines in the expected report, possibly 0. Every case is checked on both levels;
- `covers`: what the case is cited for, by the rule below.

The scenario format is described in [`examples/core/README.md`, Scenarios](../README.md#scenarios), the report in [Output](../README.md#output), and the conventions the reports follow in [Conventions of the evaluator](../README.md#conventions-of-the-evaluator).

`outside_core` lists the examples that `examples/core/classification.expected` marks `REJECTED`, with the text after `REJECTED:` as the reason. The suite makes no requirement on them.

## Levels

A line of a report belongs to a level if its first word, or for `TIME ORDER` its first two words, is one of the lines of the level:

| Level | Lines |
|---|---|
| `verdicts` | `TIME ORDER`, `ACTIVATION`, `BLOCK`, `TYPES`, `TERM`, `INVARIANT` |
| `monitor` | the lines of `verdicts`, and `MONITOR` |

No other line is compared on either level; in particular `SPEC`, `METADATA`, `REJECTED` and `LAST` lines are not.

`verdicts`: the `.scn` files of the 47 scenarios of tag `v2.5.1` have not changed since the tag, and neither have the `verdicts` lines of their `.expected` files: 14 of these files have gained one `MONITOR` line each, and the other 33 are unchanged. The exported code `evaluator/generated/TRIEL.hs` differs from that of the tag only in what the monitor adds: its functions, the constructor of the `MONITOR` line in the type `Line`, the monitor lines appended to the report by `evaluate_trace`, and the export of `enforce`, `check_action` and `Value_order`. Apart from that line of `evaluate_trace`, no function that existed at the tag has changed; `map_filter`, `does` and `evt` have only moved within the file.

`monitor`: additional. The `MONITOR` lines follow decision 37 of [`formal/core/CORE.md`](../../../formal/core/CORE.md#9-design-decisions-forced-by-the-theory), section 9, which was made after tag `v2.5.1`.

## Passing

A case passes on a level if the lines of that level in the standard output of the implementation are, line by line and exactly, the lines of that level in the `.expected` file. `\r\n` and `\n` are the same line end, and a last empty line is not counted. The exit code of the implementation does not matter. The standard error of the implementation is discarded; only its standard output is compared. An implementation that cannot be started, or does not finish within 60 seconds, fails the case. An implementation passes the suite on a level if it passes every case on that level.

Passing means agreement with the reference evaluator on these traces, in the lines of the chosen level. It does not mean conformance to the Specification.

## Where the expected reports come from

How the `.expected` files were derived, and which of them were committed before the evaluator was first run on them, is stated in [`examples/core/README.md`](../README.md), in the paragraph that begins "The expected outputs". CI compares every `.expected` file with the output of the evaluator exported from the core.

What is proved and what is trusted: [`evaluator/README.md`, What the proof covers, and what it does not](../../../evaluator/README.md#what-the-proof-covers-and-what-it-does-not), and [`formal/core/CORE.md`, section 10.6](../../../formal/core/CORE.md#106-the-translator-and-the-trusted-base).

## covers

`covers` is built mechanically from two sources, and a case is cited only for what it lists:

1. `{"doc": "examples/core/README.md", "convention": N}` for each convention N of the section [Conventions of the evaluator](../README.md#conventions-of-the-evaluator) whose text contains the name of the scenario in backquotes.
2. `{"doc": "formal/core/CORE.md", "ref": "..."}` for each place in the comment of the `.scn` file where `CORE.md` is written. `ref` is the text inside the parentheses after the name of the file, as it is, such as `decision 34` or `section 8.3, point 9`; the lines of the comment are joined with a single space.

References in a comment without the name of the file (a bare "decision N", the name of a theorem) and references to a README are not included. The conventions come first, in order, then the references to `CORE.md`, in the order of the comment.

## Running

`run.py` needs only Python 3 and its standard library. It finds the root of the repository three levels above its own folder and runs every command from the root.

```bash
python3 examples/core/conformance/run.py [--impl "COMMAND"] [--level verdicts|monitor]
```

`COMMAND` is run once per case. It is split with `shlex.split`, and in every token `{spec}` and `{trace}` are replaced by the paths of the specification and of the scenario, from the root of the repository, as in `manifest.json`; a command may use neither. The default is the reference, `python3 parser/triel_eval.py {trace}`, which needs the evaluator built and `lark==1.3.1` ([`evaluator/README.md`](../../../evaluator/README.md)). The default level is `verdicts`.

`run.py` prints `PASS` or `FAIL` for each case, with the first line that differs for a `FAIL`, and `N/M passed` at the end. Its exit code is 0 only if every case passes.

`triel check` as the implementation, on the `monitor` level (its exit code, which is not 0 on many cases, does not matter):

```bash
python3 examples/core/conformance/run.py --impl "python3 parser/triel.py check {spec} {trace}" --level monitor
```

CI runs the suite with the reference on both levels, checks `manifest.json` against the files (`evaluator_sha256`, the set of cases, and every sha256), and checks `run.py` itself: a command that prints the `.expected` file passes, and a command that prints nothing fails (`.github/workflows/evaluator.yml`).

## Limits

- Only examples inside the core: every specification of a case is accepted by the translator.
- Rejections by the translator are not tested: no `.expected` file has a `REJECTED:` line.
- The trace format is `.scn`. The same trace in JSON is described in [`evaluator/README.md`, The trace in JSON](../../../evaluator/README.md#the-trace-in-json), and `triel check` accepts it.

## License

Licensed under the Apache License 2.0 as part of `examples/` (LICENSE.md, section 2).
