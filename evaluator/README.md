# Evaluator of the TRIEL core

`generated/TRIEL.hs` is exported by Isabelle from [`formal/core/TRIEL_Exec.thy`](../formal/core/TRIEL_Exec.thy) and must not be edited. CI checks that it is exactly what `isabelle build -e -D formal/core` produces. `Main.hs` reads the input and prints the report; every verdict and every decision of a monitor is computed by the exported function `run` (`formal/core/CORE.md`, section 10); the module also exports `check_action` and `enforce`, the fail-closed monitor of a prohibition as a decision on one action (`blocks`, executed by a code equation) and as a function on traces (sections 8 and 9, decision 37).

Build with GHC (checked with 9.6.7; only `base` is needed):

```bash
ghc -O1 -ievaluator/generated -outputdir evaluator/build -o evaluator/triel-eval evaluator/Main.hs
```

Run a scenario through the translator and the evaluator:

```bash
python3 parser/triel_eval.py examples/core/scenarios/deadline_cure_ok.scn
```

The input format is described at the top of `Main.hs`, the scenario and report formats in [`examples/core/README.md`](../examples/core/README.md).

`triel-eval --last` prints the report followed by one more line, `LAST ENTRY J : ...`, with the decisions of the `MONITOR` lines at the last entry J of the trace ([`examples/core/README.md`](../examples/core/README.md#output)). `Main.hs` selects these decisions from the `MONITOR` lines that `run` computed; it does not compute or change them.

## triel check

`triel check` is one command for a developer: given a specification and a recorded trace, it prints the verdicts of the norms and the decisions of the fail-closed monitor of each prohibition.

```bash
python3 parser/triel.py check SPEC.triel TRACE [--json] [--last] [--evaluator PATH]
```

It runs from the root of the repository once the evaluator is built (above), with Python 3 and `lark==1.3.1`, like `parser/triel_eval.py`. The program is `parser/triel.py`, next to the translator and the scenario driver whose functions it calls; it needs no installation step, and it finds the translator's grammar and the evaluator relative to the repository, as the driver does. On a Unix shell, `alias triel='python3 parser/triel.py'` gives the command its short name.

What it does, step by step:

1. reads `TRACE`, a scenario written as a `.scn` file or in JSON (below); the trace names its specification, which must be the file `SPEC.triel`;
2. translates the specification with `parser/triel_to_core.py`; if the translator rejects it, the report ends with the line `REJECTED: ...` and the command stops;
3. converts the trace with the functions of `parser/triel_eval.py` and runs the evaluator, which prints the report;
4. prints the report: as text, exactly as `parser/triel_eval.py` prints it, or with `--json` as JSON, one object per line of the report.

The evaluator binary is taken from `--evaluator`, else from the environment variable `TRIEL_EVALUATOR`, else `evaluator/triel-eval` (`triel-eval.exe` on Windows), as for `parser/triel_eval.py`.

### Example

The mandate of a shop agent, [`examples/core/merchant_mandate.triel`](../examples/core/merchant_mandate.triel), on the scenario in which the agent applies a price change of 35 percent without the owner's approval:

```bash
python3 parser/triel.py check examples/core/merchant_mandate.triel examples/core/scenarios/mandate_price_over_limit.scn --last
```

```
SPEC merchant_mandate
METADATA PROVENANCE_REQUIRED true
METADATA SOURCE stock_units inventory_feed
ACTIVATION OK
BLOCK OK
TYPES OK
TERM 1 MUST_NOT agent apply_price_change : BREACHED 1794301801 NOTIFY owner
TERM 2 ON_BREACH agent : BOUND 1
TERM 3 MUST_NOT agent apply_restock : PENDING
TERM 4 MUST_NOT agent apply_campaign : PENDING
TERM 5 ON_BREACH agent : BOUND 4
INVARIANT budget_limit_set : U
MONITOR 1 : ENTRY 2 BLOCK
MONITOR 3 : NO ACTION
MONITOR 4 : NO ACTION
LAST ENTRY 2 : MONITOR 1 BLOCK
```

The exit code is 3: the monitor of the price rule (`TERM 1`) blocks the change at entry 2, the last entry. Without `--last` the report is the same without its last line, and the exit code is 3 because a `MONITOR` line has a `BLOCK`. On `mandate_price_approved.scn`, where the owner approved the change, the last line is `LAST ENTRY 2 : MONITOR 1 ALLOW` and the exit code is 0.

### --last

`--last` answers the question an agent asks before it acts: may the action I am about to take be taken now? The trace ends with that action, and the evaluator adds the line

```
LAST ENTRY J : NO DECISION | (MONITOR I (BLOCK | ALLOW))+
```

with the decision, at the last entry J, of the monitor of every top-level prohibition `TERM I` whose action it is. The decisions are the ones the evaluator prints in the `MONITOR` lines: they are computed by the exported function `run`, through `monitor_decisions` of `formal/core/TRIEL_Breach.thy`, which reads the condition of the prohibition in the blocked state of entry J − 1 with `blocks`, the function exported as `check_action`. A decision is `BLOCK` exactly when `enforce` replaces the action by a tick (`monitor_decisions_enforce`), and it does not change when entries are appended later, unless the longer trace is rejected for its time order or its types (`run_final`). `Main.hs` only selects the decisions at entry J and prints them.

`NO DECISION` means that no monitor decided on the last entry: it is not the action of the subject of a top-level prohibition, or it is the activation entry, or the report has no `MONITOR` line (a rejected trace, or no top-level prohibition). It is not a permission, and its exit code is 5, not 0.

### Exit codes

The exit code is read from the words of the lines of the report, through their JSON objects; the conditions are checked in the order of the table, and the first that holds gives the code.

| Order | Code | When |
|---|---|---|
| 1 | 2 | The translator rejects the specification: the report ends with the line `REJECTED: ...`. |
| 2 | 1 | Any other error: a file that cannot be read, a trace that is not well formed or names another specification, a specification that does not parse, an evaluator that cannot be run or fails, a report that is not recognised (a line that is not one of the lines of `examples/core/README.md`, Output), or with `--last` no `LAST` line of one of its forms at the end (an evaluator built before the option ignores it). The message is on standard error, and nothing is printed on standard output. |
| 3 | 4 | The evaluator rejects the trace, with or without `--last`: a line that begins with `TIME ORDER REJECTED`, `ACTIVATION REJECTED`, `BLOCK REJECTED` or `TYPES ILL-TYPED`. Nothing is decided on a rejected trace. |
| 4 | 3 | A monitor blocks an action: a `MONITOR` line has `BLOCK`; with `--last`, the `LAST` line has `BLOCK`. |
| 5 | 6 | Without `--last` only: the report records a violation and no monitor blocks: a `TERM` line whose verdict, the word after its colon, is `BREACHED` or `ELSE BREACHED` (also when it is followed by `CURE FULFILLED`: a breach cured in time stays a breach on record), a composite line with `STATUS VIOLATED`, or an invariant `F`. The words `VIOLATED YES` and `VIOLATED NO` of a composite line, before `STATUS`, are not a violation. |
| 5 | 5 | With `--last` only: `LAST ENTRY J : NO DECISION`, the monitor made no decision on the last action. |
| 6 | 0 | Without `--last`: none of the above, so the report is computed, no monitor blocks and no violation is recorded. With `--last`: the `LAST` line has `ALLOW` and no `BLOCK`. |

With `--last` the code answers only the question about the last action: 0 means that the last action is `ALLOW`, and a violation earlier in the trace does not change the code. Without `--last`, 0 means that the report is computed, no monitor blocked anything, and no violation is on record.

### What the proof covers, and what it does not

Covered: every verdict and every decision in the report is computed by the code that Isabelle exported from the theories of `formal/core` (`run`, with the monitor of section 8.1 and decision 37 of `formal/core/CORE.md`), and the theorems about them are proved there. The command decides nothing: the exit code is read from the words of the lines the evaluator printed.

Not covered by the proof:

- the translator `parser/triel_to_core.py`, the reading of the trace in `parser/triel_eval.py` and `parser/triel.py`, the reading and printing in `Main.hs`, and the conversion of the report to JSON. They are checked by tests (`parser/test_triel_to_core.py`, `parser/test_triel_check.py`), not proved; the conversion to JSON is also checked on every line it converts, by converting the object back to the line;
- what happens outside the command. The trace is data given to it: whoever records the times, the events and the values of the factors is responsible for them, and nothing here checks that they are true. The command does not watch a running system and does not stop anything: to keep an agent from taking a blocked action, the system that runs the agent must call the command with `--last` before the action and hold the action back on any exit code other than 0. That interception is outside the command and is not checked.

### The trace in JSON

A trace in JSON is a scenario of [`examples/core/README.md`](../examples/core/README.md#scenarios), written one to one: the same entries, times as ISO-8601 strings in UTC, and the same events, actions and values. Nothing else may appear: an unknown key, a key given twice or a missing key is an error. A file whose first character other than white space is `{` is read as JSON, any other as a `.scn` file. The JSON is converted to the scenario and checked by the same code, so both forms give the same evaluator input and the same report.

| `.scn` | JSON |
|---|---|
| `(scenario NAME (spec "PATH") ENTRY ...)` | `{"scenario": "NAME", "spec": "PATH", "entries": [ENTRY, ...]}` |
| `(entry "TIME" EVENT (data (FACTOR VALUE) ...))` | `{"time": "TIME", "event": EVENT, "data": {"FACTOR": VALUE, ...}}` |
| `(activate)`, `(tick)` | `{"kind": "activate"}`, `{"kind": "tick"}` |
| `(arrive FACTOR)` | `{"kind": "arrive", "factor": "FACTOR"}` |
| `(act SUBJECT ACTION POLARITY)` | `{"kind": "act", "subject": "SUBJECT", "action": ACTION, "polarity": "must"}` (or `"may"`, `"must_not"`) |
| `NAME`, `(NAME ARG ...)` (an action) | `"NAME"`, `{"name": "NAME", "args": [ARG, ...]}` |
| `(name X)` (an argument) | `{"name": "X"}` |
| `(bool true)`, `(bool false)` | `{"bool": true}`, `{"bool": false}` |
| `(int N)` | `{"int": N}`, a JSON integer |
| `(dec D)` | `{"dec": "D"}`, the decimal literal as a string, such as `"12.50"`, so that it stays exact |
| `(str "...")` | `{"str": "..."}` |
| `(time "TIME")` | `{"time": "TIME"}` |
| `(record (FIELD VALUE) ...)` | `{"record": {"FIELD": VALUE, ...}}` |

`PATH` is relative to the root of the repository, as in a `.scn` file. A name (`NAME`, `FACTOR`, `SUBJECT`, `FIELD`, `X`, the polarity) is one word, without white space, parentheses, `"` or `;`; a `.scn` file also accepts a name in quotes, such as `(act "agent x" ...)`, which has no form in JSON; the order of the keys of `data` and `record` is the order of the fields. The scenario `mandate_price_over_limit.scn` in JSON:

```json
{"scenario": "mandate_price_over_limit",
 "spec": "examples/core/merchant_mandate.triel",
 "entries": [
  {"time": "2026-11-10T09:00:00Z", "event": {"kind": "activate"},
   "data": {"budget_limit": {"dec": "5000.00"}, "reorder_point": {"int": 10}}},
  {"time": "2026-11-10T09:10:00Z", "event": {"kind": "tick"},
   "data": {"budget_limit": {"dec": "5000.00"}, "reorder_point": {"int": 10},
            "price_delta_pct": {"dec": "35.0"}, "price_change_approved": {"bool": false}}},
  {"time": "2026-11-10T09:10:01Z",
   "event": {"kind": "act", "subject": "agent", "action": "apply_price_change", "polarity": "must_not"},
   "data": {"budget_limit": {"dec": "5000.00"}, "reorder_point": {"int": 10},
            "price_delta_pct": {"dec": "35.0"}, "price_change_approved": {"bool": false}}}]}
```

### The report in JSON

With `--json` the report is a JSON array with one object per line of the text report, in the same order. Each object is the line taken apart into its words, with nothing added: the key `"line"` names the kind of line, and every other key is a word or a group of words of that line, named after the placeholder of the line in [`examples/core/README.md`, Output](../examples/core/README.md#output). Times, entries and the numbers of terms are JSON integers; every other word is a string, exactly as printed (an action `pay(landlord, 1200)`, an amount `250.5` or `1/3`, a quoted value `"EU"` with its quotes). Converting each object back gives the line it came from; the command checks this for every line before it prints, and fails with exit code 1 otherwise.

| Line of `examples/core/README.md`, Output | JSON object |
|---|---|
| `SPEC NAME` | `"line": "SPEC"`, `"name"`: NAME |
| `METADATA KEY VALUE` | `"line": "METADATA"`, `"key"`: KEY, `"value"`: VALUE |
| `METADATA DID SUBJECT "DID"` | `"line": "METADATA"`, `"key": "DID"`, `"subject"`: SUBJECT, `"did"`: `"DID"` with its quotes |
| `METADATA PROVES FACTOR CONSTRAINT` | `"key": "PROVES"`, `"factor"`: FACTOR, `"constraint"`: CONSTRAINT |
| `METADATA BOUND_TO FACTOR S NONCE` | `"key": "BOUND_TO"`, `"factor"`: FACTOR, `"subject"`: S, `"nonce"`: NONCE |
| `METADATA SOURCE FACTOR SUBJECT` | `"key": "SOURCE"`, `"factor"`: FACTOR, `"subject"`: SUBJECT |
| `METADATA POLARITY FACTOR NUMBER` (also `THRESHOLD`, `SENSITIVITY_BOUND`) | `"key"`: the keyword, `"factor"`: FACTOR, `"number"`: NUMBER |
| `REJECTED: CONSTRUCT; ...` | `"line": "REJECTED"`, `"constructs"`: the list of the constructs, in the order of the line |
| `TIME ORDER REJECTED ENTRY J` | `"line": "TIME ORDER REJECTED"`, `"entry"`: J |
| `ACTIVATION OK \| ACTIVATION REJECTED` | `"line": "ACTIVATION"`, `"result"`: `"OK"` or `"REJECTED"` |
| `BLOCK OK \| BLOCK REJECTED` | `"line": "BLOCK"`, `"result"`: `"OK"` or `"REJECTED"` |
| `TYPES OK \| TYPES ILL-TYPED ENTRY J FACTOR F` | `"line": "TYPES"`, `"result"`: `"OK"` or `"ILL-TYPED"`; with `ILL-TYPED`, `"entry"`: J, `"factor"`: F |
| `TERM I MUST S A DEADLINE (T \| NONE) : STATUS` | `"line": "TERM"`, `"term"`: I, `"kind": "MUST"`, `"subject"`: S, `"action"`: A, `"deadline"`: T, or `null` for `NONE`, `"status"`: STATUS (below) |
| `TERM I MUST S A DEADLINE T ELSE S2 A2 DEADLINE (T \| NONE) : FULFILLED \| PENDING \| ELSE V` | as `MUST`, with `"fallback": {"subject": S2, "action": A2, "deadline": T or null}`; `"status"`: `{"verdict": "FULFILLED"}`, `{"verdict": "PENDING"}`, or `{"verdict": "ELSE", "fallback": V}` with V a verdict (below) |
| `TERM I MUST_NOT S A : PENDING \| BREACHED T ACTION*` | `"kind": "MUST_NOT"`, `"subject"`, `"action"`, `"status"`: a verdict with `"actions"`: the list of ACTION (below), possibly empty |
| `TERM I MAY S A : FULFILLED \| PENDING` | `"kind": "MAY"`, `"subject"`, `"action"`, `"status"`: a verdict |
| `TERM I ON_BREACH S : BOUND J` | `"kind": "ON_BREACH"`, `"subject"`: S, `"bound"`: J, or `null` for `UNBOUND`, the word `Main.hs` prints when `bound_to` finds no norm for the handler |
| `TERM I COMPOSITE : DONE X INTERRUPTED X VIOLATED X STATUS ...` | `"kind": "COMPOSITE"`, `"done"`, `"interrupted"`, `"violated"`: X (`"YES"`, `"NO"` or `"UNKNOWN"`), `"status"`: `{"outcome": "VIOLATED" \| "INTERRUPTED" \| "DONE", "entry": K}` or `{"outcome": "OPEN"}` or `{"outcome": "UNKNOWN"}` |
| `INVARIANT NAME : T \| F \| U` | `"line": "INVARIANT"`, `"name"`: NAME, `"value"`: `"T"`, `"F"` or `"U"` |
| `MONITOR I : NO ACTION \| (ENTRY J (BLOCK \| ALLOW))+` | `"line": "MONITOR"`, `"term"`: I, `"decisions"`: a list of `{"entry": J, "decision": "BLOCK" or "ALLOW"}`, empty for `NO ACTION` |
| `LAST ENTRY J : NO DECISION \| (MONITOR I (BLOCK \| ALLOW))+` | `"line": "LAST"`, `"entry"`: J, `"decisions"`: a list of `{"term": I, "decision": "BLOCK" or "ALLOW"}`, empty for `NO DECISION` |

The parts of a `TERM` line, after the list of `STATUS` in `examples/core/README.md`, Output:

- a verdict, `FULFILLED`, `PENDING` or `BREACHED T`: `{"verdict": "FULFILLED"}`, `{"verdict": "PENDING"}`, `{"verdict": "BREACHED", "time": T}`;
- `STATUS` of an obligation: a verdict; after `BREACHED T`, also `"actions"`, the informational actions of the handler, and `"continuation"`, one of `{"continuation": "CLOSED"}`, `{"continuation": "TERMINATED"}`, `{"continuation": "CURE"}` with the keys of a verdict, `{"continuation": "ESCALATED", "subject": S}` with the keys of a verdict;
- an informational action: `NOTIFY S` is `{"action": "NOTIFY", "subject": S}`; `PENALTY V` is `{"action": "PENALTY", "amount": V}`; `PENALTY V CAPPED` is `{"action": "PENALTY", "amount": V, "capped": true}`; `PENALTY UNDEFINED` is `{"action": "PENALTY", "undefined": true}`; `PENALTY NEGATIVE V` is `{"action": "PENALTY", "negative": true, "amount": V}`.

The first lines of the example above, with `--json`:

```json
[
{"line": "SPEC", "name": "merchant_mandate"},
{"line": "METADATA", "key": "PROVENANCE_REQUIRED", "value": "true"},
...
{"line": "TERM", "term": 1, "kind": "MUST_NOT", "subject": "agent", "action": "apply_price_change", "status": {"verdict": "BREACHED", "time": 1794301801, "actions": [{"action": "NOTIFY", "subject": "owner"}]}},
...
{"line": "MONITOR", "term": 1, "decisions": [{"entry": 2, "decision": "BLOCK"}]},
...
{"line": "LAST", "entry": 2, "decisions": [{"term": 1, "decision": "BLOCK"}]}
]
```
