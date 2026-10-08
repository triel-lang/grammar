# Examples inside the formal core

The three specifications in this folder use only constructs that the translator `parser/triel_to_core.py` turns into terms of the Isabelle/HOL core in [`formal/core`](../../formal/core/CORE.md):

- `core_deadline_cure.triel`: a deadline, its breach, and a cure;
- `core_unless_records.triel`: a sequence under UNLESS, with the guard read from a nested record;
- `core_stale_block.triel`: a stale factor under `ON_STALE BLOCK`, a prohibition with an undefined condition, and an escalation.

The evaluator exported from Isabelle runs them on the scenarios in `scenarios/`.

The expected outputs (`scenarios/*.expected`) and the expected classification of all examples (`classification.expected`) were written by hand from the text of the specifications. They were committed before the evaluator, so the evaluator is not checked against its own output.

## Scenarios

A scenario is an implementation trace, written as an S-expression:

```
(scenario NAME
  (spec "PATH-TO-SPECIFICATION")
  (entry "TIME" EVENT DATA)
  ...)
```

- `TIME` is an ISO-8601 time in UTC (`YYYY-MM-DDThh:mm:ssZ`). It is converted to seconds since 1970-01-01T00:00:00Z.
- `EVENT` is one of:
  - `(activate)`: only for the first entry, the activation entry;
  - `(act SUBJECT ACTION POLARITY)`, where `POLARITY` is `must`, `may` or `must_not`;
  - `(arrive FACTOR)`;
  - `(tick)`.
- `DATA` is `(data (FACTOR VALUE) ...)`: the complete data at that entry, as nominative data. A factor that is not listed is absent.
- A `VALUE` is one of `(bool true)`, `(bool false)`, `(int N)`, `(str "...")`, `(time "TIME")` or `(record (FIELD VALUE) ...)`.

The polarity of an event is used only when a composite term is checked against the trace of §2.5. Verdicts match events by subject and action alone (`formal/core/CORE.md`, 8.3, point 3).

## Conventions of the evaluator

1. **Order of checks.** Activation first (every deadline must resolve), then well-formedness of the block (`wf_block`), then the types of the data. The first failure is reported and evaluation stops.
2. **Types.** Each entry is checked against the declared factor types. A factor may be absent: data can be incomplete. A present factor must have its type, and inside a record every field whose type is not `Optional` must be present. Boolean, Integer, String and DateTime are the primitive types. DateTime values and DATETIME literals are seconds since the epoch.
3. **Freshness.** A factor with `MAX_AGE m` and `ON_STALE BLOCK` is fresh at an entry if an `(arrive FACTOR)` entry at most `m` seconds earlier exists. Otherwise it is stale, and all of its complex names are absent. Data present at activation without an arrival entry counts as stale. Under `USE_LAST` the value is kept.
4. **Blocked trace.** Verdicts, invariants and the membership of composite terms are computed on the trace in which stale factors are absent. Types are checked on the data as given.
5. **Activation data.** The activation time is the time of entry 0. A deadline from a factor is read in the blocked state of entry 0.

## Output

The first lines come from the translator; the rest are printed by the evaluator. Times are in seconds since the epoch, entries are numbered from 0, and TERMS elements from 1.

```
SPEC NAME
METADATA KEY VALUE                  -- JURISDICTION, STANDARD, CURRENCY, PROVENANCE_REQUIRED, in source order
METADATA SOURCE FACTOR SUBJECT      -- in FACTORS order
ACTIVATION OK | ACTIVATION REJECTED
BLOCK OK | BLOCK REJECTED
TYPES OK | TYPES ILL-TYPED ENTRY J FACTOR F
TERM I MUST S A DEADLINE (T | NONE) : STATUS
TERM I MUST_NOT S A : PENDING | BREACHED T
TERM I MAY S A : FULFILLED | PENDING
TERM I ON_BREACH S : BOUND J
TERM I COMPOSITE : DONE X INTERRUPTED X VIOLATED X        -- X is YES, NO or UNKNOWN
INVARIANT NAME : T | F | U
```

`STATUS` of an obligation is one of:

- `FULFILLED`
- `PENDING`
- `BREACHED T` followed by the continuation, which is one of:
  - `CLOSED`
  - `TERMINATED`
  - `CURE FULFILLED`, `CURE PENDING` or `CURE BREACHED T`
  - `ESCALATED S FULFILLED`, `ESCALATED S PENDING` or `ESCALATED S BREACHED T`

`U` is the inconclusive verdict ⊥ of an invariant.

## Classification

`classification.expected` lists every example. A file is either ACCEPTED, or REJECTED with the sorted list of rejected constructs. Only the outermost unsupported construct is reported: the translator does not look inside a construct it rejects.
