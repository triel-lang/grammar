# The evidence of the value of a condition

The session `TRIEL_Evidence` extends `TRIEL_Core` with the evidence of the value of a
condition in one state: which names the value rests on, and, for an undefined value, which
missing names it waits for. `TRIEL_Evidence_Def.thy` holds the definitions,
`TRIEL_Evidence.thy` the theorems. The session `TRIEL_Evidence_Accept` (`accept/`)
restates the theorems with the types of the condition, the state and the trace written out,
every type variable with its sort and every class named in full, and fails if one of them
uses a constant other than those of the core (with HOL) and `evidence`, `supports` and
`monitor_evidence`, or depends on an Isabelle oracle (an unproved assumption). The session `TRIEL_Evidence_Lex` (`lex/`) reads `TRIEL_Evidence.thy`
with the lexer of Isabelle and fails on a command outside its list of allowed commands.
The workflow `.github/workflows/evidence.yml` fixes the definitions, the three ROOT files
and the theories of `accept/` and `lex/` by their SHA-256.
Neither `eval`, nor the verdicts, nor the reported actions of the core (`ob_report`,
`pr_report`) change.

## Definition

The evidence `evidence c σ` of a condition `c` in a state `σ` is a triple of lists of
names `(X, A, U)`:

- `X`, the names whose values were read;
- `A`, the names whose absence was read (by `PRESENT`, or by the first argument of
  `DEFAULT`);
- `U`, the absent names that an undefined value waits for.

It is computed by the same recursion as `eval`. Joining two evidences appends their lists
(`ejoin`), so a name can occur in a list more than once.

Operands (`evidV a σ`):

| Operand | Case | `(X, A, U)` |
|---|---|---|
| constant `VConst v` | always | `([], [], [])` |
| name `VName x` | `x` has a value | `([x], [], [])` |
| | `x` has no value | `([], [], [x])` |
| `DEFAULT(x, a)` | `x` has a value | `([x], [], [])`; `a` is not read |
| | `x` has none, `a` has a value | the evidence of `a`, with `x` added to `A` |
| | `x` has none, `a` has none | the evidence of `a`, with `x` added to `U` |

In the last row the value appears as soon as `x` gets one or `a` does, so `x` is awaited
together with the names that `a` waits for.

Conditions (`evidence c σ`), where `p` and `q` are the values of the left and the right
part:

| Construct | Case | Evidence |
|---|---|---|
| `true`, `false` | always | `([], [], [])` |
| `a = b`, `a < b`, `a <= b` | always | the evidences of both operands, joined |
| `NOT e` | always | the evidence of `e` |
| `e1 AND e2` | `p = F` | the evidence of `e1` alone |
| | `p ≠ F`, `q = F` | the evidence of `e2` alone |
| | otherwise | both, joined |
| `e1 OR e2` | `p = T` | the evidence of `e1` alone |
| | `p ≠ T`, `q = T` | the evidence of `e2` alone |
| | otherwise | both, joined |
| `e1 IMPLIES e2` | `p = F` | the evidence of `e1` alone |
| | `p ≠ F`, `q = T` | the evidence of `e2` alone |
| | otherwise | both, joined |
| `PRESENT(x)` | `x` has a value | `([x], [], [])` |
| | `x` has no value | `([], [x], [])` |

The comparisons `==` and `>` of the grammar are `=` and `<` here, the latter with the
operands exchanged. A part that decides the connective on its own is taken alone, even when the other part is
undefined; when both parts decide (`F AND F`, `T OR T`), the left one is taken. A
comparison is undefined exactly when its joined evidence has a non-empty `U`.
`PRESENT(x) = T` puts `x` into `X` with its value, although only its presence was read:
this is coarser than needed, keeps the theorems true and saves a fourth list.

Two further definitions:

- `supports X c σ b` holds when `eval` gives `b` for `c` on `σ` restricted to the set
  `X`. Checking it takes one evaluation and does not depend on how `X` was found.
- `monitor_evidence s a c π` lists, for every entry `j ≥ 1` of the trace `π` at which `s`
  does `a`, the entry, the value of `c` and its evidence in the state of the entry before,
  `j - 1` (entry 0 is the activation entry, as in `monitor_decisions`).

## What is proved

All in `TRIEL_Evidence.thy`, without unfinished proofs; `present_free c` means that `c`
has no `PRESENT` and no `DEFAULT` in an operand of a comparison. The eighteen theorems
below are restated in `accept/`; the other lemmas of the file are steps of their proofs.

The shape of the evidence:

- `evidence_names`: every name of the evidence occurs in the condition.
- `evidence_shape`: the names of `X` have values in `σ`, the names of `A` and `U` have none.
- `evidence_present_free`: a condition without `PRESENT` and `DEFAULT` reads no absence,
  `A = []`.

(a) A defined value:

- `evidence_definite_U`: a defined value waits for nothing, `U = []`.
- `evidence_definite`: a defined value is the same in every state that agrees with `σ` on
  `X` and has no value for the names of `A`, whatever else it holds.
- `evidence_definite_pf`: for a condition without `PRESENT` and `DEFAULT`, agreement on `X`
  is enough.
- `evidence_completions`: for such a condition, the value is the same in every completion
  of `σ` restricted to `X`.

(b) An undefined value:

- `evidence_undefined_U`: an undefined value waits for at least one name.
- `evidence_undefined_absent`: the names of `U` have no value in `σ`.
- `evidence_undefined_stays`: the value stays undefined in every state that agrees with `σ`
  on `X` and has no value for the names of `A` and of `U`.
- `evidence_undefined_resolved`: the value becomes defined in every state that agrees with
  `σ` on `X`, has no value for the names of `A` and has values for all names of `U`.
- `evidence_undefined_pf`: for a condition without `PRESENT` and `DEFAULT`, it becomes
  defined in every extension of `σ` that has values for all names of `U`.

Checking a supporting set by evaluation, for a condition without `PRESENT` and `DEFAULT`:

- `supports_sound`: a set that supports a value gives that value in every state that
  agrees with `σ` on the set.
- `supports_mono`: a larger set supports the same value.
- `evidence_supports`: the names `X` of the evidence of a defined value support it.

The monitor:

- `monitor_evidence_decisions`: with the evidence dropped and a value other than `F` read
  as "block", the list is exactly `monitor_decisions`.
- `monitor_evidence_append`: the list on a trace is a prefix of the list on every trace
  that continues it, so a decision and its evidence are final.
- `monitor_evidence_stable`: a decision with the defined value `b` and evidence
  `(X, A, U)` is taken the same way by the monitor on every trace of the same length with
  the same event at that entry whose entry before keeps the values of `X` and the absence
  of `A`.

## What the evidence does not claim

- That the trace is genuine: the evidence speaks only about the data the trace holds.
- That `U` is the smallest set of missing names.
- That every name of `U` affects the answer. Counterexample: `(x == 1 OR y == 2) AND
  y == 2` on the empty state gives `U = [x, y, y]`, yet for any value of `y` the condition is
  defined without `x`. In the extreme case `x == v AND NOT (x == v)` with `x` absent, the
  value is undefined with `U = [x, x]`, although the condition is false in every completion:
  strong-Kleene connectives are not complete (`kleene_not_complete` in
  `TRIEL_Completions.thy`). What is proved is exact in its own sense: with the values of
  `X` and the absence of `A` kept, without the names of `U` the strong-Kleene evaluation
  gives no value, with all of them it gives one.
- Stability when an entry is missing in the middle of the trace.
- With a non-empty `A`, stability when data is added. Counterexample: `NOT
  PRESENT(waiver_id)` with `waiver_id` absent is true, and the monitor blocks. Evidence made of
  read values alone would be empty and would claim the value for any data; once `waiver_id`
  arrives the condition is false. This is why `A` is kept, and why the theorems for added
  data (`evidence_definite_pf`, `evidence_completions`, `evidence_undefined_pf`) require a
  condition without `PRESENT` and `DEFAULT`. The same happens with `DEFAULT`:
  `DEFAULT(discount, 0) > 0` is false while `discount` is absent and true with
  `discount = 5`. A defined value can even become undefined: `PRESENT(x) AND y == 1` is
  false on the empty state, and once `x` arrives it is `T AND ⊥ = ⊥`.
- Minimality: an evidence with the fewest names is NP-hard to find, and minimality is not
  proved.
- When a name is read both as absent and as awaited (it is in `A` and in `U`, which
  `PRESENT` and `DEFAULT` allow: `PRESENT(x) OR x == 1` on the empty state gives `A = [x]`
  and `U = [x]`), `evidence_undefined_resolved` says nothing, since its premises cannot
  hold together.
