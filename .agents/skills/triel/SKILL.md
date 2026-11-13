---
name: triel
description: Check the actions of an AI agent against a TRIEL specification before acting, write rules given in words as a TRIEL specification and test it, and read the report of triel check. Use it when a TRIEL specification governs an agent (obligations with deadlines, prohibitions, permissions), before every action that such a specification governs, when asked to write, change or check rules for an agent's actions, and when a report shows a verdict, BLOCK, ALLOW, NO DECISION or REJECTED.
license: CC-BY-4.0
compatibility: Needs a clone of the repository that holds this skill, with every command run from its root, Python 3 with lark==1.3.1, and the evaluator built with GHC as evaluator/README.md describes.
---

All paths in this skill are relative to the root of the repository; run every command from there.
This file is licensed under CC BY 4.0 (text only). No patent license, express or implied, is granted. The code of the repository is under the Apache License 2.0; see `LICENSE.md`.
© 2026 Dmitri Chistyakov

# TRIEL for agents

A TRIEL specification says who must, may or must not do what, by when, on which data, and what follows a breach. `triel check` (`parser/triel.py`) prints the verdict of every rule on a trace and, for every top-level prohibition, the decisions of its fail-closed monitor: `BLOCK` or `ALLOW`. If `evaluator/triel-eval` is missing, build it first, as `evaluator/README.md` says.

## 1. Before every action that a TRIEL specification governs

Before every action that a TRIEL specification governs, follow these steps. This is a standing rule: it holds for every such action, for as long as the specification governs you, and an answer about one action never covers a later one.

1. **Record the trace.** Write down everything that happened since the activation, as the host reported it, in JSON (`evaluator/README.md`, section "The trace in JSON"). Then add two last entries:
   - a `tick` entry with the data just before the action, without anything the action itself changes: the latest data the host reported;
   - the entry of the action itself, with the same data as the `tick` entry, unchanged and with nothing added.

   Give both entries exactly the same time: the current UTC time by the clock, at the moment of the check.
2. **Run the check** and read the exit code of the command itself:

   ```bash
   python3 parser/triel.py check SPEC TRACE --last --json
   ```

   Add `--evaluator PATH` if the evaluator is not in its default place. Do not send the output into a pipeline (`| head`, `| jq`, `| tail`), do not add `|| true`, and do not run the command inside another one: the exit code of a pipeline is that of its last command, so a `BLOCK` turns into 0. To process the output, save the code first: `python3 parser/triel.py check SPEC TRACE --last --json > report.json; code=$?`.
3. **Decide.** Take the action only on code 0, and right after the check. If the action is delayed, check again with the new time.
   - Code 0 means one thing only: the monitor of every top-level prohibition whose action this is allows it. It says nothing about prohibitions inside composite terms (`THEN`, `OR`, `AND`, `UNLESS`, the branches of `IF` and `WHEN`, `REF`), nor about obligations, permissions and invariants.
   - If the specification prohibits this action (the same subject, name and arguments) inside a composite term, that prohibition has no `TERM I MUST_NOT S A` line of its own: it is inside a `TERM K COMPOSITE` line. Then do as on code 5: do not act, and tell the user that no monitor decides this prohibition. A line `STATUS VIOLATED ENTRY J` confirms a violation, but its absence does not allow the action: the status of a composite term is fixed at its first violation, so a second violation gives no new line, and a nested prohibition whose condition is undefined is not violated (`STATUS OPEN`).
   - On any other code, do not act, and tell the user what the report says: which `TERM` and `MONITOR` block, `NO DECISION`, or why the trace or the specification was rejected. Code 1 gives no report: pass on the error message.
   - Code 5 (`NO DECISION`) is not a permission (`evaluator/README.md`, sections "--last" and "What the proof covers, and what it does not"). If a `TERM` line requires this action (`MUST`) and names a deadline, tell the user the obligation and its deadline at once; the decision is theirs or the host's.
   - Without `--last`, an action that no monitor decides gives 0, so `--last` is required.

   | Code with `--last` | The report | What you do |
   |---|---|---|
   | 0 | the `LAST` line has `ALLOW` and no `BLOCK` | act now, unless a composite term prohibits the action (above) |
   | 1 | none: an error message on standard error | do not act; pass the message on |
   | 2 | `REJECTED: ...`, the translator rejects the specification | do not act |
   | 3 | the `LAST` line has `BLOCK` | do not act; name the `TERM` whose monitor blocks |
   | 4 | `TIME ORDER REJECTED`, `ACTIVATION REJECTED`, `BLOCK REJECTED` or `TYPES ILL-TYPED`: the trace is rejected | do not act |
   | 5 | `LAST ENTRY J : NO DECISION` | do not act; the user or the host decides |

   Code 6 occurs only without `--last`: a violation is on record and no monitor blocks.
4. **The last entry is a question, not a fact.** If you do not take the action, remove its entry from the recorded history before the next check; keep the `tick` entry with its real data. The lines of the report that depend on entry J (`FULFILLED`, `BREACHED`, `NOTIFY`, `PENALTY`, `STATUS … ENTRY J`) describe what would follow if the action were taken. Do not report them to the user as something that happened.

**Why a `tick` entry at the very time of the action.** The monitor decides on the action at entry J in the state of entry J − 1, and the freshness of a factor with `MAX_AGE` is counted at the time of entry J − 1 too. In `examples/core/core_invoice_agent.triel` the EUR value of the invoice, `amount_eur`, is fresh for one hour after it arrives (`MAX_AGE 1 HOURS ON_STALE BLOCK`). In this trace a quote below the limit arrived at 09:30, and the agent is about to pay at 11:00:

<!-- test: tick example -->
```json
{"scenario": "pay_on_old_quote", "spec": "examples/core/core_invoice_agent.triel", "entries": [
 {"time": "2026-11-02T09:00:00Z", "event": {"kind": "activate"},
  "data": {"limit_eur": {"dec": "1000.00"}, "owner_approved": {"bool": false}}},
 {"time": "2026-11-02T09:30:00Z", "event": {"kind": "arrive", "factor": "amount_eur"},
  "data": {"amount_eur": {"dec": "900.00"}, "limit_eur": {"dec": "1000.00"}, "owner_approved": {"bool": false}}},
 {"time": "2026-11-02T11:00:00Z", "event": {"kind": "tick"},
  "data": {"amount_eur": {"dec": "900.00"}, "limit_eur": {"dec": "1000.00"}, "owner_approved": {"bool": false}}},
 {"time": "2026-11-02T11:00:00Z",
  "event": {"kind": "act", "subject": "agent", "action": {"name": "pay", "args": [{"name": "supplier"}]}, "polarity": "must_not"},
  "data": {"amount_eur": {"dec": "900.00"}, "limit_eur": {"dec": "1000.00"}, "owner_approved": {"bool": false}}}]}
```

Checked as written, it ends with `LAST ENTRY 3 : MONITOR 2 BLOCK`, exit code 3: at 11:00 the quote is stale, so it is absent and the condition is undefined. Without the `tick` entry the monitor reads the state of 09:30, where the quote was fresh and below the limit, and the answer is `ALLOW`, exit code 0, for a payment on a stale quote. Data without `MAX_AGE` go stale the same way: an approval that the host withdrew after its last entry still counts in a trace without the `tick` entry. The scenario `mandate_price_over_limit` of `README.md` has its `tick` entry earlier than the action and is still right, because its factors have no `MAX_AGE` and its data did not change between the two entries. You cannot know that in general, so add the `tick` entry.

## 2. Write rules given in words as a specification

1. Start from the closest specification in `examples/core/`; `examples/core/README.md` describes each of them. For instance:
   - `examples/core/core_invoice_agent.triel`: an obligation with a deadline and a fallback (`WITHIN … ELSE`), a prohibition whose condition reads a quote under `ON_STALE BLOCK` and an approval that may be absent, and a breach handler that notifies the owner;
   - `examples/core/merchant_mandate.triel`: prohibitions on applying prepared changes, each lifted by its own approval factor;
   - `examples/core/core_deadline_cure.triel`: a deadline, its breach and a cure;
   - `examples/core/sensor_overheat.triel`: durations counted from the activation, an escalation after a breach, and a reading under `MAX_AGE`;
   - `examples/core/core_payment.triel`: actions with arguments, an obligation whose window opens with `FROM`, and penalties with `CAP`;
   - `examples/core/purpose_limitation_gate.triel`: a permission and a prohibition with complementary conditions.
2. Stay within the constructs that the translator accepts. Run `python3 parser/triel_to_core.py FILE` until it accepts the specification: exit code 0; 2 with a line `REJECTED: ...` when it rejects a construct; 1 when the file does not parse. It names only the outermost construct it rejects, so run it again after every fix.
3. Write a prohibition that must stop an action of the agent at the top level of `TERMS`: only such prohibitions have a monitor.
4. For every rule, write at least one scenario where it is kept and one where it is broken or the action is blocked. Run them with `python3 parser/triel.py check FILE TRACE` (with `--last` for a check before an action) and compare the result with what the user expects.
5. If a rule does not say who, by when, on which data and what follows a breach, ask the user. If there is nobody to ask, write the assumption down next to the specification.
6. Do not invent syntax. If the translator rejects a construct, tell the user which rule cannot be checked in the core. Do not drop the rule silently, and do not replace it by another meaning without saying so.
7. Keep your files outside `examples/`, for instance in a folder `work/` of your own. The `spec` path of a trace is relative to the root of the repository.
8. In your answer, say plainly that neither the acceptance by the translator nor passing scenarios show that the specification says what the user meant: name both.
9. Do not use a specification you wrote yourself to allow your own actions until the user has confirmed it.

The blocks every specification needs, in order, `INVARIANTS` included:

```triel
SPECIFICATION my_rules VERSION 1.0.0

SUBJECTS {
  editor : PARTY,
  agent  : SYSTEM
}

TERMS {
  editor MUST review_draft WITHIN 2 DAYS;
  agent MUST_NOT publish WHEN NOT draft_reviewed
}

FACTORS {
  draft_reviewed : Boolean METADATA
}

INVARIANTS {
  review_known : LIVENESS : EVENTUALLY(PRESENT(draft_reviewed))
}
```

## 3. Read the report

Each line of the text report is one object of the JSON report (`--json`). The kinds of line, in their order:

- `SPEC` and `METADATA`: printed by the translator.
- `REJECTED: ...`: the translator rejects the specification (exit code 2) and names the outermost constructs it rejects; nothing is evaluated.
- `TIME ORDER REJECTED ENTRY J`, `ACTIVATION REJECTED`, `BLOCK REJECTED`, `TYPES ILL-TYPED ENTRY J FACTOR F`: the evaluator rejects the trace (exit code 4) and decides nothing.
- `TERM I MUST ...`: an obligation and its verdict: `FULFILLED`, `PENDING` (not decided yet), or `BREACHED T` followed by the actions of its handler and a continuation (`CLOSED`, `TERMINATED`, `CURE …`, `ESCALATED …`). A breach stays on record after a cure.
- `TERM I MUST_NOT ...`: a top-level prohibition, `PENDING` or `BREACHED T` followed by the actions of its handler (`NOTIFY S`, `PENALTY V`). A breach needs the condition to be true: an action under an undefined condition is blocked but not breached.
- `TERM I MAY ...`: a permission, `FULFILLED` once exercised, else `PENDING`.
- `TERM I ON_BREACH S : BOUND J`: a handler, bound to `TERM J`.
- `TERM I COMPOSITE : ...`: a composite term. Its `STATUS` is `VIOLATED`, `INTERRUPTED` or `DONE` with an entry, which is final; `OPEN`, which is not; or `UNKNOWN`.
- `INVARIANT NAME : T`, `F` or `U`: `U` is inconclusive, neither shown true nor shown false on the data. `ALWAYS(...)` is never `T` on a finite trace.
- `MONITOR I : ...`: the decisions of the monitor of the top-level prohibition `TERM I`, one for each action of its subject: `BLOCK` when the condition is not known to be false in the state of the entry before the action, `ALLOW` when it is false there; `NO ACTION` when the subject never takes the action.
- `LAST ENTRY J : ...`: with `--last` only, the decisions at the last entry J, or `NO DECISION`.

With `--last`, the lines that depend on the last entry describe the action as if it were taken (part 1, step 4). For a line that is not described here, read `examples/core/README.md`, section "Output"; for the JSON objects, `evaluator/README.md`, section "The report in JSON".

## 4. Pitfalls

- **The `tick` entry at the time of the action** (part 1). Without it, a stale value or a withdrawn approval decides.
- **An undefined condition blocks.** A factor that is absent or stale makes the condition of a prohibition undefined: its monitor blocks the action, while the verdict stays `PENDING` (scenarios `invoice_stale_quote` and `sensor_stale`).
- **`data` is the complete data at that entry.** A factor that is not listed is absent, not unchanged (`examples/core/README.md`, section "Scenarios"; scenario `invoice_approval_missing`). Write only the values the host reported; leave out a value that nobody gave.
- **Freshness needs an arrival.** A factor with `MAX_AGE … ON_STALE BLOCK` is fresh only within its `MAX_AGE` after an `arrive` entry; data present at the activation without an arrival are stale (`examples/core/README.md`, section "Conventions of the evaluator", point 3; scenario `sensor_silent`). Do not add `arrive` entries that did not happen.
- **Times may not decrease.** The evaluator rejects such a trace with `TIME ORDER REJECTED ENTRY J`, exit code 4 (scenario `deadline_cure_time_order`).
- **An event matches a norm by subject, action name and arguments.** `pay` does not match `pay(supplier)`: the monitor reports `NO ACTION`, and the check before the action gives `NO DECISION`. The polarity written in the event is ignored (scenario `sequence_polarity`).
- **A breach stays on record after a cure.** `BREACHED … CURE FULFILLED` gives exit code 6 without `--last` (scenario `gdpr_notified_day_5`).
- **`NO DECISION` is not a permission, and a prohibition inside a composite term has no monitor** (part 1, step 3).
- **`==` and `!=` compare values of one type.** Between values of different types they are rejected with `REJECTED: comparison of different types`, as in `approved == "yes"` where the factor `approved` is a `Boolean`.
- **The handler of a prohibition** may contain only `NOTIFY` and `PENALTY`. A continuation (`CURE_BY`, `TERMINATE`, `ESCALATE_TO`) is rejected (`examples/core/README.md`, section "Output"): `python3 parser/triel_to_core.py examples/semantics/prohibition_continuation.triel` prints `REJECTED: §2.6 defines continuations only for obligations` and exits with code 2. Tell the user that this part of the rule cannot be checked in the core; if you propose another rule instead, say that it means something else.
- **`PENALTY` needs a currency**, declared as in `examples/core/core_payment.triel`; otherwise `REJECTED: PENALTY without CURRENCY`.
- **`INVARIANTS` is required** and holds at least one invariant; without it the file does not parse (exit code 1).
- **Names are ASCII identifiers**: a letter, then letters, digits and `_`, and not a reserved word such as `U`, `EU` or `BLOCK` (`TRIEL-grammar-v2_5-core.ebnf`, section "11a. Reserved Keywords").
- **The trace is the host's data.** Record only what happened, with the real times and values. TRIEL does not check that a trace is true (`evaluator/README.md`, section "What the proof covers, and what it does not").

## 5. What is proved and what is not

- Every verdict and every decision of a monitor in the report is computed by the code that Isabelle exported from the theories of `formal/core`; the command only reads the files, runs the translator and the evaluator, and prints.
- The translator, the reading of the trace and the printing are tested, not proved.
- The trace is data given to the command: nothing checks that its times, events and values are true.
- When you check your own action, that is not the interception that `evaluator/README.md` speaks of. A host that needs the guarantee calls the command itself before the action and holds the action back on any exit code other than 0.
