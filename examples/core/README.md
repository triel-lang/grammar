# Examples inside the formal core

The fourteen specifications in this folder use only constructs that the translator `parser/triel_to_core.py` turns into terms of the Isabelle/HOL core in [`formal/core`](../../formal/core/CORE.md):

- `core_deadline_cure.triel`: a deadline, its breach, and a cure;
- `core_unless_records.triel`: a sequence under UNLESS, with the guard read from a nested record;
- `core_stale_block.triel`: a stale factor under `ON_STALE BLOCK`, a prohibition with an undefined condition, and an escalation;
- `core_prohibition_handler.triel`: a breach handler bound to a prohibition, with informational actions only;
- `core_numbers.triel`: Integer and Decimal factors, ordering comparisons, and a comparison with an absent operand;
- `core_conditional.triel`: `IF`/`ELIF`/`ELSE` and `WHEN` terms, a named term with `REF`, and `DEFAULT`, with a condition that is undefined where the term is reached;
- `core_payment.triel`: actions with arguments, an obligation whose window opens with `FROM`, and penalties with arithmetic and `CAP`, computed in the state of the breach: capped, undefined and negative;
- `core_fallback.triel`: `WITHIN … ELSE`, an obligation with a fallback that comes into force at the deadline instead of a breach;
- `core_commitment.triel`: `EVENTUALLY … WITHIN` a duration and a factor (true at the deadline, false past it, undefined on missing data, rejected activation), and `POLARITY`, `THRESHOLD` and `SENSITIVITY_BOUND` printed as metadata;
- `core_sequence.triel`: two obligations in sequence, which need two actions, and prohibitions inside composite terms, which their first forbidden action violates, and the status of each term, read on the first prefix of the trace with a violation or with a completion by an executed action;
- `core_readings.triel`: composite terms whose prefixes have several readings (the guard of `UNLESS` after or at the entry of the payment, a prohibition in a branch of `OR`), for which the status is conservative;
- `core_hidden.triel`: a hidden `ZK<Integer>` factor, named as an action argument and never read, a `ZK<String>` factor `WITHOUT REVEALING ALL` read like an ordinary factor, and `PROOF_SYSTEM`, `CURVE`, `DID`, `PROVES`, `HASH` with a salt and `BOUND_TO` printed as metadata;
- `core_invoice_agent.triel`: an AI agent that pays an invoice for its owner: `WITHIN … ELSE` with the owner as the fallback, a prohibition whose condition compares a Decimal factor quoted by an oracle under `ON_STALE BLOCK` and reads an approval that may be absent, a breach handler that notifies the owner, and `PROVENANCE_REQUIRED`;
- `gdpr_art33_notification.triel`: the notification of a personal data breach to the supervisory authority after Article 33 of the GDPR, in a stylised reading: `WITHIN 72 HOURS` from activation, the moment the controller became aware of the breach, with `ON_BREACH CURE_BY 7 DAYS`. A missed deadline is a breach, which stays on record; a notification within 7 days of the breach cures it (`BREACHED … CURE FULFILLED`), and a cure window that passes without one is a second, final breach. The 7 days are an assumption of the example, not a period of Article 33; the reasons for the delay are a factor that no verdict reads; the risk exception and the phased notification of Article 33 are outside the example.

The scenario `age_verification_breach` runs `examples/age_verification.triel`, whose hidden `age` factor the core accepts.

The evaluator exported from Isabelle runs them on the scenarios in `scenarios/`.

The expected outputs (`scenarios/*.expected`) and the expected classification of all examples (`classification.expected`) were written by hand from the text of the specifications. They were committed before the evaluator, so the evaluator is not checked against its own output. The scenarios added in version 2.5.1 (`sequence_*`, `deadline_cure_time_order`) were committed, with their expected outputs, before they were first run, and so were the scenarios `gdpr_*`, both when the example was written and when it was re-encoded with a cure.

## Scenarios

A scenario is an implementation trace, written as an S-expression:

```
(scenario NAME
  (spec "PATH-TO-SPECIFICATION")
  (entry "TIME" EVENT DATA)
  ...)
```

- `PATH-TO-SPECIFICATION` is relative to the root of the repository.
- `TIME` is an ISO-8601 time in UTC (`YYYY-MM-DDThh:mm:ssZ`, ASCII digits). It is converted to seconds since 1970-01-01T00:00:00Z. The driver does not reorder the entries or check their order: the evaluator does.
- `EVENT` is one of:
  - `(activate)`: only for the first entry, the activation entry;
  - `(act SUBJECT ACTION POLARITY)`, where `POLARITY` is `must`, `may` or `must_not`, and `ACTION` is a name, or `(NAME ARG ...)` for an action with arguments; an argument is `(name X)`, the name of a subject or a factor (`X` may be a dotted path), or a `VALUE`;
  - `(arrive FACTOR)`;
  - `(tick)`.
- `DATA` is `(data (FACTOR VALUE) ...)`: the complete data at that entry, as nominative data. A factor that is not listed is absent. A factor, or a field of a record, may be listed only once.
- A `VALUE` is one of `(bool true)`, `(bool false)`, `(int N)`, `(dec D)`, `(str "...")`, `(time "TIME")` or `(record (FIELD VALUE) ...)`. `D` is a decimal literal such as `12.50` or `-0.5`; it denotes an exact number, and `(int N)` is the number `N`, written with ASCII digits and an optional `-`. A string is written in double quotes, with the escapes `\n`, `\t`, `\"` and `\\`.

The polarity of an event is not used: verdicts and the membership of composite terms match events by subject and action alone (`formal/core/CORE.md`, 8.3, point 3, and section 9, decision 31). It is kept in the format for the events of `TECHNICAL_REPORT.md` §2.5 (`sequence_polarity`).

## Conventions of the evaluator

1. **Order of checks.** The order of the times first: a list of entries in which an entry is earlier than the entry before it is not an implementation trace, and the report is the single line `TIME ORDER REJECTED ENTRY J`, J the first such entry (`deadline_cure_time_order`). Then activation (every deadline must resolve, in the `TERMS` block and in the invariants, and the deadline of every fallback must be after the first deadline), then well-formedness of the block (`wf_block`, and every `REF` names an earlier element without a handler: `refs_ok`), then the types of the data. The first failure is reported and evaluation stops.
2. **Types.** Each entry is checked against the declared factor types. A factor may be absent: data can be incomplete. A present factor must have its type, and inside a record every field whose type is not `Optional` must be present. Boolean, Integer, Decimal, String and DateTime are the primitive types. A number is exact: an Integer is a whole number, a Decimal a number with finitely many decimal places, and every Integer is a Decimal. DateTime values and DATETIME literals are seconds since the epoch.
3. **Freshness.** A factor with `MAX_AGE m` and `ON_STALE BLOCK` is fresh at an entry if an `(arrive FACTOR)` entry at most `m` seconds earlier exists. Otherwise it is stale, and all of its complex names are absent. Data present at activation without an arrival entry counts as stale. Under `USE_LAST` the value is kept.
4. **Blocked trace.** Verdicts, invariants and the membership of composite terms are computed on the trace in which stale factors are absent. Types are checked on the data as given.
5. **Activation data.** The activation time is the time of entry 0. A deadline from a factor is read in the blocked state of entry 0.
6. **Conditional terms.** An `IF` or `WHEN` condition is read once, in the first state of the trace being checked. Only true selects `THEN`; false and undefined take `ELIF`/`ELSE`, and without them the term completes `Done` on the one-entry trace.
7. **Named terms.** `name := t` is reported as its own element, like any other; a `REF name` inside another element is replaced by t before membership is decided.
8. **Actions with arguments.** An event matches a norm only with the same subject, action name and arguments. Names are compared as names; values by value, so `(int 1200)` and `(dec 1200.00)` are the same argument.
9. **FROM.** An obligation with `FROM f` is fulfilled only by an action at a time in [f, d], and a duration in `BY` counts from f. f is read at activation, like a deadline.
10. **Penalties.** A `PENALTY` amount is computed once, in the state of the entry just before the entry that establishes the breach: for a prohibition the state before the forbidden action, for an obligation the last state not after the deadline. It is undefined if an operand is absent, reported as negative if it is negative, and otherwise capped by `CAP`.
11. **`EVENTUALLY … WITHIN`.** The deadline is resolved at activation, like the deadline of an obligation. The invariant is `T` once its condition is true at an entry not after the deadline, an entry at the deadline included; `F` once an entry is strictly after the deadline and the condition was false at every entry not after it; `U` otherwise, so an entry where the condition is undefined prevents `F`.
12. **`WITHIN … ELSE`.** If the first obligation is not met by its deadline d, it is not breached: the fallback is in force from d, with the window (d, d′], and is reported after `ELSE`. A duration in the deadline of the fallback counts from d. A handler bound to such an obligation is rejected. If d′ is not after d, the activation is rejected (`fallback_order_rejected`, `fallback_order_equal`, `fallback_order_ok`).
13. **Hidden factors.** A `ZK<T>` factor without `WITHOUT REVEALING ALL` is hidden. Before anything else, the evaluator removes every hidden factor from the data of every entry, so its value, given or not, of the right type or not, changes nothing in the report (`hidden_valid` and `hidden_value_ignored` get the same report). A `ZK<T>` factor `WITHOUT REVEALING ALL` is an ordinary factor of type T, typed like any other (`hidden_visible_ill_typed`). `Hash` and `Address` values are strings.
14. **Composite terms.** A composite line says, for each outcome, whether the whole observed trace with that outcome is a trace of the term (`TECHNICAL_REPORT.md` §2.5), and then gives the status of the term. The actions of a term are the events of the entries after the one where it is reached, so `alice MUST pay THEN alice MUST pay` needs two payments (`sequence_one_payment`, `sequence_two_payments`). A prohibition completes at once and is violated by its first forbidden action. The status is read on the prefixes of the trace in order. The observation ends at the first prefix that is a violated trace of the term, or on which the term completes by an executed action (an obligation discharged, a permission exercised, or an `UNLESS` handler completed so), provided no reading of that prefix or of an earlier one has reached a prohibition as the last element of the term. `STATUS VIOLATED ENTRY k` if that prefix is a violated trace; otherwise `STATUS INTERRUPTED ENTRY k` if the term is interrupted on it with a handler completed by an executed action, and otherwise `STATUS DONE ENTRY k`; so VIOLATED takes precedence over DONE (`sequence_violation_then_done`). `STATUS OPEN` if no prefix ends the observation yet; `STATUS UNKNOWN` if the evaluator cannot decide the first prefix that matters (possible only with `UNLESS`). A status with an entry is final: it stays whatever entries follow, unless the longer trace is rejected as a whole (time order, types). `OPEN` is not final. An outcome Done reached at once does not end the observation: a prohibition, a permission that is not exercised and a conditional term with no branch taken complete at once, without executing anything, so a term that completes at once is OPEN (`conditional_undefined`). A term that has reached a prohibition is watched to the end of the trace, like a top-level prohibition: `alice MUST pay THEN bob MUST_NOT leak` is OPEN after the payment (`sequence_one_payment`, `sequence_two_payments`) and VIOLATED at the leak (`sequence_prohibition_violated`, `sequence_violation_not_last`). When a prefix has several readings (an obligation whose action could still come later, the guard of `UNLESS` at the entry of an action, a prohibition in a branch of `OR`), the status is conservative: once one reading has reached a prohibition, only a violation ends the observation (`readings_guard_after_pay`, `readings_guard_at_pay`, `readings_guard_at_pay_leak`, `readings_or_pay_leak`, `readings_leak_then_pay`). So `alice MUST pay OR bob MUST_NOT leak` is VIOLATED when Bob leaks after Alice pays, and `bob MUST_NOT leak THEN alice MAY ship` is watched to the end of the trace, also after Alice ships: the reading in which she does not ship has reached the prohibition. A violation is missed only after the observation has ended on a completion by an executed action, before any reading reached a prohibition: in `bob MUST_NOT leak THEN alice MUST pay` a leak after the payment does not change the status DONE, and in `alice MUST pay UNLESS flag DO bob MUST_NOT leak` neither does a leak after the guard fires, once Alice has paid before it (`readings_guard_after_pay`). This is a limit of version 2.5.1 (`formal/core/CORE.md`, decision 34).

## Output

The first lines come from the translator; the rest are printed by the evaluator. Times are in seconds since the epoch, entries are numbered from 0, and TERMS elements from 1. A number is printed exactly, with the fewest decimal places: the `PENALTY 250.50` of a handler is reported as `PENALTY 250.5`.

```
SPEC NAME
METADATA KEY VALUE                  -- JURISDICTION, STANDARD, PROVENANCE_REQUIRED, PROOF_SYSTEM, CURVE, CURRENCY, in source order
METADATA DID SUBJECT "DID"          -- in SUBJECTS order
METADATA PROVES FACTOR CONSTRAINT   -- in FACTORS order, and for each factor in source order: PROVES (one line per
METADATA BOUND_TO FACTOR S NONCE    --   constraint), BOUND_TO, SOURCE, and
METADATA SOURCE FACTOR SUBJECT
METADATA POLARITY FACTOR NUMBER     --   POLARITY, THRESHOLD and SENSITIVITY_BOUND, as written
TIME ORDER REJECTED ENTRY J          -- the only evaluator line, when the times decrease at entry J
ACTIVATION OK | ACTIVATION REJECTED
BLOCK OK | BLOCK REJECTED
TYPES OK | TYPES ILL-TYPED ENTRY J FACTOR F
TERM I MUST S A DEADLINE (T | NONE) : STATUS                -- A is NAME or NAME(ARG, ...)
TERM I MUST S A DEADLINE T ELSE S2 A2 DEADLINE (T | NONE) : FULFILLED | PENDING | ELSE V   -- V: FULFILLED, PENDING or BREACHED T
TERM I MUST_NOT S A : PENDING | BREACHED T ACTION*
TERM I MAY S A : FULFILLED | PENDING
TERM I ON_BREACH S : BOUND J
TERM I COMPOSITE : DONE X INTERRUPTED X VIOLATED X STATUS ((VIOLATED | INTERRUPTED | DONE) ENTRY K | OPEN | UNKNOWN)
                                                          -- X is YES, NO or UNKNOWN; also IF, WHEN and REF
INVARIANT NAME : T | F | U
```

`STATUS` of an obligation is one of:

- `FULFILLED`
- `PENDING`
- `BREACHED T`, followed by the informational actions of the handler (see below) and then by the continuation, which is one of:
  - `CLOSED`
  - `TERMINATED`
  - `CURE FULFILLED`, `CURE PENDING` or `CURE BREACHED T`
  - `ESCALATED S FULFILLED`, `ESCALATED S PENDING` or `ESCALATED S BREACHED T`

After `BREACHED T`, an obligation or a prohibition lists the informational actions of the handler bound to it, in source order; they fire at the breach. An action is `NOTIFY S`, `PENALTY V`, `PENALTY V CAPPED` (the amount exceeded the cap and `V` is the cap), `PENALTY UNDEFINED` (an operand has no value) or `PENALTY NEGATIVE V` (the amount is negative, which the semantic rules forbid). A handler bound to a prohibition can contain only these actions: the translator rejects a continuation-determining action (`TERMINATE`, `CURE_BY`, `ESCALATE_TO`) there, since §2.6 defines continuations only for obligations.

An action with arguments is printed `NAME(ARG, ...)`: a name as written, a string in quotes, a number exactly.

`U` is the inconclusive verdict ⊥ of an invariant.

## Classification

`classification.expected` lists every example. A file is either ACCEPTED, or REJECTED with the sorted list of rejected constructs. Only the outermost unsupported construct is reported: the translator does not look inside a construct it rejects.
