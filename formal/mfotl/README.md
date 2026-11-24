# The bridge from the TRIEL core to MFOTL: conditions, norms and deadlines

This directory relates the TRIEL core ([`../core`](../core), session `TRIEL_Core`) to the metric first-order temporal logic MFOTL of the AFP entry `MFOTL_Checker` (release afp-2025-2, Isabelle2025-2). It has two parts. Part 1 shows that a three-valued condition of the core is a pair of MFOTL formulas, one for "true" and one for "false", with no premise on the completeness of the data, and that "unknown blocks" is the failure of the formula for "false". Part 2 is about norms and deadlines: obligations with a window or without a deadline, prohibitions, permissions, fallbacks and the handlers of a breach. It shows that the verdict of such a norm on the prefix of an implementation trace up to entry j is read from past-time MFOTL formulas at entry j. So are the decision of the fail-closed monitor and the freshness of a factor at entry j. The time of the breach of a prohibition is read at the entry of the first forbidden action. The verdict of an obligation with a deadline that is not before the activation and without FROM is also read from a formula of bounded future, at entry 0 of every MFOTL trace that encodes the trace. The core is not changed.

- [`ROOT`](ROOT): the session `TRIEL_MFOTL` (parent `MFOTL_Checker`). Part 1 is the theories [`TRIEL_MFOTL_Enc.thy`](TRIEL_MFOTL_Enc.thy) (the encoding of a trace) and [`TRIEL_MFOTL_Cond.thy`](TRIEL_MFOTL_Cond.thy) (conditions). Part 2 is the theories [`TRIEL_MFOTL_Time.thy`](TRIEL_MFOTL_Time.thy) (the time of an entry and the windows of the core), [`TRIEL_MFOTL_Norm.thy`](TRIEL_MFOTL_Norm.thy) (norms as past-time formulas) and [`TRIEL_MFOTL_Future.thy`](TRIEL_MFOTL_Future.thy) (an obligation with a deadline as a formula of bounded future).
- [`accept/ROOT`](accept/ROOT): the session `TRIEL_MFOTL_Accept`. It has a time limit, so a proof that does not end is a failure. Its two theories do not import each other.
  - [`accept/Accept_MFOTL1.thy`](accept/Accept_MFOTL1.thy) restates the theorems of part 1 with every type fixed and proves each by its theorem alone; it fails if a restated theorem uses a constant other than those of the core, of the AFP theory `Formula` and of the bridge, or depends on an oracle.
  - [`accept/Accept_MFOTL2.thy`](accept/Accept_MFOTL2.thy) does the same for part 2, in four parts. (1) It writes out each of the 17 constants of part 2 (16 formulas and the number `rel_lo`) in the constructors of the AFP theory `Formula`, the intervals of the AFP, arithmetic of HOL, the constants of part 1 and the constants written out before it, and proves each from the fact `X_def` of the stage. (2) It restates the theorems of part 2, every type variable with its sort, and proves each by its theorem alone. (3) Probes: from the satisfaction relation of MFOTL, in proofs that name no lemma of part 2 (the simp rules that part 2 declares are in the simp set; the formulas of part 1 are read by their equations), it derives what the formulas of (1) say at an entry, all but `AfterLo`, `ActedN` and `ElseIn`, and checks them on concrete entries with the activation time 0. An action exactly at the deadline fulfils, and one time unit later the obligation is breached (`accept_probe_at_deadline`, `accept_probe_after_deadline`). FROM is inclusive (`accept_probe_from`). A condition is read at the entry before the action (`accept_probe_condition_before`, `accept_probe_condition_late`). An undefined condition blocks and is not a breach (`accept_probe_undefined_blocks`). (4) It fails if a lemma uses a constant other than those of the core, of the AFP theory `Formula` (with its ancestors) and the 26 constants of the bridge; if a lemma lacks a constant it is about; if a constant of part 2 is not written out in (1); or if a lemma depends on an oracle.
- [`../../.github/workflows/mfotl.yml`](../../.github/workflows/mfotl.yml) builds both sessions against the AFP sessions they need. Its checks:
  - (1) A change of the bridge or of the workflow changes no other file: not the core, not its checks, and nothing outside `formal/mfotl` and the workflow, a renamed file counted as deleted and added. This is checked on every push to a branch `stage*` or `mfotl*` that changes the core, its checks, the bridge or the workflow; on `main`, only what the next sentence says. `formal/mfotl` holds exactly its ten files, and `ROOT`, `accept/ROOT` and the two acceptance theories are unchanged.
  - (2) The five theories of the bridge are ASCII without carriage returns and hold none of the listed words, also right after a digit, `_` or a sign: `sorry`, `oops`, the commands of axioms, oracles, unchecked definitions and ML, the commands that change the syntax or the names, a mixfix annotation (a parenthesis followed, also across lines, by a string, a cartouche or a comment), an antiquotation, a control symbol other than sub and sup, the proof symbol and the switches of proof checking. Whether a proof outside the restated theorems uses an oracle (for example `by eval`) is not checked.
  - (3) The session `TRIEL_MFOTL` builds, and (4) the session `TRIEL_MFOTL_Accept` builds.
  - (5) Five mutations of the formulas of part 2 fail the build. Each replaces one piece of a definition in a copy of `formal/mfotl`. M1: "passed" from the deadline on, not strictly after it. M2: the lower bound of a window one time unit too early. M3: the condition of a prohibition read at the entry of the action, not before it. M4: the monitor blocks only when the condition is true, not when it is unknown. M5: "breached" as soon as the deadline has passed, also after an action in time. The check fails if a mutation does not apply or if the build of the copy passes. It also fails if that build starts a session that is not of the bridge, or fails without a failed session of the bridge and an error at a command. Other changes of the formulas are not tried.

## Part 1: conditions

### The encoding

The values of MFOTL are `('n, 'v, 's, 'a) mval`: a name `MN x`, a value `MV u`, a subject `MS s` or an action `MA a` of the core. Predicates and variables of MFOTL are strings.

For an implementation trace π (`itrace` of `TRIEL_Breach`) and a set C of values, the database `enc_db C π j` of entry j holds

- `val(MN x, MV u)` for every name x with the value u in the state `st π j`;
- `lt(MV u, MV w)` and `le(MV u, MV w)` for the values u and w of `ran (st π j) ∪ C` with `vless u w` and `vleq u w`;
- `arr(MN x)` if the event of the entry is the arrival of data for x, and `act(MS s, MA a)` if it is an action a of s and j > 0 (entry 0 is the activation entry, whose event is not an action).

An MFOTL trace σ encodes π (`enc_pre C π σ`) if, for every j < |π|, the database of entry j of σ is `enc_db C π j` and its timestamp is `time π j − time π 0` (as a natural number; for a trace of the core the difference is not negative). The entries of σ after the first |π| are not constrained.

A condition c is translated into two formulas: `Pc c` holds when c is true and `Nc c` when c is false. NOT exchanges them; AND, OR and IMPLIES follow the strong Kleene tables (for example `Pc (e₁ AND e₂)` is `Pc e₁ ∧ Pc e₂` and `Nc (e₁ AND e₂)` is `Nc e₁ ∨ Nc e₂`); PRESENT(x) is "some value of x is in the database". A value expression a becomes the formula `V a y`, "the variable y is the value of a": a constant is `y ≈ MV u`, a name x is `val(MN x, y)`, and DEFAULT(x, a) is `val(MN x, y) ∨ (¬ ∃y. val(MN x, y)) ∧ V a y`. A comparison a < b is `∃x1 x2. V a x1 ∧ V b x2 ∧ lt(x1, x2)` for "true" and the same with `¬ lt(x1, x2)` for "false"; a ≤ b is the same with `le`. MFOTL compares a variable only with a constant, so a = b is "one variable is the value of a and of b" for "true", and "a and b have a value, and no variable is the value of both" for "false". Variables: a comparison binds its operands to x1 and x2 and DEFAULT binds again the variable of its operand; `Pc c` and `Nc c` are closed formulas (`fv_Pc_Nc`), so these fixed names are never captured.

### What is proved

The theorems of the theories `TRIEL_MFOTL_Enc` and `TRIEL_MFOTL_Cond`, as `Accept_MFOTL1.thy` restates them. `enc_pre_exists`, `enc_time` and the four theorems `bridge_…` assume that π is a trace of the core (`is_trace π`: a non-empty list of entries whose times do not decrease).

- `enc_db_eq`: the database of entry j is exactly the set of facts `val`, `lt`, `le`, `arr` and `act` above.
- `enc_pre_iff`: σ encodes π exactly when its first |π| databases are those of π and its timestamps are the times of π counted from entry 0.
- `enc_pre_exists`: if π is a trace, every state of π has finitely many names and C is finite, an MFOTL trace that encodes π exists.
- `econsts_finite`: the set `econsts c` of the value constants of a condition is finite.
- `enc_time`: for a trace π and j < |π|, the timestamp of entry j of an encoding, as an integer, is `time π j − time π 0`.
- `enc_db_lt`, `enc_db_le`: on values of the state and of C, the fact `lt(MV u, MV w)` (`le(MV u, MV w)`) is in the database exactly when `vless u w` (`vleq u w`).
- `bridge_true`: for a trace π, an encoding σ of π with `econsts c ⊆ C`, an entry j < |π| and every valuation, `Pc c` holds at j in σ exactly when c is true in the state of entry j.
- `bridge_false`: under the same premise, c is false in the state of entry j exactly when `Nc c` holds at j.
- `bridge_blocks_cond`: a prohibition with the condition c blocks in the state of entry j (`blocks` of the core: c is not known to be false) exactly when `Nc c` does not hold at j.
- `bridge_complete_cond`: if moreover every name whose value c needs has a value (`names c ⊆ dom (st π j)`, the premise of T4; `names c` holds the names that are operands of comparisons, without the argument of PRESENT and the first argument of DEFAULT), c is defined and its value is the truth of `Pc c`.

`bridge_true`, `bridge_false` and `bridge_blocks_cond` have no premise on the completeness of the data; only `bridge_complete_cond` has one. The lemmas they rest on are `sat_V` (the variable y is the value of a; `sat_V_upd` is its form with y bound to a given value), `evalV_ran` (a value of an operand is a value of the state or a constant of the operand), `enc_db_val` (the facts `val` are the state) and `bridge_cond` (`bridge_true` and `bridge_false` at once, by induction on the condition).

### Order of values

What is encoded: the facts `lt(MV u, MV w)` and `le(MV u, MV w)` of entry j, only for pairs of values u and w of `ran (st π j) ∪ C`, the values of the state and the constants given to the encoding.

What is preserved: on these pairs, exactly `vless` and `vleq` (`enc_db_lt`, `enc_db_le`). This is all the comparisons need: the value of an operand of a comparison is a value of the state or a constant of the condition (`evalV_ran`), and `bridge_true` and `bridge_false` assume `econsts c ⊆ C`.

What is not: the class `value_order` of the core fixes `vless` and `vleq` and assumes nothing about them, so the bridge states no law of order (transitivity, irreflexivity, totality, or the relation between `vless` and `vleq`). For MFOTL, `lt` and `le` are facts of the database like any other: its formulas do not know that they are transitive. Comparisons of values outside C and outside the state of the entry are not encoded, so a formula that compares such a value with `lt` or `le` finds no fact.

### What the bridge does not claim

- **Prefix and infinite trace.** An MFOTL trace is infinite, and `enc_pre` fixes only its first |π| entries. The theorems of part 1 are about one entry j < |π| and its state. They say nothing about the entries after the prefix, nor about a temporal formula whose truth depends on them, and no verdict of the core (prohibitions, obligations, deadlines) is translated in part 1. Part 2 translates verdicts of norms.
- **Enforcement.** `bridge_blocks_cond` relates the condition under which the core blocks to `Nc c` in one state. It does not translate the monitor of the core (`enforce`), and it does not claim that an MFOTL monitor enforces anything.
- **Completions.** The bridge does not relate `Pc` and `Nc` to the completions of the data (`TRIEL_Completions`). For a condition without PRESENT and DEFAULT, that it stays true or false in every completion is a theorem of the core (`breach_certain_completions`, `monitor_sound_completions`), not of the bridge; a condition with PRESENT or DEFAULT need not keep its value when data are added (`T3_present_not_monotone`, `T3_default_not_monotone`).
- **`kleene_optimal`.** The bridge does not claim that `Pc` and `Nc` are the most defined sound reading of a condition; it translates the strong Kleene evaluation of the core as it is.
- **Infinitely many facts.** The databases of an MFOTL trace are finite. If a state of π has infinitely many names, or the values of C give infinitely many facts `lt` or `le`, no MFOTL trace encodes π, and the theorems about encodings say nothing about π.
- **The algorithms of the AFP.** The theorems relate the core to the satisfaction relation `Formula.sat` of MFOTL. They say nothing about the algorithms of the AFP: the checker and the monitor of `MFOTL_Checker`, or the monitor of `MFOTL_Monitor`.

## Part 2: norms and deadlines

### The formulas

Part 2 reads the verdicts of section 8 of [`../core/CORE.md`](../core/CORE.md) on the prefix `pre π j` of an implementation trace π, its entries 0 to j. It reads them at entry j of an encoding σ of π. Time is counted from entry 0, the activation entry. For a trace π and an encoding σ of π, the timestamp of entry 0 of σ is 0 (`enc_tau0`), and for j < |π| that of entry j is `time π j − time π 0`, as a natural number (`enc_tau`). A formula takes the parameters of the norm and the activation time τ₀, an integer; no formula takes a trace. The theorems put τ₀ = `time π 0`. A window of the core is (lo, d]: lo is `None` without FROM, so the window is (−∞, d], and lo is `Some (f − 1)` with FROM f.

`Once I φ`, `Prev I φ` and `Eventually I φ` are the operators `formula.Once`, `formula.Prev` and `formula.Eventually` of MFOTL with the interval I. `all` is the interval `Interval.all`, from 0 to ∞, and [l, r] is `Interval.interval l r`. The intervals of MFOTL are closed on both sides. `Pc c` and `Nc c` are the formulas of part 1.

The time of an entry (`TRIEL_MFOTL_Time`):

- `First` = `¬ Prev all TT`: holds exactly at entry 0 (`sat_First`).
- `At I` = `Once I First`: the timestamp of the entry, counted from entry 0, is in I (`sat_At`).
- `rel_lo τ₀ lo`, a number, not a formula: the lower bound of the window as a distance from τ₀. It is 0 if lo is `None`, and `nat (l + 1 − τ₀)` if lo is `Some l`: times are integers, so "strictly after l" is "from l + 1 on".
- `InWin τ₀ lo d` = `At [rel_lo τ₀ lo, d − τ₀]`, or `FF` if d < τ₀ or d − τ₀ < `rel_lo τ₀ lo`: the times of the window (lo, d].
- `AfterLo τ₀ lo` = `At [rel_lo τ₀ lo, ∞]`: the times after lo.
- `Passed τ₀ d` = `At [d − τ₀ + 1, ∞]`, or `TT` if d < τ₀: the times strictly after d.

Norms (`TRIEL_MFOTL_Norm`):

- `Act s a` = `act(MS s, MA a)`, the fact `act` of the encoding: this entry is an action a of s.
- `Acted τ₀ s a lo d` = `Once all (Act s a ∧ InWin τ₀ lo d)`: at some entry up to this one, s took the action a at a time of the window (lo, d].
- `ObBre τ₀ s a lo d` = `¬ Acted τ₀ s a lo d ∧ Passed τ₀ d`: there is no such entry, and this entry is strictly after d.
- `ActedN τ₀ s a lo` = `Once all (Act s a ∧ AfterLo τ₀ lo)`: at some entry up to this one, s took the action a at a time after lo.
- `Forb s a c` = `Act s a ∧ Prev all (Pc c)`: this entry is the action a of s, and c was true at the entry before it.
- `PrBre s a c` = `Once all (Forb s a c)`: some entry up to this one is a forbidden action.
- `PrFirst s a c` = `Forb s a c ∧ ¬ Prev all (PrBre s a c)`: this entry is a forbidden action, and no earlier entry is one.
- `Blk s a c` = `Act s a ∧ Prev all (¬ Nc c)`: this entry is the action a of s, and c was not known to be false at the entry before it.
- `Fresh m x` = `Once [0, m] arr(MN x)` (for m < 0: `[0, 0]`): for 0 ≤ m, data for x arrived at an entry at most m time units before this one.
- `ElseIn τ₀ s a d` = `¬ Acted τ₀ s a None d ∧ Passed τ₀ d`: the trace passed d without the action, so the fallback is in force.

The future (`TRIEL_MFOTL_Future`):

- `ObFut n s a` = `Eventually [0, n] (Act s a)`: read at entry 0, s takes the action a at an entry at most n time units after entry 0.

`after lo t` is the predicate of the core: lo is `None`, or lo is `Some l` with l < t. For a trace π, an encoding σ of π, j < |π| and τ₀ = `time π 0`, `InWin τ₀ lo d` holds at j exactly when `after lo (time π j)` and `time π j ≤ d` (`sat_InWin`). `AfterLo τ₀ lo` holds at j exactly when `after lo (time π j)` (`sat_AfterLo`). `Passed τ₀ d` holds at j exactly when d < `time π j` (`sat_Passed`). For an encoding σ of π and j < |π|, `Act s a` holds at j exactly when j ≥ 1 and the event of entry j is an action a of s (`sat_Act`). For WITHIN k without FROM, with d = τ₀ + k and 0 ≤ k, `InWin τ₀ None d` is `At [0, k]` and `Passed τ₀ d` is `At [k + 1, ∞]`, whatever τ₀ is (`InWin_within`, `Passed_within`).

### What is proved

The theorems of part 2, as `Accept_MFOTL2.thy` restates them. All are in `TRIEL_MFOTL_Norm`, except `bridge_window_future`, which is in `TRIEL_MFOTL_Future`. All but `bridge_window_future` have three premises: π is a trace of the core (`is_trace π`), σ encodes π (`enc_pre C π σ`), and j < |π|. Further premises are named with each theorem. In the formulas, τ₀ is `time π 0`. "On the prefix up to j" means on `pre π j`. "Holds at j" means `Formula.sat σ v j`, and every theorem holds for every valuation v. A theorem with several clauses is restated clause by clause.

Obligations. `window s a lo d` is the verdict of s MUST a with the window (lo, d] (BY, WITHIN, FROM). On the prefix up to j:

- `bridge_window_fulfilled`: the window is Fulfilled exactly when `Acted τ₀ s a lo d` holds at j.
- `bridge_window_breached`: it is `Breached t` exactly when t = d and `ObBre τ₀ s a lo d` holds at j.
- `bridge_window_pending`: it is Pending exactly when neither `Acted τ₀ s a lo d` nor `ObBre τ₀ s a lo d` holds at j.
- `bridge_ob_no_deadline`: an obligation without a deadline (`ob_verdict s a lo None`) is Fulfilled if `ActedN τ₀ s a lo` holds at j, and Pending otherwise.

Prohibitions, the monitor and permissions. These theorems have the further premise `econsts c ⊆ C`.

- `bridge_pr_breached`: on the prefix up to j, s MUST_NOT a WHEN c (`pr_verdict s a c`) is `Breached t` for some t exactly when `PrBre s a c` holds at j.
- `bridge_pr_pending`: on the prefix up to j, it is Pending exactly when `PrBre s a c` does not hold at j.
- `bridge_pr_time`: on the prefix up to j, it is `Breached t` exactly when `PrFirst s a c` holds at some entry k ≤ j with `time π k` = t.
- `bridge_blocked_action`: entry j of π is a blocked action of the prohibition (`blocked_action s a c π j`) exactly when `Blk s a c` holds at j.
- `bridge_may`: on the prefix up to j, s MAY a WHEN c (`may_verdict s a c`) is Fulfilled exactly when `PrBre s a c` holds at j.

Fresh factors (MAX_AGE).

- `bridge_fresh`: if 0 ≤ m, x is fresh at entry j with the maximum age m (`fresh m x π j`) exactly when `Fresh m x` holds at j.

Fallbacks (ELSE). `else_verdict s a d s′ a′ D′` is the status of s MUST a with the deadline d and the fallback s′ MUST a′ with the deadline D′. The window of the fallback is (d, d′] for D′ = `Some d′`, and the times after d for D′ = `None`. On the prefix up to j:

- `bridge_else`, for D′ = `Some d′`:
  - (1) the status is EFulfilled exactly when `Acted τ₀ s a None d` holds at j;
  - (2) it is `EElse d Fulfilled` exactly when `ElseIn τ₀ s a d ∧ Acted τ₀ s′ a′ (Some d) d′` holds at j;
  - (3) it is `EElse d (Breached d′)` exactly when `ElseIn τ₀ s a d ∧ ObBre τ₀ s′ a′ (Some d) d′` holds at j;
  - (4) it is EPending exactly when neither `Acted τ₀ s a None d` nor `Passed τ₀ d` holds at j.
- `bridge_else_alt_pending`, for D′ = `Some d′`: the status is `EElse d Pending` exactly when `ElseIn τ₀ s a d` holds at j and neither `Acted τ₀ s′ a′ (Some d) d′` nor `ObBre τ₀ s′ a′ (Some d) d′` does.
- `bridge_else_no_deadline`, for D′ = `None`:
  - (1) the status is EFulfilled exactly when `Acted τ₀ s a None d` holds at j;
  - (2) it is `EElse d Fulfilled` exactly when `ElseIn τ₀ s a d ∧ ActedN τ₀ s′ a′ (Some d)` holds at j;
  - (3) it is `EElse d Pending` exactly when `ElseIn τ₀ s a d` holds at j and `ActedN τ₀ s′ a′ (Some d)` does not;
  - (4) it is EPending exactly when neither `Acted τ₀ s a None d` nor `Passed τ₀ d` holds at j.

Handlers of a breach (ON_BREACH). `handle_breach b lo s a d acts` is the status of s MUST a with the window (lo, d], the start b of the obligation and the handler acts. CURE_BY k opens a second window (d, d + k] for the same action. ESCALATE_TO s′ gives s′ the window (d, d + (d − b)] for the same action. On the prefix up to j:

- `bridge_handle_open`, for every acts:
  - (1) the status is SFulfilled exactly when `Acted τ₀ s a lo d` holds at j;
  - (2) it is SPending exactly when neither `Acted τ₀ s a lo d` nor `ObBre τ₀ s a lo d` holds at j.
- `bridge_terminate`: if `cont_of acts = Some Terminate` (TERMINATE), the status is `SBreached d Terminated` exactly when `ObBre τ₀ s a lo d` holds at j.
- `bridge_no_continuation`: if `cont_of acts = None` (no TERMINATE, CURE_BY or ESCALATE_TO), the status is `SBreached d NoContinuation` exactly when `ObBre τ₀ s a lo d` holds at j.
- `bridge_cure`, if `cont_of acts = Some (CureBy k)` (CURE_BY k):
  - (1) the status is `SBreached d (Cure Fulfilled)` exactly when `ObBre τ₀ s a lo d ∧ Acted τ₀ s a (Some d) (d + k)` holds at j;
  - (2) it is `SBreached d (Cure (Breached (d + k)))` exactly when `ObBre τ₀ s a lo d ∧ ObBre τ₀ s a (Some d) (d + k)` holds at j;
  - (3) it is SFulfilled exactly when `Acted τ₀ s a lo d` holds at j.
- `bridge_cure_pending`, under the same premise: the status is `SBreached d (Cure Pending)` exactly when `ObBre τ₀ s a lo d` holds at j and neither `Acted τ₀ s a (Some d) (d + k)` nor `ObBre τ₀ s a (Some d) (d + k)` does.
- `bridge_escalate`, if `cont_of acts = Some (EscalateTo s′)` (ESCALATE_TO s′):
  - (1) the status is `SBreached d (Escalated s′ Fulfilled)` exactly when `ObBre τ₀ s a lo d ∧ Acted τ₀ s′ a (Some d) (d + (d − b))` holds at j;
  - (2) it is `SBreached d (Escalated s′ (Breached (d + (d − b))))` exactly when `ObBre τ₀ s a lo d ∧ ObBre τ₀ s′ a (Some d) (d + (d − b))` holds at j.
- `bridge_escalate_pending`, under the same premise: the status is `SBreached d (Escalated s′ Pending)` exactly when `ObBre τ₀ s a lo d` holds at j and neither `Acted τ₀ s′ a (Some d) (d + (d − b))` nor `ObBre τ₀ s′ a (Some d) (d + (d − b))` does.

The future. This theorem has no encoding σ and no entry j among its premises. It assumes that π is a trace of the core, that C is finite, that every state of π has finitely many names, and that `time π 0 ≤ d`. Let n be d − τ₀, a natural number.

- `bridge_window_future`:
  - (1) the window without FROM on π (`window s a None d π`) is Fulfilled exactly when `ObFut n s a` holds at entry 0 of every MFOTL trace σ with `enc_pre C π σ`;
  - (2) it is `Breached d` exactly when `ObFut n s a` fails at entry 0 of every MFOTL trace σ with `enc_pre C π σ`.

No theorem of part 2 has a premise on the completeness of the data. Only the theorems on prohibitions, the monitor and permissions assume `econsts c ⊆ C`. The theorems rest on these lemmas: `enc_tau0` and `enc_tau` (the times of an encoding); `sat_InWin`, `sat_AfterLo`, `sat_Passed` and `sat_Act` (above); `acted_pre`, `passed_pre` and `forbidden_pre` (the predicates of the core on a prefix are statements about the entries 0 to j of π); `sat_Acted` (`Acted` is `acted` of the core on the prefix); `window_pre_sat` (the verdict of a window read from `Acted` and `Passed`); `sat_Forb`, `sat_PrBre` and `sat_PrFirst` (the forbidden actions of the core); `else_pre_sat` and `else_none_pre_sat` (the status of a fallback); `sat_ObFut` (what `ObFut` says at entry 0) and `enc_pre_ext` (an encoding whose entry after the prefix has a chosen finite database and the last time of the prefix, and whose later entries are empty). `sat_Forb` uses `bridge_true` of part 1, and `bridge_blocked_action` uses `bridge_false`. `TRIEL_MFOTL_Norm` also proves `bridge_window_last`: for a trace π and an encoding σ of π, the window on the whole of π is Fulfilled exactly when `Acted τ₀ s a lo d` holds at entry |π| − 1, and `Breached d` exactly when `ObBre τ₀ s a lo d` does. `Accept_MFOTL2.thy` does not restate it.

### What the bridge does not claim

- **Prefix and future.** The theorems of `TRIEL_MFOTL_Norm` are about an entry j < |π| of one encoding σ. Only `bridge_window_future` quantifies over all encodings of π. It has a clause for Fulfilled and one for `Breached d`; no theorem reads Pending from `ObFut`.
- **FROM and the other norms in the future.** `ObFut` is given only for a window without FROM whose deadline is not before the activation (`time π 0 ≤ d`). No formula of bounded future is given for a window with FROM, an obligation without a deadline, a prohibition, a permission, a fallback, a handler or a fresh factor. For these, part 2 has only the past-time formulas.
- **Finality.** The bridge reads a verdict on one prefix. Whether a verdict, once reached, stays when the trace is extended is a matter of the core (`window_final`, `ob_verdict_final`, `pr_verdict_final`, `else_final`, `handle_breach_final`), not of the bridge.
- **Deadlines as numbers.** The theorems take the deadlines, the lower bounds of windows, the start b and the durations as given numbers (d, d′, lo, b, k and m). The bridge does not translate how the core resolves a deadline or a start at activation, also from a factor, or when it rejects an activation (`resolve`, `activates`, `start_of`, `lo_of`, `else_deadline`).
- **Blocks and handlers as written.** The theorems are about one norm with its parameters. The bridge does not translate a TERMS block, the binding of a handler (`bound_to`, `wf_block`), or the trace semantics of terms (section 4 of `CORE.md`). The theorems constrain a handler only through `cont_of acts`: NOTIFY, PENALTY and the amount of a penalty (`TRIEL_Penalty`) are not translated.
- **Enforcement.** `bridge_blocked_action` translates the decision of the monitor at one entry (`blocked_action`). The bridge does not translate the monitor as a function (`enforce`) or the list of its decisions (`monitor_decisions`). It does not claim that an MFOTL monitor enforces anything.
- **Stale factors.** `bridge_fresh` translates `fresh`. The bridge does not translate the state under ON_STALE BLOCK, in which a stale factor is absent (`blocked`). `Forb` and `Blk` read the condition in the encoded state of the entry before the action.
- **More data.** The bridge does not relate the formulas of part 2 to a trace with more data (`data_le`) or to the completions of the data. How the verdicts behave there is a matter of the core (sections 8.2 and 8.5 of `CORE.md`).
- **Absolute time.** The formulas know only the time since the activation entry. For a deadline given as a date the formula depends on the activation time τ₀; it is shown not to depend on τ₀ only for WITHIN k without FROM (`InWin_within`, `Passed_within`). Invariants (`TRIEL_Invariants`) and signals (`TRIEL_Signals`) are not translated.
- **Encodings.** The theorems of `TRIEL_MFOTL_Norm` assume an encoding σ of π. If none exists (see "Infinitely many facts" in part 1), they say nothing about π.
- **The algorithms of the AFP.** As in part 1, the theorems are about `Formula.sat`. They say nothing about the checker and the monitor of `MFOTL_Checker` or the monitor of `MFOTL_Monitor`, and do not claim that these algorithms accept the formulas of part 2.
