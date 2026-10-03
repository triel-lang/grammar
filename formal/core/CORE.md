# TRIEL core: definitions and theorems

This is a mechanised core of the TRIEL specification language, checked in Isabelle/HOL. The theories are [`TRIEL_Core.thy`](TRIEL_Core.thy) (expressions, sections 1–3) and [`TRIEL_Trace.thy`](TRIEL_Trace.thy) (trace semantics, section 4), and [`ROOT`](ROOT) defines the session `TRIEL_Core`.

It is based only on the public material at <https://github.com/triel-lang/grammar>: TECHNICAL_REPORT.md §2.5 and §2.9, and FOUNDATIONS.md. It makes no assumptions about any non-public implementation.

To build it, open `Isabelle2025-2\Cygwin-Terminal.bat` on Windows (or any shell on Linux/macOS), go to this folder, and run:

```
isabelle build -D .
```

The build was checked with Isabelle2025-2. The output of a clean build (`isabelle build -c -v -D .`) is saved in [`build.log`](build.log).

## 1. Definitions

**Names, values, states.** *N* and *V* are arbitrary types (the type variables `'n` and `'v` in Isabelle). A state is a partial map

  σ : N ⇀ V,  dom σ = { x | σ x ≠ ⊥ }.

A name outside dom σ is *absent*. FOUNDATIONS.md treats a stale value as absent, so a stale value is outside dom σ too.

**Information order.**

  σ ⊑ σ′  ⟺  ∀x ∈ dom σ. σ′ x = σ x.

σ′ agrees with σ wherever σ is defined, and it may also define more names. This is the same relation as HOL's `⊆ₘ`, so it is a partial order (`info_le_refl`, `info_le_trans`, `info_le_antisym`).

**Syntax.** Expressions have two sorts, so that `eval` can return a truth value:

  a ::= c | x                          (value constant c ∈ V, name x ∈ N)
  e ::= true | false | a₁ = a₂ | NOT e | e₁ AND e₂ | e₁ OR e₂ | e₁ IMPLIES e₂ | PRESENT(x)

Value constants and names can only appear as operands of `=`. A name cannot be used directly as a boolean, because its value is in V and not in the truth values.

**Truth values.** 𝔹⊥ = {T, F, ⊥}, represented as `bool option` with ⊥ = `None`.

**Strong Kleene connectives**, as specified in §2.9:

- ¬T = F, ¬F = T, ¬⊥ = ⊥.
- p ∧ q = F if p = F or q = F; T if p = q = T; otherwise ⊥.
- p ∨ q = T if p = T or q = T; F if p = q = F; otherwise ⊥.
- p → q = T if p = F or q = T; F if p = T and q = F; otherwise ⊥. Lemma `kimp_kor_knot` shows this equals ¬p ∨ q.

**Evaluation.** ⟦a⟧σ ∈ V ∪ {⊥} and ⟦e⟧σ ∈ 𝔹⊥:

- ⟦c⟧σ = c and ⟦x⟧σ = σ x.
- ⟦true⟧σ = T and ⟦false⟧σ = F.
- ⟦a₁ = a₂⟧σ is ⊥ if either ⟦aᵢ⟧σ = ⊥. Otherwise it is T if ⟦a₁⟧σ = ⟦a₂⟧σ, and F if they differ.
- ⟦NOT e⟧σ = ¬⟦e⟧σ. AND, OR and IMPLIES are interpreted by ∧, ∨ and → above.
- ⟦PRESENT(x)⟧σ = (x ∈ dom σ). This is always defined.

**Auxiliary notions.**

- *PRESENT-free*: e contains no PRESENT subterm (`present_free`).
- *names(e)*: the names that occur as comparison operands (`names`). PRESENT arguments are not counted, because PRESENT never reads a value. *pnames(e)* is the set of PRESENT arguments.
- *Classical semantics* ⟦e⟧ᶜ(D, ρ) ∈ {T, F} (`ceval`) takes a **total** valuation ρ : N → V and a set D ⊆ N of present names. It uses the ordinary two-valued connectives and ⟦PRESENT(x)⟧ᶜ = (x ∈ D).
- *Definedness order* on partial results: p ≼ q ⟺ (p = ⊥ ∨ p = q) (`approx`).

## 2. Theorems

All of the following are proved in `TRIEL_Core.thy`. There is no `sorry` and no `oops`.

### T1: algebraic laws (`T1_*`)

For all e, e₁, e₂, e₃ and σ:

- ⟦e₁ AND e₂⟧σ = ⟦e₂ AND e₁⟧σ and ⟦e₁ OR e₂⟧σ = ⟦e₂ OR e₁⟧σ
  — AND and OR are commutative, including when an operand is ⊥.
- ⟦(e₁ AND e₂) AND e₃⟧σ = ⟦e₁ AND (e₂ AND e₃)⟧σ, and the same for OR
  — AND and OR are associative, so chains of either need no brackets.
- ⟦NOT (e₁ AND e₂)⟧σ = ⟦NOT e₁ OR NOT e₂⟧σ and ⟦NOT (e₁ OR e₂)⟧σ = ⟦NOT e₁ AND NOT e₂⟧σ
  — De Morgan's laws hold in strong Kleene logic.
- ⟦NOT NOT e⟧σ = ⟦e⟧σ
  — double negation cancels, since ¬¬⊥ = ⊥.

### T2: monotonicity (`T2_monotone`, from `eval_mono`)

  e PRESENT-free ∧ σ ⊑ σ′ ∧ ⟦e⟧σ = b ≠ ⊥  ⟹  ⟦e⟧σ′ = b.

Explanation: once a PRESENT-free expression has a definite value, giving more names a value cannot change that value.

**Relation to TECHNICAL_REPORT.md §2.9.** T2 is the monotonicity claim of §2.9, *"every expression form other than `PRESENT` and `DEFAULT` is monotone in the information order"*, stated for this core. The core does not include `DEFAULT`, so "other than PRESENT and DEFAULT" becomes "PRESENT-free". The §2.9 phrase "has the same value on any data that extends it" is the conclusion ⟦e⟧σ′ = ⟦e⟧σ for σ ⊑ σ′. The proof uses the stronger statement ⟦e⟧σ ≼ ⟦e⟧σ′ (`eval_mono`): every Kleene connective and the comparison are monotone in ≼.

### T3: PRESENT is not monotone (`T3_present_not_monotone`)

  ∃ σ, σ′, x.  σ ⊑ σ′ ∧ ⟦PRESENT(x)⟧σ ≠ ⟦PRESENT(x)⟧σ′.

Explanation: take σ = ∅ and σ′ = [x ↦ v]. Then PRESENT(x) changes from F to T, which is why §2.9 excludes PRESENT from the monotonicity claim. Lemma `present_flips` gives the general form: whenever x ∉ dom σ, extending σ with x flips PRESENT(x) from F to T.

### T4: agreement with two-valued logic (`T4_classical`, `T4_classical_the`, `T4_total`)

If names(e) ⊆ dom σ, then for every total ρ that extends σ (∀x ∈ dom σ. σ x = ρ x):

  ⟦e⟧σ ≠ ⊥  and  ⟦e⟧σ = ⟦e⟧ᶜ(dom σ, ρ).

Explanation: when every name the expression reads is defined, the three-valued semantics never produces ⊥ and gives the ordinary Boolean result. One instance is ρ = λx. the(σ x) (`T4_classical_the`).

If in addition pnames(e) ⊆ dom σ, then ⟦e⟧σ = ⟦e⟧ᶜ(N, ρ) (`T4_total`). This is the fully classical reading, in which every name is present and PRESENT is constantly T.

### T5: meaning of PRESENT (`T5_present`)

  ⟦PRESENT(x)⟧σ = T  ⟺  x ∈ dom σ.

Explanation: PRESENT(x) is true exactly when x has a value in the state. Since it is never ⊥ (`eval_present_defined`), it is F exactly when x is absent.

## 3. Modelling choices

- **Two-sorted syntax.** Value expressions and boolean expressions are separate sorts. Evaluation of a boolean expression returns a truth value in 𝔹⊥, while names and value constants denote values in V. In this core, value expressions occur only as the operands of `=`, which corresponds to `==` in the TRIEL grammar.
- **Stale values.** Following FOUNDATIONS.md, a stale value is outside dom σ, so PRESENT(x) is F for a stale x. The `ON_STALE`/`BLOCK` machinery from §2.9 is not modelled.
- **Out of scope.** `DEFAULT`, arithmetic, function calls, and every construct listed as "Open" in FOUNDATIONS.md are outside this core.

## 4. Trace semantics (TECHNICAL_REPORT.md §2.5)

The theory `TRIEL_Trace.thy` imports `TRIEL_Core.thy`. Guards are the expressions of section 1, and "eval(c, σ) = true" means ⟦c⟧σ = T. So an undefined guard (⊥) never interrupts.

### 4.1 Definitions

**Entries and traces.** An entry is a triple (σ, τ, e):

- σ is a state as in section 1. Values have an arbitrary type, so they may themselves be maps.
- τ is a timestamp in a linear order.
- e is the event that produced σ: a deontic event (s, a, p) with p ∈ {must, may, must_not}, the arrival of data from a factor, or a clock tick.

A trace π is a non-empty list of entries whose timestamps do not decrease (`is_trace`). Its last entry has index |π| − 1.

**Fusion and prefixes.**

- π₁ ⌢ π₂ is defined when the last entry of π₁ is the first entry of π₂ (`fusable`). It is π₁ followed by π₂ without its first entry, so the shared entry appears once (`fuse`).
- π[0..k] is the prefix of π that ends at entry k (`pre`).

**Outcomes.**

- o ∈ {Done, Interrupted, Violated}.
- o₁ ⊔ o₂ is the maximum in the order Done < Interrupted < Violated (`ojoin`).
- κ(Done) = κ(Interrupted) = Interrupted and κ(Violated) = Violated (`kappa`).

**Denotations.** ⟦t⟧ is a set of pairs (π, o).

- ⟦s MUST a⟧ = { (π, Done) | the last event of π is (s, a, must) }.
- ⟦s MAY a WHEN c⟧ = { (π, Done) | the last event of π is (s, a, may), |π| ≥ 2, ⟦c⟧σₙ₋₁ = T with n = |π| − 1 } ∪ { (⟨x⟩, Done) | x any entry }.
- ⟦s MUST_NOT a WHEN c⟧ = { (⟨x⟩, Done) | x any entry }.
- ⟦t₁ THEN t₂⟧ = { (π₁ ⌢ π₂, o₂) | (π₁, Done) ∈ ⟦t₁⟧, (π₂, o₂) ∈ ⟦t₂⟧ } ∪ { (π₁, o₁) ∈ ⟦t₁⟧ | o₁ ≠ Done }.
- ⟦t₁ OR t₂⟧ = ⟦t₁⟧ ∪ ⟦t₂⟧.
- ⟦t₁ AND t₂⟧ = { (π, o₁ ⊔ o₂) | π ∈ interleave(π₁, π₂), (π₁, o₁) ∈ ⟦t₁⟧, (π₂, o₂) ∈ ⟦t₂⟧ }. This is defined in the locale `interleaving`, where `interleave` is a parameter.
- **UNLESS.** The guard c *fires* at entry j of π if j < |π| − 1 and ⟦c⟧σⱼ = T (`fires`). Let k be the first entry at which it fires (`first_fire`).
  - If c never fires on π, then ⟦t₁ UNLESS c DO t₂⟧ contains (π, o) ∈ ⟦t₁⟧ unchanged.
  - If it does, it contains (π[0..k] ⌢ π′, κ(o′)) for each (π′, o′) ∈ ⟦t₂⟧.

**Totality.** ⟦t⟧ is *total* if every entry is the first entry of some trace in ⟦t⟧, that is, t can start from any entry (`total`).

### 4.2 Theorems

All of the following are proved in `TRIEL_Trace.thy`, with no `sorry` and no `oops`. The laws of UNLESS are numbered in the order §2.5 lists them.

- **⊔** is commutative, associative and idempotent (`ojoin_commute`, `ojoin_assoc`, `ojoin_idem`). It also satisfies every equation §2.5 states for it (`ojoin_stated_cases`).
- **Law 1** (`unless_false`): t UNLESS false DO e = t.
  — The guard `false` never fires.
- **Law 2** (`unless_or`): (t₁ OR t₂) UNLESS c DO e = (t₁ UNLESS c DO e) OR (t₂ UNLESS c DO e).
  — This follows directly from the union.
- **Law 3** (`unless_then`): if ⟦t₂⟧ is total, then (t₁ THEN t₂) UNLESS c DO e = (t₁ UNLESS c DO e) THEN (t₂ UNLESS c DO e).
  — Both sides watch the guard at the same entries.
  - The entry at which t₁ completes is watched only as the first entry of t₂. So when c first holds exactly at that junction, both sides let t₁ complete and interrupt t₂ at its first entry.
  - The proof goes through lemmas about indices and prefixes of fused traces: `fires_fuse_left`/`_right`, `first_fire_fuse_left`/`_right`, `pre_fuse_left`/`_right` and `fuse_assoc`.
- **Law 3 needs totality** (`unless_then_counterexample`, `unless_then_not_unconditional`).
  — Without totality the equation fails. Take ⟦t₁⟧ = {(⟨x, x⟩, Done)}, ⟦t₂⟧ = ∅, ⟦e⟧ = {(⟨x⟩, Done)} and c = true. The left side is ∅, but the right side contains (⟨x⟩, Interrupted).
- **Law 4** (`unless_idem`): (t UNLESS c DO e) UNLESS c DO e = t UNLESS c DO e.
  — The outer guard first fires at the same entry as the inner one, so e runs once (`refire`).
- **Non-law** (`unless_nested_ne_or`): (t UNLESS c DO e) UNLESS d DO e ≠ t UNLESS (c OR d) DO e for some t, c, d and e.
  — The outer guard d is still watched while the handler e runs, so it can cut e short. The witness uses c = true and d = PRESENT(n).
- **Totality.**
  - MUST, MAY and MUST_NOT are total (`total_must`, `total_may`, `total_mustnot`).
  - THEN, OR and UNLESS preserve totality (`total_then`, `total_or`, `total_unless`).
  - AND preserves totality under the locale assumption (`interleaving.total_and`), and that assumption is satisfiable (`interleaving_satisfiable`).
  - So law 3 holds whenever t₂ is built from these forms.
- **Well-formed traces.** The denotations of MUST, MAY and MUST_NOT contain only traces. THEN, OR and UNLESS preserve this (`wf_must`, `wf_may`, `wf_mustnot`, `wf_then`, `wf_or`, `wf_unless`).

### 4.3 Clarifications of §2.5

In five places the text of §2.5 is incomplete, and this formalisation adopts the following readings.

1. **Fusion.** §2.5 says when π₁ ⌢ π₂ is defined but not what it is. Its explanation of the THEN law ("at m … N−1 by the second", where m is the entry at which t₁ completes) fixes the reading: π₁ followed by π₂ without its first entry.
2. **Combining outcomes.** The equations for ⊔ leave Interrupted ⊔ Done and Violated ⊔ Done undefined. Read literally, they also give Violated ⊔ Interrupted = Interrupted but Interrupted ⊔ Violated = Violated. ⊔ is taken to be the maximum in Done < Interrupted < Violated, which agrees with every stated equation when "otherwise" is read as "when o ≠ Violated".
3. **Interleaving.** `interleave` is not defined. It is a parameter, constrained only by one assumption: If t1 and t2 are total, then for every entry x there are traces of t1 and of t2 that start at x and have at least one interleaving starting at x.
4. **Law 3.** §2.5 states it without a side condition, but it needs ⟦t₂⟧ to be total (see the counterexample above). Every term form with a denotation in §2.5 gives a total denotation (AND under the interleaving assumption of item 3).
5. **MAY.** eval(c, σₙ₋₁) with n = |π| − 1 has no state to refer to when π has a single entry. So a taken action gives a trace of at least two entries, and c is evaluated in the state before the action.

### 4.4 Not formalised

These term forms have no denotation in §2.5 and are outside this theory: `IF c THEN t`, `WHEN c THEN t`, `ON … DO`, `WITHIN … ELSE`, `REF`, `EXECUTE` and `ON_BREACH`. The breach and deadline semantics of §2.6 and the satisfaction of `INVARIANTS` are not formalised either.
