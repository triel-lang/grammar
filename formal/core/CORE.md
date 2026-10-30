# TRIEL core: definitions and theorems

This is a mechanised core of the TRIEL specification language, checked in Isabelle/HOL. The theories are [`TRIEL_Core.thy`](TRIEL_Core.thy) (expressions, sections 1–3), [`TRIEL_Trace.thy`](TRIEL_Trace.thy) (trace semantics, section 4), [`TRIEL_Ex.thy`](TRIEL_Ex.thy) (the indicator predicate *Ex*, section 5), [`TRIEL_Terms.thy`](TRIEL_Terms.thy) (the term language, section 6), [`TRIEL_ND.thy`](TRIEL_ND.thy) (nominative data, section 7) [`TRIEL_Breach.thy`](TRIEL_Breach.thy) (deadlines and breach, section 8), [`TRIEL_Completions.thy`](TRIEL_Completions.thy) (completions of the data, section 8.5), [`TRIEL_Invariants.thy`](TRIEL_Invariants.thy) (invariants, section 10), [`TRIEL_Indicators.thy`](TRIEL_Indicators.thy) (the indicators E_z and ↓z and the stability of verdicts, section 7.2), [`TRIEL_Compositions.thy`](TRIEL_Compositions.thy) (the quantifier, renomination, closure under the base compositions, and conditions as terms, section 7.3), [`TRIEL_Numbers.thy`](TRIEL_Numbers.thy) (the numeric types Integer and Decimal, section 10.4), [`TRIEL_Penalty.thy`](TRIEL_Penalty.thy) (the amount of a penalty, section 8.4) and [`TRIEL_Exec.thy`](TRIEL_Exec.thy) (the evaluator exported to Haskell, section 10). [`ROOT`](ROOT) defines the session `TRIEL_Core`. `TRIEL_ND.thy` uses the finite maps of `HOL-Library`.

It is based only on the public material at <https://github.com/triel-lang/grammar>: TECHNICAL_REPORT.md §2.5–§2.9, and FOUNDATIONS.md. It makes no assumptions about any non-public implementation.

To build it, open `Isabelle2025-2\Cygwin-Terminal.bat` on Windows (or any shell on Linux/macOS), go to this folder, and run:

```
isabelle build -D .
```

`isabelle build -e -D .` also writes the exported evaluator to `evaluator/generated/`.

The build was checked with Isabelle2025-2. The output of a clean build (`isabelle build -c -v -D .`), with the PDF document, is saved in [`build.log`](build.log); it was produced on Linux, in the Docker image `makarius/isabelle:Isabelle2025-2` with TeX Live added.

The build also typesets the theories, with a short introduction ([`document/root.tex`](document/root.tex)), into `output/document.pdf`. This step needs a LaTeX installation that provides `lualatex`, for example MiKTeX or TeX Live.

## 1. Definitions

**Names, values, states.** *N* and *V* are arbitrary types (the type variables `'n` and `'v` in Isabelle). A state is a partial map

  σ : N ⇀ V,  dom σ = { x | σ x ≠ ⊥ }.

A name outside dom σ is *absent*. FOUNDATIONS.md treats a stale value as absent, so a stale value is outside dom σ too.

**Information order.**

  σ ⊑ σ′  ⟺  ∀x ∈ dom σ. σ′ x = σ x.

σ′ agrees with σ wherever σ is defined, and it may also define more names. This is the same relation as HOL's `⊆ₘ`, so it is a partial order (`info_le_refl`, `info_le_trans`, `info_le_antisym`).

**Syntax.** Expressions have two sorts, so that `eval` can return a truth value:

  a ::= c | x | DEFAULT(x, a)          (value constant c ∈ V, name x ∈ N)
  e ::= true | false | a₁ = a₂ | a₁ < a₂ | a₁ ≤ a₂ | NOT e | e₁ AND e₂ | e₁ OR e₂ | e₁ IMPLIES e₂ | PRESENT(x)

Value constants, names and `DEFAULT` can only appear as operands of the comparisons `=`, `<` and `≤`. A name cannot be used directly as a boolean, because its value is in V and not in the truth values.

**Order on values.** The ordering comparisons need two relations on V, `vless` and `vleq`. They are the parameters of the class `value_order`, which assumes nothing about them, so every theorem holds for every choice. The evaluator instantiates them with the order of exact numbers (section 10.4).

**Truth values.** 𝔹⊥ = {T, F, ⊥}, represented as `bool option` with ⊥ = `None`.

**Strong Kleene connectives**, as specified in §2.9:

- ¬T = F, ¬F = T, ¬⊥ = ⊥.
- p ∧ q = F if p = F or q = F; T if p = q = T; otherwise ⊥.
- p ∨ q = T if p = T or q = T; F if p = q = F; otherwise ⊥.
- p → q = T if p = F or q = T; F if p = T and q = F; otherwise ⊥. Lemma `kimp_kor_knot` shows this equals ¬p ∨ q.

**Evaluation.** ⟦a⟧σ ∈ V ∪ {⊥} and ⟦e⟧σ ∈ 𝔹⊥:

- ⟦c⟧σ = c and ⟦x⟧σ = σ x. ⟦DEFAULT(x, a)⟧σ = σ x if x ∈ dom σ, and ⟦a⟧σ otherwise (`evalV_default`).
- ⟦true⟧σ = T and ⟦false⟧σ = F.
- ⟦a₁ = a₂⟧σ is ⊥ if either ⟦aᵢ⟧σ = ⊥. Otherwise it is T if ⟦a₁⟧σ = ⟦a₂⟧σ, and F if they differ.
- ⟦a₁ < a₂⟧σ and ⟦a₁ ≤ a₂⟧σ are ⊥ if either ⟦aᵢ⟧σ = ⊥. Otherwise they are vless(⟦a₁⟧σ, ⟦a₂⟧σ) and vleq(⟦a₁⟧σ, ⟦a₂⟧σ).
- ⟦NOT e⟧σ = ¬⟦e⟧σ. AND, OR and IMPLIES are interpreted by ∧, ∨ and → above.
- ⟦PRESENT(x)⟧σ = (x ∈ dom σ). This is always defined.

**Auxiliary notions.**

- *PRESENT-free*: e contains no PRESENT subterm and no DEFAULT (`present_free`, with `default_free` for value expressions). §2.9 excepts both forms from monotonicity (T3 and `T3_default_not_monotone`).
- *names(e)*: the names that occur as comparison operands (`names`). PRESENT arguments are not counted, because PRESENT never reads a value; the first argument of DEFAULT is not counted either, because DEFAULT reads it only when it is present. *pnames(e)* is the set of PRESENT arguments and first arguments of DEFAULT.
- *Classical semantics* ⟦e⟧ᶜ(D, ρ) ∈ {T, F} (`ceval`) takes a **total** valuation ρ : N → V and a set D ⊆ N of present names. It uses the ordinary two-valued connectives, vless and vleq for the ordering comparisons, ⟦PRESENT(x)⟧ᶜ = (x ∈ D), and ⟦DEFAULT(x, a)⟧ᶜ = ρ x if x ∈ D, ⟦a⟧ᶜ otherwise.
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

**Relation to TECHNICAL_REPORT.md §2.9.** T2 is the monotonicity claim of §2.9, *"every expression form other than `PRESENT` and `DEFAULT` is monotone in the information order"*, stated for this core: "other than PRESENT and DEFAULT" is "PRESENT-free", which excludes both. The §2.9 phrase "has the same value on any data that extends it" is the conclusion ⟦e⟧σ′ = ⟦e⟧σ for σ ⊑ σ′. The proof uses the stronger statement ⟦e⟧σ ≼ ⟦e⟧σ′ (`eval_mono`): every Kleene connective and the comparison are monotone in ≼.

### Comparisons (`cmp_undefined`, `cmp_absent_name`, `cmp_mono`)

  ⟦a⟧σ = ⊥ ∨ ⟦b⟧σ = ⊥  ⟹  ⟦a = b⟧σ = ⟦a < b⟧σ = ⟦a ≤ b⟧σ = ⊥, and σ ⊑ σ′ ⟹ ⟦a ∘ b⟧σ ≼ ⟦a ∘ b⟧σ′ for ∘ ∈ {=, <, ≤}.

Explanation: a comparison with an operand that has no value is undefined, like every other condition that reads an absent name, and a definite answer of a comparison survives every extension of the state. The comparisons are PRESENT-free, so T2 and T4 cover them.

### T3: PRESENT is not monotone (`T3_present_not_monotone`)

  ∃ σ, σ′, x.  σ ⊑ σ′ ∧ ⟦PRESENT(x)⟧σ ≠ ⟦PRESENT(x)⟧σ′.

Explanation: take σ = ∅ and σ′ = [x ↦ v]. Then PRESENT(x) changes from F to T, which is why §2.9 excludes PRESENT from the monotonicity claim. Lemma `present_flips` gives the general form: whenever x ∉ dom σ, extending σ with x flips PRESENT(x) from F to T.

DEFAULT is not monotone either (`T3_default_not_monotone`): for v ≠ w, ∅ ⊑ [x ↦ v], DEFAULT(x, w) changes from w to v, and DEFAULT(x, w) = w changes from T to F.

### T4: agreement with two-valued logic (`T4_classical`, `T4_classical_the`, `T4_total`)

If names(e) ⊆ dom σ, then for every total ρ that extends σ (∀x ∈ dom σ. σ x = ρ x):

  ⟦e⟧σ ≠ ⊥  and  ⟦e⟧σ = ⟦e⟧ᶜ(dom σ, ρ).

Explanation: when every name the expression reads is defined, the three-valued semantics never produces ⊥ and gives the ordinary Boolean result. One instance is ρ = λx. the(σ x) (`T4_classical_the`).

T4 holds with DEFAULT: DEFAULT reads its first argument only when it is present, so it needs no condition beyond names(e) ⊆ dom σ.

If in addition pnames(e) ⊆ dom σ, then ⟦e⟧σ = ⟦e⟧ᶜ(N, ρ) (`T4_total`). This is the fully classical reading, in which every name is present and PRESENT is constantly T.

### T5: meaning of PRESENT (`T5_present`)

  ⟦PRESENT(x)⟧σ = T  ⟺  x ∈ dom σ.

Explanation: PRESENT(x) is true exactly when x has a value in the state. Since it is never ⊥ (`eval_present_defined`), it is F exactly when x is absent.

## 3. Modelling choices

- **Two-sorted syntax.** Value expressions and boolean expressions are separate sorts. Evaluation of a boolean expression returns a truth value in 𝔹⊥, while names and value constants denote values in V. In this core, value expressions occur only as the operands of `=`, `<` and `≤`, which correspond to `==`, `<` and `<=` in the TRIEL grammar. `a != b`, `a > b` and `a >= b` are NOT (a = b), b < a and b ≤ a (section 10.6).
- **Stale values.** Following FOUNDATIONS.md, a stale value is outside dom σ, so PRESENT(x) is F for a stale x. The theories of this section do not model when a value becomes stale; `ON_STALE BLOCK` is modelled in sections 8 and 10.4 (`blocked`, `blockp`).
- **Out of scope.** Arithmetic occurs only in the amount of a `PENALTY` (section 8.4). Function calls, and every construct listed as "Open" in FOUNDATIONS.md, are outside this core.

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

- An event e is an *action a of s* if e = (s, a, p) for some polarity p (`does`): the polarity of an event is not part of the match. The first entry of a trace of a term is the entry where the term is reached, and its actions are the events of the later entries.
- ⟦s MUST a⟧ = { (π, Done) | |π| ≥ 2 and the last event of π is an action a of s }.
- ⟦s MAY a WHEN c⟧ = { (π, Done) | the last event of π is an action a of s, |π| ≥ 2, ⟦c⟧σₙ₋₁ = T with n = |π| − 1 } ∪ { (⟨x⟩, Done) | x any entry }.
- The entry j of π is a *forbidden action* of s MUST_NOT a WHEN c if j ≥ 1, the event of entry j is an action a of s, and ⟦c⟧σⱼ₋₁ = T (`forbidden`).
- ⟦s MUST_NOT a WHEN c⟧ = { (⟨x⟩, Done) | x any entry } ∪ { (π, Violated) | π is a trace, its last entry is a forbidden action, and no earlier entry is one }.
- ⟦t₁ THEN t₂⟧ = { (π₁ ⌢ π₂, o₂) | (π₁, Done) ∈ ⟦t₁⟧, (π₂, o₂) ∈ ⟦t₂⟧ } ∪ { (π₁, o₁) ∈ ⟦t₁⟧ | o₁ ≠ Done }.
- ⟦t₁ OR t₂⟧ = ⟦t₁⟧ ∪ ⟦t₂⟧.
- ⟦t₁ AND t₂⟧ = { (π, o₁ ⊔ o₂) | π ∈ interleave(π₁, π₂), (π₁, o₁) ∈ ⟦t₁⟧, (π₂, o₂) ∈ ⟦t₂⟧ }. This is defined in the locale `interleaving`, where `interleave` is a parameter.
- **UNLESS.** The guard c *fires* at entry j of π if j < |π| − 1 and ⟦c⟧σⱼ = T (`fires`). Let k be the first entry at which it fires (`first_fire`).
  - If c never fires on π, then ⟦t₁ UNLESS c DO t₂⟧ contains (π, o) ∈ ⟦t₁⟧ unchanged.
  - If it does, it contains (π[0..k] ⌢ π′, κ(o′)) for each (π′, o′) ∈ ⟦t₂⟧.
- **IF.** ⟦IF c THEN t₁ ELSE t₂⟧ = { (π, o) ∈ ⟦t₁⟧ | ⟦c⟧σ₀ = T } ∪ { (π, o) ∈ ⟦t₂⟧ | ⟦c⟧σ₀ ≠ T }, where σ₀ is the state of the first entry of π (`if_d`).
- **The one-entry term.** ⟦skip⟧ = { (⟨x⟩, Done) | x any entry } (`skip_d`). `IF c THEN t` without `ELSE` is `IF c THEN t ELSE skip`.

**Totality.** ⟦t⟧ is *total* if every entry is the first entry of some trace in ⟦t⟧, that is, t can start from any entry (`total`).

**The same trace with more data.** π′ *refines* π (`data_le π π′`) if π′ has the entries of π, with the same timestamps and events, and at each entry a state with more data (σⱼ ⊑ σ′ⱼ, the information order of section 1). `data_le` is reflexive and transitive and preserves `is_trace`; it is the hypothesis under which the verdicts of sections 8 and 10 are compared on two readings of the same observations.

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
- **UNLESS distributes over IF** (`unless_if`): (IF c THEN t ELSE e) UNLESS d DO h = IF c THEN (t UNLESS d DO h) ELSE (e UNLESS d DO h).
  — Both sides decide the branch on the first entry, and UNLESS keeps the first entry of every trace.
- **Totality.**
  - MUST, MAY, MUST_NOT and skip are total (`total_must`, `total_may`, `total_mustnot`, `total_skip`).
  - THEN, OR, UNLESS and IF preserve totality (`total_then`, `total_or`, `total_unless`, `total_if`).
  - AND preserves totality under the locale assumption (`interleaving.total_and`), and that assumption is satisfiable (`interleaving_satisfiable`).
  - So law 3 holds whenever t₂ is built from these forms.
- **Well-formed traces.** The denotations of MUST, MAY and MUST_NOT contain only traces. THEN, OR, UNLESS and IF preserve this, and skip contains only traces (`wf_must`, `wf_may`, `wf_mustnot`, `wf_then`, `wf_or`, `wf_unless`, `wf_if`, `wf_skip`).
- **Forbidden actions and more data** (`forbidden_data_mono`): for a `PRESENT`-free c, a forbidden action of s MUST_NOT a WHEN c stays forbidden on every refinement of the trace (`data_le`).
  — T2 at the entry before the action.

### 4.3 Clarifications of §2.5

In seven places the text of §2.5 is incomplete, and this formalisation adopts the following readings. Readings 5–7 were revised in version 2.5.1 (section 9, decisions 31 and 32).

1. **Fusion.** §2.5 says when π₁ ⌢ π₂ is defined but not what it is. Its explanation of the THEN law ("at m … N−1 by the second", where m is the entry at which t₁ completes) fixes the reading: π₁ followed by π₂ without its first entry.
2. **Combining outcomes.** The equations for ⊔ leave Interrupted ⊔ Done and Violated ⊔ Done undefined. Read literally, they also give Violated ⊔ Interrupted = Interrupted but Interrupted ⊔ Violated = Violated. ⊔ is taken to be the maximum in Done < Interrupted < Violated, which agrees with every stated equation when "otherwise" is read as "when o ≠ Violated".
3. **Interleaving.** `interleave` is not defined. It is a parameter, constrained only by one assumption: If t1 and t2 are total, then for every entry x there are traces of t1 and of t2 that start at x and have at least one interleaving starting at x.
4. **Law 3.** §2.5 states it without a side condition, but it needs ⟦t₂⟧ to be total (see the counterexample above). Every term form with a denotation in §2.5 gives a total denotation (AND under the interleaving assumption of item 3). For the term language of section 6 this is proved for every term (`den_total`), so law 3 holds there with no side condition (`term_unless_then`).
5. **MAY and MUST.** eval(c, σₙ₋₁) with n = |π| − 1 has no state to refer to when π has a single entry. So a taken action gives a trace of at least two entries, and c is evaluated in the state before the action. The same holds for MUST: the entry where a term is reached is not one of its actions, as in the verdicts of section 8 ("actions are the events of later entries"). Until version 2.5 the one-entry trace whose event was the action belonged to ⟦s MUST a⟧, so `alice MUST pay THEN alice MUST pay` was done after one payment.
6. **MUST_NOT.** §2.5 gives a prohibition only the one-entry trace and says that it constrains the implementation trace as §2.6 states. A prohibition inside a composite term then had no effect at all: no outcome of any term was ever Violated. The denotation adds the traces that end with the first forbidden action, however late, with the outcome Violated. They are the breached traces of `pr_verdict` cut at the breach (`mustnot_violated_breach`, `breach_mustnot_violated`). The prohibition still completes at once, so a term that continues after it does not watch its action (decision 32).
7. **Polarity.** §2.5 writes events as (s, a, polarity) and §2.6 as (s, a, polarity, τ), but neither says what the polarity of an event means. It is ignored in both layers: an event is matched by subject and action (section 8.3, point 3).

### 4.4 Not formalised

These term forms have no denotation in §2.5 and are outside this theory: `ON … DO`, `WITHIN … ELSE`, `EXECUTE` and `ON_BREACH`. (`WITHIN … ELSE` at the top level of a block has a verdict semantics in section 8, and in the trace semantics it is read as the choice of its two obligations, section 10.3.) `IF`, `WHEN` and the one-entry term are in section 6; `REF` is resolved by substitution in section 10.3. The breach and deadline semantics of §2.6 are formalised in section 8, and the satisfaction of `INVARIANTS` in section 10.1.

## 5. The indicator predicate *Ex* (`TRIEL_Ex.thy`)

This section follows the logics of quasiary predicates of Nikitchenko and Shkilniak, in the form given in [5] of `FOUNDATIONS.md` (section 2 there).

### 5.1 Definitions

- **Quasiary predicate.** A quasiary predicate is a map Q from states (nominative data) to 𝔹⊥ (`qpred`). It is determined by its truth domain T(Q) = { d | Q(d) = T } and its falsity domain F(Q) = { d | Q(d) = F } (`truth_dom`, `false_dom`). Since Q has values in 𝔹⊥, these two sets are disjoint (`single_valued`).
- **Total and equitone.** Q is *total* if it is defined everywhere (`total_pred`). Q is *equitone* if Q(d) defined and d ⊑ d′ imply Q(d′) = Q(d) (`equitone`).
- **Total indicator predicate.** E_z has T(E_z) = { d | z ∈ dom d } and F(E_z) = { d | z ∉ dom d } (`Ex_ind`). In Isabelle it is called `Ex_ind`, because `Ex` is HOL's existential quantifier. These two domains determine it uniquely (`Ex_ind_domains`, `Ex_ind_unique`).
- **Weak equality.** =xy has T(=xy) = { d | d(x), d(y) defined and equal } and F(=xy) = { d | d(x), d(y) defined and different } (`weq`). TRIEL's comparison of two names is exactly this predicate (`eval_eq_names`).

### 5.2 Theorems

- **`present_is_Ex`:** ⟦PRESENT(x)⟧ = E_x, as predicates on states.
  — The value-presence predicate of TRIEL is the total indicator predicate.
- **`Ex_ind_total`, `Ex_ind_not_equitone`, `present_total_not_equitone`:** E_x, and so PRESENT(x), is total and not equitone.
  — This is why §2.9 makes PRESENT the exception to monotonicity.
- **`Ex_ind_exists`:** E_x(d) = T ⟺ ∃v. ⟦x = v⟧d = T.
  — This is the free-logic reading E!x ≡ ∃y. y = x.
- **`present_free_equitone`:** every PRESENT-free expression denotes an equitone predicate.
  — This is theorem T2 restated in the terminology of quasiary predicates.
- **`partial_indicator`:** T(=xx) = T(E_x), F(=xx) = ∅, and =xx is equitone.
  — The comparison x = x is the partial indicator predicate. It detects presence but never says "absent". Section 7.2 treats it as the indicator ↓x.

## 6. Terms (`TRIEL_Terms.thy`)

### 6.1 Definitions

- **Terms.** Terms form an inductive type (`tm`):

    t ::= s MUST a | s MAY a WHEN c | s MUST_NOT a WHEN c | t₁ THEN t₂ | t₁ OR t₂ | t₁ UNLESS c DO t₂ | t₁ AND t₂
        | IF c THEN t₁ ELSE t₂ | skip

  `IF c THEN t` without `ELSE` is `IF c THEN t ELSE skip`; `ELIF` is a nested `IF` in the `ELSE` branch; `WHEN c THEN t` is `IF c THEN t`. `REF` is not a term of `tm`: it is resolved into a term by substitution (section 10.3), so every theorem about `tm` covers the terms it produces.

- **Denotation.** The denotation `den` maps each term, structurally, to the denotation of section 4. It is defined in the locale `term_semantics`, which extends `interleaving` with timestamps in a linear order, because AND needs `interleave`.

### 6.2 Theorems

- **`den_total`:** ⟦t⟧ is total for every term t.
  — Every term can start from any entry.
- **`term_unless_false`, `term_unless_or`, `term_unless_idem`:** laws 1, 2 and 4 of §2.5, stated for terms.
- **`term_unless_then`:** ⟦(t₁ THEN t₂) UNLESS c DO e⟧ = ⟦(t₁ UNLESS c DO e) THEN (t₂ UNLESS c DO e)⟧ for all terms t₁, t₂, e and every guard c.
  — Law 3 holds for the term language with no side condition, because every term is total.
- **`term_unless_if`:** ⟦(IF c THEN t ELSE e) UNLESS d DO h⟧ = ⟦IF c THEN (t UNLESS d DO h) ELSE (e UNLESS d DO h)⟧.
- **`den_if`:** (π, o) ∈ ⟦IF c THEN t ELSE e⟧ ⟺ π ≠ ⟨⟩ and (π, o) ∈ ⟦t⟧ if ⟦c⟧σ₀ = T, (π, o) ∈ ⟦e⟧ otherwise, where σ₀ is the first state of π.
  — The condition is evaluated once, where the term is reached.
- **`if_no_else_not_true`:** if ⟦c⟧σ₀ ≠ T at the entry x, then (⟨x⟩, Done) ∈ ⟦IF c THEN t⟧, and it is the only trace of `IF c THEN t` that starts at x.
- **`if_undefined_else`:** if ⟦c⟧σ₀ = ⊥, then IF c THEN t ELSE e has the traces of e that start there, as IF false THEN t ELSE e does.
- **`if_classical`** (from T4): if the first state σ₀ defines names(c) and ρ is a total valuation that extends it, then ⟦IF c THEN t ELSE e⟧ takes t or e as ⟦c⟧ᶜ(dom σ₀, ρ) is T or F.
- **`if_branch_stable`** (from T2): if c is PRESENT-free, σ ⊑ σ₀ and ⟦c⟧σ ≠ ⊥, then every trace whose first state is σ₀ takes the branch chosen in σ.
- **`if_undefined_branch_not_stable`:** the branch taken on ⊥ is not protected: x = v is ⊥ in ∅ and T in [x ↦ v]. Every rule that picks a branch on ⊥ has this property.
- **`must_action`, `must_one_entry`:** every trace of MUST has an action of its subject at an entry j ≥ 1, and no one-entry trace is a trace of MUST.
- **`must_then_must_two_actions`:** no trace of two entries belongs to `s MUST a THEN s MUST a`, with any outcome: two obligations in sequence need two actions.
- **`mustnot_violated`, `violated_reachable`:** a forbidden action after a state where c = T gives a violated trace of `s MUST_NOT a WHEN c`; so the outcome Violated is reached.
- **`then_mustnot_violated`:** the trace activation, (s, a, p), (s′, a′, p′) with c true before the last event is a violated trace of `s MUST a THEN s′ MUST_NOT a′ WHEN c`.

## 7. Nominative data (`TRIEL_ND.thy`)

The values in sections 1–6 have an arbitrary type. This section gives TRIEL data (records, optional values, nesting) the structure of multi-level nominative data. The definition follows the Mizar formalisation of simple-named complex-valued nominative data by Ivanov, Nikitchenko, Kryvolap and Korniłowicz ([7] in `FOUNDATIONS.md`).

### 7.1 Definitions

- **Nominative data.** A datum is an atom (a basic value) or a finite partial map from names to data (`nd`):

    d ::= Atom b | Nom [x₁ ↦ d₁, …, xₖ ↦ dₖ]

  The finite maps are the `fmap` of `HOL-Library`. Data have finite depth, which corresponds to the rank sequences of [7].
- **Operations of [7].**
  - *denaming* x⇒ takes the value of x (`denaming`);
  - *naming* ⇒x builds [x ↦ d] (`naming`);
  - *global overlapping* d₁ ∇ d₂ = d₂ ∪ d₁|(dom d₁ ∖ dom d₂), so d₂ wins (`global_overlapping`);
  - *local overlapping* replaces the value of one name (`local_overlapping`).
- **Complex names.** A complex name p = x₁.x₂.….xₖ, as in TRIEL's `factor_ref`, is a list of names. Its value d(p) is obtained by successive denaming (`den_path`).
- **Information order.** d ≤ d′ (`nd_le`) means two things: every atom of d is an atom of d′ at the same complex name, and every inner node of d is an inner node of d′. So d′ may add names at any depth, but changes or removes nothing.
- **Flattening.** `flat d` is the state over complex names that maps each complex name leading to an atom to that atom (`flat`). This is the bridge to sections 1–5.
- **Expressions.** Expressions are those of section 1 with complex names (`eval_nd`).
  - A complex name denotes a value only when it leads to an atom. If it leads to a record or to nothing, comparisons with it are ⊥.
  - PRESENT(p) is true when p leads to anything, an atom or a record.
- **Indicator predicate.** The total indicator predicate for a complex name is E_p with T(E_p) = { d | d(p)↓ } and F(E_p) = { d | d(p)↑ } (`Ex_nd`).
- **Types.** Types are primitive types (interpreted by a predicate I on atoms), Optional⟨T⟩ and Record {f: T, …} (`ty`). List and Map are not covered.
  - Records are open: a datum may have names the type does not declare, and only declared fields are checked.
  - Optional⟨T⟩ is permitted absence, not a value. The typing judgement `wt I T v` is on v ∈ nd ∪ {absent}.

### 7.2 Theorems

- **`nd_le_refl`, `nd_le_trans`, `nd_le_antisym`:** ≤ is a partial order. `nd_le_NomD` and `nd_le_NomI` describe it node by node.
- **`whole_data_equality_not_monotone`:** for distinct names x and y there are d ≤ d′ with d(x) = d(y) ≠ ⊥ but d′(x) ≠ d′(y).
  — Equality of whole records is not monotone, which is why comparisons see only atoms.
- **`flat_mono`:** d ≤ d′ ⟹ flat d ⊑ flat d′.
- **`eval_nd_flat`:** for PRESENT-free e, evaluation over d equals the evaluation of section 1 over flat d.
  — This is how the theorems of sections 2 and 5 carry over.
- **`T1_nd`:** the algebraic laws T1 over nominative data.
- **`T2_nd_monotone`, `present_free_equitone_nd`:** if e is PRESENT-free, d ≤ d′ and ⟦e⟧d = b ≠ ⊥, then ⟦e⟧d′ = b.
  — This is the monotonicity claim of §2.9 for nested data, derived from T2 through `flat_mono`.
- **`T3_nd_present_not_monotone`:** PRESENT is not monotone under ≤.
- **`T4_nd`:** agreement with two-valued logic, with PRESENT read as presence of a node. For `DEFAULT(p, a)` the classical reading takes p as present when it leads to a node, so T4_nd assumes that the first argument of every `DEFAULT` leads to an atom whenever it leads to anything (`dnames`, `evalV_nd_classical`); the translator rejects `DEFAULT` of a record (section 10.6, rule 8).
- **`T5_nd_present`:** ⟦PRESENT(p)⟧d = T ⟺ d(p)↓.
- **`present_nd_is_Ex`, `Ex_nd_total`, `Ex_nd_not_equitone`:** PRESENT(p) is E_p, and E_p is total and not equitone.
- **`denaming_naming`, `denaming_local_overlapping_same`, `denaming_local_overlapping_other`:** the basic equations of the operations of [7].
- **`wt_required_field_present`:** a declared field whose type contains no Optional is present in every well-typed record.
- **`wt_mono`:** if T contains no Optional (`opt_free`), wt I T d and d ≤ d′, then wt I T d′.
  — Typing is monotone under the information order for such types, because records are open.
- **`wt_not_mono_optional`:** for types with Optional, monotonicity fails.
  — An absent Optional field may be filled, by an extension, with a value of the wrong type. Example: Record {f: Optional⟨T⟩} with an empty datum, extended by [f ↦ a] where a is not of type T.

**Three indicators: absent for good, or not yet known** (`TRIEL_Indicators.thy`). With incomplete data, a name that is absent from a datum can mean two different things.

- *The field is absent for good.* This is how typing reads it: Optional⟨T⟩ permits absence, so the datum is well typed.
- *The value is not yet known.* This is how the information order reads it: an extension may add the name later.

`wt_not_mono_optional` shows that the two readings cannot both hold for Optional. The logics of quasiary predicates have three indicators, and each takes one side. The third one comes from S. S. Shkilniak, 2024 ([8] in `FOUNDATIONS.md`).

| Indicator | Truth domain | Falsity domain | Properties | Source |
|---|---|---|---|---|
| ε_x, oriented to absence (free logic) | { d \| x ∉ dom d } | { d \| x ∈ dom d } | total, not equitone | [2], pp. 265–267 |
| E_x, total | { d \| d(x)↓ } | { d \| d(x)↑ } | total, single-valued, not monotone | [5], [8] |
| ↓x, partial | { d \| d(x)↓ } | ∅ | P-predicate, irrefutable, equitone | [8] |

ε_x is the variable-unassignment predicate of [2] (p. 265). Its truth and falsity domains are defined in [2], p. 266: T(εz) = { d | z ∉ asn(d) } and F(εz) = { d | z ∈ asn(d) }, where asn(d) is the set of names assigned in d. [2] also states that εz is total (p. 267), and that E!z of free logic corresponds to the negation of εz (p. 268). With the negation of [2] (T(¬p) = F(p), F(¬p) = T(p), p. 266) and the definition of E_x in [5], ε_x = ¬E_x. E_x is total and not equitone (`Ex_ind_total`, `Ex_ind_not_equitone`, `Ex_nd_not_equitone`), so ε_x is total and not equitone too. Section 7.3 defines ε_x (`eps_R`) and proves E_x = ¬ε_x (`Ex_R_is_not_eps`).

*Definitions*, as in [8]:

- An R-predicate Q is a pair (T(Q), F(Q)) of a truth domain and a falsity domain (`rpred`, `R_T`, `R_F`). Q[d] is the set of truth values Q takes on d (`rval`). Q is a P-predicate if T(Q) ∩ F(Q) = ∅ (`P_pred`). The value Q(d) ∈ 𝔹⊥ of a P-predicate is `pval`, and `of_qpred` turns a quasiary predicate of section 5 into an R-predicate (`pval_of_qpred`, `of_qpred_pval`).
- d ⊆ d′, the extension of a named set (inclusion of graphs), is the information order ⊑ of section 1. The definitions take the order as a parameter, so they also apply to ≤ on nominative data.
- Q is *monotone* if d₁ ⊆ d₂ ⇒ Q[d₁] ⊆ Q[d₂] (`rmono`), that is, if T(Q) and F(Q) are closed upwards (`rmono_iff`). A P-predicate Q is *equitone* if Q(d) defined and d ⊆ d′ imply Q(d′) = Q(d) (`equitone_R`, `equitone_on`). For P-predicates the two notions coincide (`P_pred_rmono_iff_equitone`).
- E_z (`Ex_R`) has T(E_z) = { d | d(z)↓ } and F(E_z) = { d | d(z)↑ }. ↓z (`DownInd`) has T(↓z) = { d | d(z)↓ } and F(↓z) = ∅.
- In logics with weak equality, ↓z is =zz. As in [8], only the diagonal is used: T(=zz) = { d | d(z)↓ } and F(=zz) = ∅. No general definition of =xy is added; the diagonal is that of TRIEL's comparison `weq` (section 5).
- *Partial presence* of a complex name p (`present_partial`, as an R-predicate `DownInd_nd`) is ↓p on nominative data: T where p leads to an atom or a record, undefined elsewhere.
- A *condition* (`cond`) is built from atoms by NOT, AND and OR, and evaluated with the strong Kleene connectives of section 1 (`cond_eval`). Its verdict is T, F or ⊥. Over nominative data the atoms are E_p (`AEx`), ↓p (`ADown`), "p is an atom of primitive type q" (`AIs`, `is_prim`), which is ⊥ when p leads to nothing and F when it leads to a record, and the comparisons a = b, a < b and a ≤ b of two value expressions (`ACmp`, `crel_expr`), which are ⊥ when an operand does not lead to an atom.

*Theorems* (all in `TRIEL_Indicators.thy`):

- **`T_DownInd_eq_T_Ex`:** T(↓z) = T(E_z).
- **`DownInd_P_pred`, `DownInd_irrefutable`, `DownInd_mono`, `DownInd_equitone`, `DownInd_equitone_R`:** ↓z is a P-predicate, F(↓z) = ∅, and ↓z is monotone and equitone.
- **`DownInd_is_eq_zz`, `self_eq_is_DownInd`:** ↓z is =zz, so on the flat named sets of section 1 ↓z is the comparison `z == z`. On nominative data `p == p` is below ↓p (`self_eq_below_present_partial`): it is ⊥ when p leads to a record.
- **`Ex_R_P_pred`, `Ex_R_total`, `pval_Ex_R_present`:** E_z is single-valued and total, and it is PRESENT(z).
- **`Ex_R_counterexample`, `Ex_R_not_mono`, `Ex_R_not_equitone_R`:** ∅ ⊑ [z ↦ v], with E_z(∅) = F and E_z([z ↦ v]) = T. So E_z[∅] = {F} is not a subset of E_z[[z ↦ v]] = {T}, and E_z is not monotone.
- **`present_partial_domains`, `present_partial_below_present`, `present_partial_mono`, `present_partial_equitone`, `DownInd_nd_equitone_R`:** partial presence has the truth domain of E_p and an empty falsity domain. Wherever it is defined it agrees with PRESENT(p), and it is monotone under the extension ≤ of nominative data.
  — `self_eq_below_present_partial`: the comparison p == p is below ↓p. It is ⊥ when p leads to a record, because comparisons see only atoms.
- **`cmp_equitone`, `cmp_atom_equitone`, `cmp_atom_undefined`:** the comparisons without `DEFAULT` are equitone, on flat states and on nominative data, and a comparison with an operand that has no value is ⊥.
- **`default_breaks_stability`, `default_cmp_not_equitone`:** a comparison with `DEFAULT` is not: on the empty record, extended by [f ↦ v], the condition DEFAULT(f, w) = w changes its verdict from T to F for v ≠ w. So `Ex_free_atom` excludes `DEFAULT` as it excludes E_p, and `verdict_stable`, `verdict_stable_nd` do not cover it.
- **`cond_equitone`, `verdict_stable`, `verdict_stable_nd`:** if every atom of a condition is equitone, the condition is equitone: a definite verdict T or F stays the same under every extension of the data. Over nominative data this holds for every condition whose atoms are ↓p, type checks and comparisons, without E_p.
- **`opt_cond_Ex_wt`, `Ex_breaks_stability`, `Ex_cond_not_equitone`:** with the atom E_p the property fails. The condition "NOT E_f OR f has type q" is the typing judgement of Record {f: Optional⟨q⟩} (`opt_cond_Ex_wt`). On the data of `wt_not_mono_optional` (the empty record, extended by [f ↦ b] where b is not of type q) its verdict changes from T to F.
- **`opt_cond_Down_wt`, `Down_cond_equitone`:** the same condition with ↓f agrees with typing when f is present and is ⊥ when f is absent. On the same data its verdict changes from ⊥ to F, so no definite verdict is overturned.
- **`inv_data_mono_equitone`:** the LTL3 verdicts of invariants (section 10.1) survive more data for every state formula whose predicate is equitone. `inv_data_mono` is the case of PRESENT-free formulas.
- **`equitone_R_not`, `equitone_R_or`, `equitone_closure_equitone`:** the equitone P-predicates are closed under the negation and the disjunction of R-predicates (`R_not`, `R_or`; on P-predicates these are the Kleene ¬ and ∨, `pval_R_not`, `pval_R_or`), and ↓z is one of them. So every predicate built from ↓z and equitone P-predicates by ¬ and ∨ is an equitone P-predicate.

*Reading.* "The field is absent for good" corresponds to E_x on a closed record: E_x(d) = F is a definite answer, and it is right only if no extension can add the field. "The value is not yet known" corresponds to the undefinedness of ↓x: ↓x(d) = ⊥, and an extension can only make it T. A condition written with ↓ never gives a verdict that more data would overturn (`verdict_stable_nd`). A condition written with E_x can (`Ex_breaks_stability`). The meanings of `PRESENT` and of Optional are unchanged: `PRESENT` is E_x (section 9, decision 1), and typing with Optional is still not monotone.

This reading is TRIEL's own; it is not claimed to be the reading of absence intended in the composition-nominative approach.

**Open question.** This is a question of TRIEL's design: should TRIEL read an absence in data that may still arrive as ↓ (not yet known), and an absence in a closed record as E_x (absent for good)?

### 7.3 Compositions (`TRIEL_Compositions.thy`)

[8] states that the class of equitone P-predicates is closed under all base compositions of its algebras (p. 26). Section 7.2 proves this for ¬, ∨ and ↓z. This section adds the quantifier ∃x and renomination, and so checks the claim in full. It also writes the formulas of [8] as terms and shows that every TRIEL condition of section 7.2 is such a term. The definitions are those of [2] and [8], with page numbers.

*Definitions:*

- **Deletion** (`del_names`, [8] p. 24): d‖₋Z = { v ↦ a ∈ d | v ∉ Z }.
- **Extended renomination** (`ren_ext`, [8] p. 24): for distinct upper names v₁, …, vₙ, u₁, …, uₘ with lower names x₁, …, xₙ, ⊥, …, ⊥,
  r(d) = [v₁ ↦ d(x₁), …, vₙ ↦ d(xₙ)] ∪ d‖₋{v₁, …, vₙ, u₁, …, uₘ}.
  The names uⱼ lose their values. The order of the pairs does not matter ([8] p. 24), and [2] (p. 265) reads the parameter as a mapping from the upper names to the lower ones. Here it is a partial map ρ with ρ(vᵢ) = xᵢ and ρ(uⱼ) = ⊥. In the sources the parameter is finite; the definitions and theorems hold for every ρ.
- **Traditional renomination** (`ren`, [2] p. 265): r(d) = [v ↦ a | v ↦ a ∈ d, v ∉ {v₁, …, vₙ}] ∪ [vᵢ ↦ aᵢ | xᵢ ↦ aᵢ ∈ d]. It is the extended renomination without pairs u/⊥ ([8] p. 25; `ren_is_ren_ext`).
- **Quantifier** (`R_ex`, [8] p. 25; the same in [2] p. 266): T(∃xP) = ⋃_{a∈A} { d | d‖₋x ∪ x ↦ a ∈ T(P) } and F(∃xP) = ⋂_{a∈A} { d | d‖₋x ∪ x ↦ a ∈ F(P) }. The named set d‖₋x ∪ x ↦ a, written d∇x ↦ a in [2], is d(x ↦ a) (`del_names_upd`, `R_ex_domains`).
- **Renomination composition** (`R_ren_ext`, `R_ren`; [8] p. 25, [2] p. 266): R(Q)[d] = Q[r(d)] (`rval_R_ren_ext`), that is T(R(Q)) = { d | r(d) ∈ T(Q) } and F(R(Q)) = { d | r(d) ∈ F(Q) }.
- **Base compositions** ([8] p. 25): C↓⊥Q = {¬, ∨, R with extended renomination, ∃x, ↓z} and C↓Q = {¬, ∨, R with traditional renomination, ∃x, ↓z}. E_z is not among them. Conjunction is not a base composition.
- **Variable unassignment** (`eps_R`, [2] p. 266): T(εz) = { d | z ∉ asn(d) } and F(εz) = { d | z ∈ asn(d) }, where asn(d) = dom d ([2] p. 265).
- **Pointwise extension** (`pw_le`): d ≤ d′ if every name that has a value a in d has a value a′ in d′ with a ≤ a′ in a given order on values. With equality on values this is the inclusion d ⊆ d′ of [8], that is ⊑ (`pw_le_eq`). This order is not in the sources. It is used so that one proof covers both flat named sets and nominative data.
- **Formulas** (`fm`, [8] §2, p. 26): Fa) base predicate symbols; F↓) ↓z; Fp) ¬Φ and ∨ΦΨ; FR⊥) RΦ with extended renomination; F∃) ∃xΦ. One constructor is added here: E_z (`FE`), so that the atom E_p of conditions has a counterpart. A formula without `FE` is a formula of [8].
- **Interpretation** (`interp`, [8] p. 26, rules Ip, IR⊥, I∃): a map I from base predicate symbols to R-predicates extends to formulas by I(¬Φ) = ¬I(Φ), I(∨ΦΨ) = ∨(I(Φ), I(Ψ)), I(RΦ) = R(I(Φ)) and I(∃xΦ) = ∃x(I(Φ)). The symbols ↓z denote the indicators, and `FE z` denotes E_z.
- **Conditions as formulas.** A nominative datum d is read as the named set p ↦ d(p) over complex names (`nd_named`). The translation `cond_fm` sends E_p to `FE p`, ↓p to `FDown p`, and "p is an atom of primitive type q" and the comparisons to base predicate symbols (`bsym`), interpreted by `is_R`. A comparison a ∘ b is the R-predicate `cmp_R` with T = { σ | a and b denote atoms u, w and u ∘ w } and F = { σ | a and b denote atoms u, w and not u ∘ w }. NOT and OR go to ¬ and ∨. AND goes to ¬(¬Φ ∨ ¬Ψ), because conjunction is not a base composition.
- **Expressions as conditions** (`expr_cond`). The expressions of section 1 over complex names, which the evaluator reads, are translated to the conditions of section 7.2: a comparison to the atom `ACmp`, `DEFAULT` operands included (the operands of that atom are value expressions); `PRESENT(p)` to E_p; `NOT`, `AND`, `OR` to the connectives of the condition; `e₁ IMPLIES e₂` to `NOT e₁ OR e₂` (`kimp_kor_knot`); the literal true to ↓[] and false to its negation, since the empty complex name leads to the datum itself and so is present on every datum (`present_partial_Nil`). The translation is total.
- **Expressions over flat states as formulas** (`expr_fm`). For the flat states of section 1, which need not come from a nominative datum, an expression is translated directly to a formula: a comparison to a base predicate symbol (`ssym`) interpreted by `cmp_S`, the R-predicate with T = { σ | a and b have values u, w and u ∘ w } and F = { σ | a and b have values u, w and not u ∘ w }; `PRESENT(x)` to `FE x`; `AND` to ¬(¬Φ ∨ ¬Ψ) and `IMPLIES` to ¬Φ ∨ Ψ; the literal true to ∃x ↓x for a name x given as a parameter, which is true on every named set because x has a value in d(x ↦ a) (`pval_ex_down`), and false to its negation. There is no constant among the base compositions, and ↓z alone is undefined where z has no value.

*Theorems* (all in `TRIEL_Compositions.thy`):

- **`ren_ext_mono`, `ren_mono`:** d ⊑ d′ ⟹ r(d) ⊑ r(d′), for extended and for traditional renomination. `ren_ext_mono_pw` is the same for every pointwise extension.
- **`P_pred_R_ex`, `P_pred_R_ren_ext`, `P_pred_R_ren`** (with `P_pred_R_not`, `P_pred_R_or`): ∃x and renomination map P-predicates to P-predicates.
- **`rmono_R_ex`, `rmono_R_ren_ext`, `rmono_R_ren`** (with `rmono_R_not`, `rmono_R_or`, `DownInd_rmono_pw`): they map monotone R-predicates to monotone R-predicates, for every pointwise extension with a reflexive order on values.
- **`equitone_R_ex`, `equitone_R_ren_ext`, `equitone_R_ren`** (and `equitone_R_ex_pw`, `equitone_R_ren_ext_pw`): ∃x and renomination preserve equitonicity.
- **`comp_closure_P`, `comp_closure_rmono`, `comp_closure_equitone`:** a predicate built by the compositions of C↓⊥Q from P-predicates is a P-predicate. Built from monotone R-predicates, it is monotone. Built from equitone P-predicates, it is an equitone P-predicate. `comp_closure_ren` covers C↓Q, and `equitone_closure_sub` contains the closure of section 7.2. This checks the claim of [8] (p. 26) in full, for the P-, RM- and PE-predicates.
- **`DownInd_not_total`:** ↓z is not total, so the classes of total predicates are not closed ([8] p. 26).
- **`Ex_R_is_not_eps`:** E_z = ¬εz. So E_z is a term of the algebra of [2], though not a composition of C↓⊥Q.
- **`pval_R_ex`, `pval_R_ren_ext`:** on P-predicates the quantifier is the strong Kleene ∃, and renomination is precomposition with r.
- **`interp_comp_closure`, `interp_P_pred`, `interp_equitone`:** a formula without E_z denotes a predicate of the closure. If the base predicates are P-predicates, every formula denotes a P-predicate. If they are equitone P-predicates, every formula without E_z denotes an equitone P-predicate.
- **`nd_le_pw`:** d ≤ d′ on nominative data if and only if p ↦ d′(p) extends p ↦ d(p) pointwise, where an atom stays the same atom and a record stays a record.
- **`cmp_R_rmono`, `cmp_R_equitone`:** a comparison without `DEFAULT` is a monotone and equitone P-predicate under the extension of nominative data.
- **`cond_fm_correct`:** for every condition φ of section 7.2, comparisons included, and every datum d, the interpretation of `cond_fm φ` on p ↦ d(p) has the value of φ on d. So every TRIEL condition is a term of the composition algebra.
- **`cond_equitone_from_closure`, `verdict_stable_from_closure`:** the stability of verdicts of section 7.2 (`verdict_stable_nd`) follows from the closure, for conditions with comparisons too. A condition without E_p and `DEFAULT` translates to a formula without E_z whose base predicates are equitone (`catom_fm_E_free`, `cond_fm_syms`, `interp_equitone_pw_syms`), and that formula denotes an equitone P-predicate.
- **`expr_cond_correct`, `expr_cond_Ex_free`:** for every expression e of section 1 over complex names and every datum d, the condition `expr_cond e` has the value of e on d, under every interpretation of the primitive types. Its atoms are without E_p and `DEFAULT` if and only if e is PRESENT-free.
- **`T2_nd_from_closure`, `present_free_equitone_nd_from_closure`, `T2_flat_from_closure`:** the monotonicity claim T2 for nested data (`T2_nd_monotone`, section 7.2) follows from the closure of the equitone P-predicates under the base compositions: a PRESENT-free expression is a condition without E_p and `DEFAULT` (`expr_cond_Ex_free`), that condition is a term of the algebra (`cond_fm_correct`), and the term denotes an equitone P-predicate (`cond_equitone_from_closure`). The same for the states the evaluator reads, `flat d` (`T2_flat_from_closure`, through `eval_nd_flat`).
- **`cmp_S_equitone`, `expr_fm_correct`, `T2_from_closure`, `present_free_equitone_from_closure`:** on flat states, a comparison without `DEFAULT` is an equitone P-predicate under ⊑; the interpretation of `expr_fm x e` has the value of e on every state; and T2 of section 2 (`T2_monotone`) follows from the closure: a PRESENT-free expression translates to a formula without E_z (`expr_fm_E_free`) whose base predicates are comparisons without `DEFAULT` (`expr_fm_syms`), so the formula denotes an equitone P-predicate (`interp_equitone_pw_syms`). So Theorem T2, on flat states and on nested data, is a consequence of the closure theorem, as is the stability of verdicts; the direct proofs (`eval_mono`, `flat_mono`) remain.

*Not formalised.* Superposition of functions into predicates, and with it the substitution of the value of an expression into a condition, is not formalised here. The sources used in this section, [2], [5] and [8], are pure first-order logics without function symbols.

## 8. Deadlines and breach (`TRIEL_Breach.thy`, TECHNICAL_REPORT.md §2.6)

Section 2.6 distinguishes the specification trace of §2.5 from the *implementation trace*: the events a running system produces, each with a timestamp. This section adds a layer of *verdicts* over implementation traces. The trace semantics of sections 4 and 6 is unchanged, so `den`, `den_total` and the laws of UNLESS are not affected.

### 8.1 Definitions

- **Implementation traces and time.** Implementation traces are the traces of section 4 with integer timestamps (`itrace`).
  - Entry 0 is the activation entry: its timestamp is the activation time τ₀, and its state is the activation state. Actions are the events of the later entries.
  - An event is matched to a norm by subject and action (`does`).
- **Deadlines.** A deadline is an absolute time, a duration, or a factor plus an offset (`deadline`). It is resolved once, at activation (`resolve`, `activates`).
  - A duration counts from τ₀.
  - A factor is read in the activation state.
  - A deadline that does not resolve rejects the activation.
- **Verdicts.** Fulfilled, Breached τ or Pending (`verdict`).
  - **Obligation.** s MUST a BY d, or WITHIN d, has the window (−∞, d] (`window`, `ob_verdict`). It is Fulfilled by an action of s in the window, Breached d once the trace has an entry strictly after d with no such action, and Pending otherwise.
  - **FROM.** s MUST a BY d FROM f has the window [f, d], which over integer times is (f − 1, d] (`start_of`, `lo_of`). f is a DATETIME or a factor, resolved at activation like a deadline, and a duration in BY counts from f (`deadline_of`). Without FROM, the start is the activation time τ₀ and the window is (−∞, d].
  - **Prohibition.** s MUST_NOT a WHEN c is Breached at the first action a of s before which ⟦c⟧ = T, where c is evaluated in the state before the action (`pr_verdict`). Its forbidden actions are those of the trace semantics (`forbidden`, section 4.1).
  - **Permission.** s MAY a WHEN c is never breached (`may_verdict`).
- **Enforcement and verdict: two roles.** A monitor *enforces* a prohibition fail-closed: it blocks the action unless c is known to be false, so it also blocks on ⊥ (`blocks`). The *verdict* records a breach only when c = T. The fail-closed rule listed in `FOUNDATIONS.md` belongs to enforcement, not to the verdict.
- **The monitor as a function** (`enforce`, section 9, decision 37). Entry j of π is a *blocked action* of s MUST_NOT a WHEN c if j ≥ 1, its event is the action a of s, and `blocks c (st π (j − 1))` (`blocked_action`). `enforce s a c π` is π with every blocked action replaced by a clock tick (`Tick`) with the same time and the same state; every other entry is kept. It is a suppression automaton in the sense of Ligatti, Bauer and Walker (edit automata): it reads the trace entry by entry and suppresses an action or lets it through. `monitor_decisions s a c π` lists, for every entry whose event is the action a of s, the entry and whether it is blocked; the evaluator prints it (section 10.4).
- **Actions.** The type of actions is a parameter of every theory, so an action with arguments, `pay(bob, 100)`, is just an action; the evaluator instantiates it with a name and a list of arguments (section 10.4).
- **Breach actions.** NOTIFY and PENALTY are informational. TERMINATE, CURE_BY and ESCALATE_TO determine the continuation (`baction`, `is_cont`). A handler is well formed if it has at least one action and at most one continuation-determining action (`wf_actions`).
- **Status after a breach** (`handle_breach`):
  - with no continuation-determining action, or with TERMINATE, the obligation stays breached and is closed;
  - CURE_BY k opens the window (τ_b, τ_b + k] from the moment of breach τ_b;
  - ESCALATE_TO s′ gives s′ a new obligation for the same action, with a window of the same length counted from the moment of transfer.
  - `handle_breach` takes the start of the obligation (τ₀, or f with FROM) for the length of that window, and the lower bound of its window.
- **Fallbacks** (`else_verdict`, section 9, decision 22). `s MUST a WITHIN d ELSE s′ MUST a′ BY d′` is `SMustElse`. It is fulfilled by an action of s in (−∞, d]. Once the trace passes d without one, it is not breached: the status is `EElse d v`, where v is the verdict of the fallback with the window (d, d′]. A duration in d′ counts from d (`else_deadline`). A handler bound to an obligation with a fallback is rejected (`else_handlers_ok`). At activation, d′ must resolve to a time after d (`else_order_ok`, decision 27).
- **TERMS blocks and binding.** A TERMS block is a list of surface terms (`sterm`). A handler is bound to the nearest preceding obligation or prohibition of the same subject at the top level (`bound_to`). The well-formedness predicate `wf_block` requires three things:
  - handlers only at the top level;
  - every handler well formed and bound;
  - at most one handler per obligation or prohibition.
- **MAX_AGE and ON_STALE BLOCK.** A factor with MAX_AGE m is fresh at an entry if its value arrived at most m time units earlier (`fresh`). Under BLOCK, a stale factor is absent from the state (`blocked`).

### 8.2 Theorems

- **`deadline_missed_breach`, `within_missed_breach`:** a deadline passed with no action means Breached, at τ₀ + k for WITHIN k.
- **`fulfilled_at_deadline`:** an action exactly at the deadline fulfils.
- **`pending_open`:** Pending means that no entry is past the deadline yet.
- **`window_final`, `ob_verdict_final`, `pr_verdict_final`:** once reached, a verdict does not change when the trace is extended. For a breach this uses non-decreasing timestamps.
  — Breach is monotone in time.
- **`mustnot_violated_breach`, `breach_mustnot_violated`:** a violated trace of a prohibition (section 4.1) is breached at its last entry, and every breached trace has the prefix up to the breach as a violated trace. The trace semantics and the verdict of a prohibition agree.
- **`breach_blocked`:** every breach of a prohibition is an action the monitor would have blocked.
- **`enforced_no_breach`:** if no action was taken in a blocking state, there is no breach.
- **`undefined_guard_blocks_not_breach`:** if c = ⊥, the monitor blocks, but the verdict is not a breach.
  — Enforcement is strictly stronger than the verdict.
- **`enforce_sound`:** `pr_verdict s a c (enforce s a c π) = Pending`: the output of the monitor is never breached. — Soundness of enforcement (Schneider; Ligatti, Bauer and Walker).
- **`enforce_is_trace`, `enforce_st`, `enforce_time`, `enforce_tstamps`:** the output of the monitor is a trace with the states and times of π. **`enforce_preserves_time_order`:** `sorted (map tstamp (enforce s a c π)) ⟷ sorted (map tstamp π)`.
- **`enforce_idempotent`:** `enforce s a c (enforce s a c π) = enforce s a c π`.
- **`enforce_blocks_exactly`:** for j < |π|, `enforce s a c π ! j ≠ π ! j ⟷ blocked_action s a c π j`: the entries the monitor changes are exactly the blocked actions. **`blocked_action_enforce`:** the output has no blocked action.
- **`enforce_id_iff`:** `enforce s a c π = π ⟷ (∀j. ¬ blocked_action s a c π j)`.
- **`enforce_unchanged_no_breach`:** a trace the monitor leaves unchanged is not breached.
- **`enforce_transparent`:** if `eval c (st π j) ≠ None` for every j < |π|, then `enforce s a c π = π ⟷ pr_verdict s a c π = Pending`. — Transparency on defined data: the monitor changes a trace exactly when the prohibition is breached, so it never alters a breach-free trace.
- **`enforce_undefined_blocks`:** an action a of s at entry j with `eval c (st π (j − 1)) = None` becomes a tick, so `enforce s a c π ≠ π`, and j is not a forbidden entry of π. — Where transparency with respect to the verdict fails, and why: the fail-closed monitor blocks an action the verdict does not count as a breach.
- **`enforce_minimal`:** on defined data (as in `enforce_transparent`), for every π′ with the states and times of π whose verdict is Pending: an action a of s that π′ keeps at entry j is not a blocked action of π, and `enforce s a c π ! j = π ! j`. — No breach-free edit of the trace keeps an action the monitor blocks; the monitor suppresses the least.
- **`blocks_data_mono`:** c PRESENT-free ∧ σ ⊑ σ′ ∧ `blocks c σ′` ⟹ `blocks c σ`. — What the monitor allows in a state it allows in every state with more data (from T2). **`blocked_action_data_mono`:** for a PRESENT-free c and a trace π′ with the length and the events of π whose state at every entry has at least the data of π (`st π i ⊑ st π′ i`), a blocked action of π′ is a blocked action of π: more data, fewer blocked actions.
- **`monitor_decisions_iff`, `monitor_decisions_block`, `monitor_decisions_allow`, `monitor_decisions_enforce`:** (j, T) is a decision exactly when j is a blocked action, that is, exactly when `enforce` changes entry j; (j, F) exactly when the action at j is let through.
- **`monitor_decisions_append`:** the decisions on π @ ρ begin with the decisions on π. — A decision is final.
- **`enforce_allows_sound`** (TRIEL_Completions): for a PRESENT-free c, an action that `enforce` lets through was taken in a state in which c is false in every completion.
- **`may_never_breached`:** a permission is never breached.
- **`cont_unique`, `cont_of_some`, `two_continuations_rejected`, `section_2_6_example_rejected`:** continuation-determining actions are mutually exclusive.
  — A handler with two of them is rejected, including the list PENALTY, NOTIFY, TERMINATE, CURE_BY given in §2.6.
- **`informational_irrelevant`:** the status depends only on the continuation-determining actions.
- **`cure_restores`:** an action in the cure window cures the breach, and no second breach fires.
- **`cure_failed`:** a failed cure is a second breach, and it is final.
- **`escalation_keeps_breach`:** after ESCALATE_TO the original obligation stays breached.
- **`handle_breach_final`:** the status after a breach is final once its windows are decided.
- **`bound_to_nearest`, `bound_to_None`:** binding goes to the nearest preceding obligation or prohibition of the same subject, or to nothing if there is none.
- **`nested_handler_rejected`, `wf_handler_bound`, `wf_one_handler`:** a nested handler is rejected; in a well-formed block every handler is bound, and every obligation has at most one handler.
- **`activation_rejected`:** a deadline from an absent factor rejects the activation.
- **`from_window`, `after_from`:** with FROM f, an action fulfils exactly when it is at a time in [f, d].
- **`before_from_no_fulfil`, `fulfilled_at_from`:** an action before f does not fulfil, so the obligation is breached at d if nothing else happens; an action exactly at f fulfils.
- **`from_no_deadline`:** with FROM and no deadline, only an action at or after f fulfils, and the obligation is never breached.
- **`empty_window_breached`:** a window that starts after its deadline cannot be met: the obligation is breached at d.
- **`no_from`, `from_duration`, `from_at`, `from_absent_factor`:** without FROM, start, window and deadline are as before; a duration in BY counts from the start; a DATETIME start is that time; a start from an absent factor does not resolve.
- **`activation_rejected_from`, `activates_resolves`:** a start from an absent factor rejects the activation; after activation, the start and the deadline of every top-level obligation resolve.
- **`else_fulfilled`, `else_pending`, `else_taken`, `else_no_breach`:** an action by d fulfils an obligation with a fallback; when d passes without one, the fallback is in force from d instead of a breach.
- **`else_alt_after`, `else_alt_breached`, `else_alt_duration`:** only an action strictly after d fulfils the fallback; a missed fallback deadline d′ is a breach at d′; a duration in d′ counts from d.
- **`else_final`, `activation_rejected_else`, `activates_resolves_else`:** the status is final once decided; both deadlines are resolved at activation, and one from an absent factor rejects it.
- **`else_handler_rejected`:** a handler bound to an obligation with a fallback is rejected.
- **`else_order_rejected`, `else_order_window`, `else_order_duration`:** a fallback deadline that resolves at or before d fails `else_order_ok`; when it holds, d < d′, so the window (d, d′] is not empty; a positive duration in d′ always gives d < d′.
- **`fresh_at_max_age`:** an age equal to MAX_AGE is still fresh.
- **`stale_absent`:** under BLOCK a stale factor is absent, so PRESENT is F.
- **`stale_safe`:** a result computed with stale factors treated as absent is not overturned by whatever values those factors have when refreshed.
  — This is the safety claim of §2.9, derived from T2.
- **Verdicts on the same trace with more data** (`data_le`, section 4.1; decision 36).
  - **`acted_data_indep`, `passed_data_indep`, `window_data_indep`, `ob_verdict_data_indep`, `handle_breach_data_indep`, `else_verdict_data_indep`:** the verdict and the status of an obligation, with or without a handler or a fallback, read only times and events, so they are the same on every refinement of the trace.
  - **`pr_verdict_pending_data_mono`, `pr_verdict_decided_data_mono`:** for a `PRESENT`-free c, a prohibition that is pending on the refinement was pending before: a breach is not withdrawn by more data (the counterpart, for the verdict, of `blocks_data_mono` above).
  - **`pr_verdict_data_mono`:** for a `PRESENT`-free c, on a trace (non-decreasing times), if s MUST_NOT a WHEN c is Breached τ, then on every refinement it is Breached τ′ for some τ′ ≤ τ. The first forbidden action stays forbidden, and an earlier action whose condition was ⊥ may have become forbidden, so the time of breach can move earlier, never later.
  - **`may_verdict_data_mono`:** for a `PRESENT`-free c, an exercised permission stays exercised, and one that is pending on the refinement was pending before.
  - **`pr_verdict_present_not_mono`:** with `PRESENT` a breach can be withdrawn. On the two entries activation, (s, a) at time 1, with x absent from the activation state, s MUST_NOT a WHEN NOT PRESENT(x) is Breached 1; on the refinement where x is present at activation it is Pending.

### 8.3 Clarifications of §2.6

Points 1–14 are the points where §2.6 is ambiguous or contradictory. Points 15–21 are further readings needed to formalise it.

1. **Binding.** §2.6 binds a handler to the nearest preceding obligation and also says that two obligations with one trailing handler have no defined meaning. The binding rule is adopted: the handler binds to the nearest one, and the others have no handler.
2. **Handlers are top-level.** Syntactically a handler is a term, but it has no denotation as one. It is allowed only at the top level of a TERMS block; a nested handler is rejected (`nested_handler_rejected`).
3. **Polarity.** An implementation event is matched by subject and action; the polarity belongs to the norm. Since version 2.5.1 the trace semantics of section 4 matches events the same way (decision 31).
4. **Prohibitions.** The condition c of MUST_NOT WHEN c is evaluated in the state before the action. The verdict is Breached only when c = T. Fail-closed handling of ⊥ belongs to enforcement (see 8.1).
5. **Origin of durations.** Durations in BY and in a term-level WITHIN count from the activation time τ₀. CURE_BY counts from the moment of breach.
6. **Boundary.** An action at the deadline fulfils. A breach is established only when the trace has an entry strictly after the deadline, and the time of breach is the deadline.
7. **Deadline from a factor.** It is fixed at activation; if the factor is absent there, the activation is rejected.
8. **WITHIN without ELSE.** A missed deadline is a breach (`within_missed_breach`). With ELSE, a missed deadline puts the fallback obligation in force instead (section 9, decision 22).
9. **Failed cure.** A failed cure is a second breach and is final: no handler applies to it, so there is no loop.
10. **ESCALATE_TO s′.** The original obligation stays breached. s′ gets a new obligation for the same action, with a window of the same length (d − τ₀) counted from the moment of transfer.
11. **TERMINATE** closes the obligation, not the whole specification.
12. **Only informational actions.** The obligation stays breached and is closed.
13. **FROM … UNTIL.** `FROM` is formalised (section 9, decision 17); `UNTIL` is removed from obligations (decision 21).
14. **MAX_AGE.** An age equal to MAX_AGE is still fresh. Under USE_LAST the last value is kept and is present.
15. **Binding target.** A handler binds to an obligation *or a prohibition* of the same subject, as §2.6 states.
16. **One handler per norm.** At most one handler per obligation or prohibition (`wf_one_handler`).
17. **No deadline.** An obligation without a deadline is never breached. This is semantically sound, but a future analyser of specifications should warn about it: no verdict can hold such an obligation to account.
18. **CURE_BY** takes a duration.
19. **Activation entry.** Entry 0 of an implementation trace is the activation entry; actions are the events of later entries.
20. **Scope of verdicts.** Verdicts are given to the top-level elements of a TERMS block. Deadlines inside composite terms are resolved at activation (and can reject it), but have no verdict of their own.
21. **Handlers of prohibitions.** §2.6 defines continuations only for obligations. A handler bound to a prohibition may have only informational actions; the evaluator and the translator reject a continuation there (section 10.6, rule 4).

### 8.4 The amount of a penalty (`TRIEL_Penalty.thy`)

*Definitions:*

- **Amounts.** An amount expression is a value expression of section 1, or two amount expressions combined by `+`, `-` or `*`, or the negation of one (`pexp`). Its value ⟦e⟧σ ∈ ℚ ∪ {⊥} (`evalP`) reads a value as a number with a function `num`, and is ⊥ when an operand is ⊥ or not a number. Division is not admitted.
- **The amount of a penalty.** `PENALTY e CAP c` is `Pen e (Some c)` (`pen`). Its amount in σ (`pen_amount`) is *undefined* if ⟦e⟧σ = ⊥, *negative* v if ⟦e⟧σ = v < 0, and otherwise v, or c with the mark *capped* if c < v.
- **The state of the breach.** For an obligation with deadline d, `breach_entry d π` is the first entry strictly after d, and the penalty is read in the state of the entry before it (`ob_pen_state`). For a prohibition, `first_forbidden` is the first forbidden action, and the penalty is read in the state before it (`pr_pen_state`), in which the condition is read.
- **Reported actions.** After a breach, the informational actions of the handler are reported in source order: NOTIFY with its subject, PENALTY with its amount in the state of the breach (`ract`, `report_actions`, `ob_report`, `pr_report`).

*Theorems:*

- **`evalP_strict`:** an amount is ⊥ when an operand is, as every arithmetic operation of §2.9.
- **`evalP_mono`, `pen_amount_mono`:** without DEFAULT, a defined amount is not changed by more data, as T2 for comparisons. **`pen_default_not_mono`:** with DEFAULT it is: DEFAULT(x, 0) is 0 on ∅ and 1 on [x ↦ 1].
- **`decimal_add`, `decimal_uminus`, `decimal_diff`, `decimal_mult`** (in `TRIEL_Numbers.thy`), **`evalP_decimal`, `pen_amount_decimal`:** the Decimals are closed under `+`, `-` and `*`, so an amount computed from Decimal values and a Decimal cap is a Decimal.
- **`pen_amount_undefined`, `pen_amount_negative`, `pen_amount_exact`, `pen_amount_capped`, `pen_amount_bounds`:** the four cases of the amount; a reported amount is never negative and never exceeds the cap.
- **`breach_entry_passed`, `ob_pen_state_at_deadline`:** the penalty of an obligation is read in the last state not after the deadline (in the activation state if the deadline is before activation).
- **`pr_pen_state_condition`:** the penalty of a prohibition is read in the state in which its condition is true, the state before the forbidden action.
- **`ob_pen_state_final`, `pr_pen_state_final`, `ob_report_final`, `pr_report_final`:** once a norm is breached, later entries change neither the state of the breach nor the reported actions and amounts.

### 8.5 Completions of the data (`TRIEL_Completions.thy`)

*Definitions:*

- **Completion.** σ′ is a completion of σ if σ ⊑ σ′ and dom σ′ = N (`completion`): a total valuation that agrees with σ wherever σ is defined. Every state has one (`completion_exists`).
- **Skip reading.** `skip_allows c σ` ⟺ ⟦c⟧σ ≠ T: the action is allowed unless the condition is known to be true, so an undefined condition allows it.
- **Absent-false reading.** `eval_af` is two-valued: a comparison with an operand that has no value is false, the connectives are the classical ones, and PRESENT(x) is x ∈ dom σ.
- **Compositional evaluations.** G = (gnot, gand, gor, gimp) is a quadruple of connectives on 𝔹⊥ (`connectives`). `evalG G` reads the atoms as `eval` does and combines the values of NOT, AND, OR and IMPLIES with the connectives of G. G is sound (`sound_conn`) if, for every PRESENT-free e, every σ and every completion σ′ of σ, `evalG G e σ` ≼ ⟦e⟧σ′. Soundness quantifies over the conditions of one type of names and values, so that type is its first argument: `sound_conn TYPE(('n, 'v) expr) G`.

*Theorems:*

- **`eval_af_total`, `completion_defined`:** on a total valuation every condition is defined, and its value is that of `eval_af`.
- **`monitor_sound_completions`:** c PRESENT-free ∧ ¬ blocks c σ ∧ σ′ a completion of σ ⟹ ⟦c⟧σ′ = F. If the fail-closed monitor does not block, the condition is false in every completion.
- **`enforce_allows_sound`:** the same for the monitor as a function: c PRESENT-free, 1 ≤ j < |π|, the event of `enforce s a c π ! j` the action a of s, σ′ a completion of `st π (j − 1)` ⟹ ⟦c⟧σ′ = F.
- **`breach_certain_completions`:** c PRESENT-free ∧ ⟦c⟧σ = T ∧ σ′ a completion of σ ⟹ ⟦c⟧σ′ = T.
- **`skip_reading_unsound`:** there are a PRESENT-free c, a state σ and a completion σ′ with `skip_allows c σ`, `blocks c σ` and ⟦c⟧σ′ = T.
- **`absent_false_unsound`:** there are a PRESENT-free c, a state σ and a completion σ′ with `eval_af c σ` false, `blocks c σ` and ⟦c⟧σ′ = T.
- **`absent_comparison`:** for x ∉ dom σ, the comparison x = v is such a condition for both theorems: ⟦x = v⟧σ = ⊥, both readings allow the action, the monitor blocks it, and the completion that gives x the value v makes it true. Like the prohibition of `examples/core/core_invoice_agent.triel` when its quote is stale, it is a comparison one of whose operands has no value yet.
- **`stale_quote_completion`:** the same for the ordering comparison limit < amount (the comparison amount_eur > limit_eur of that prohibition), with the limit l known and the amount absent, when vless l a for some amount a. The witness above is = because `value_order` assumes nothing about <.
- **`kleene_not_complete`, `absent_contradiction`:** there are a PRESENT-free c and a state σ with ⟦c⟧σ = ⊥ although ⟦c⟧σ′ = F for every completion σ′; for x ∉ dom σ, the condition x = v AND NOT (x = v) is one.
- **`kleene_sound_conn`:** the strong Kleene connectives (knot, kand, kor, kimp) are sound.
- **`sound_conn_kleene_le`, `kleene_optimal`:** if the type of values has two different values, every connective of a sound G is pointwise ≼ the strong Kleene one, and so `evalG G e σ` ≼ ⟦e⟧σ for every PRESENT-free e. Strong Kleene evaluation is the most defined sound compositional evaluation. The proof uses the two values: where a strong Kleene connective is undefined, the completions that give x the one value and the other give the condition different values.
- **`compositional_incomplete`:** under the same hypothesis no sound compositional evaluation is complete: x = v AND NOT (x = v) with x absent is false in every completion and undefined for every sound G.
  — A classical fact about the logic of Kleene, proved here with respect to the completions of states.

## 9. Design decisions forced by the theory

Each decision below was made because of a theorem: either one that proves the decision necessary, or one that shows what goes wrong without it.

1. **PRESENT is the total indicator E_x, not the partial indicator =xx.**
   - The partial indicator, the comparison x = x, has the truth domain of E_x but an empty falsity domain (`partial_indicator`). It can confirm presence but can never report absence. That is not enough for `PRESENT`, which §2.9 requires to be false for an empty or stale value.
   - So `PRESENT(x)` is defined as E_x (`present_is_Ex`, `present_nd_is_Ex`), which is total (`Ex_ind_total`).
   - The price is that E_x is not equitone (`Ex_ind_not_equitone`, `Ex_nd_not_equitone`). That is why `PRESENT` is the exception to monotonicity (`T3_present_not_monotone`, `T3_nd_present_not_monotone`), while =xx is equitone.
2. **Comparisons see only atoms; a complex name that leads to a record is ⊥ in a comparison.**
   - Equality of whole data is not monotone under the information order. Two equal records stop being equal when one of them is extended (`whole_data_equality_not_monotone`).
   - Restricting comparisons to atoms is what lets the monotonicity claim of §2.9 hold for nested data (`T2_nd_monotone`, through `eval_nd_flat` and `flat_mono`).
3. **Records are open: data may carry names the record type does not declare.**
   - With open records, typing survives the addition of names at any depth for every type without Optional (`wt_mono`). The record step of the proof uses only the declared fields.
   - A closed record type would reject any datum with an extra name, so adding a name could break typing. There is no separate theorem for closed records; the point is that `wt_mono` needs openness.
4. **Distributivity of UNLESS over THEN (law 3) rests on totality.**
   - As stated in §2.5, the law fails for arbitrary denotations (`unless_then_counterexample`, `unless_then_not_unconditional`).
   - It holds when the right operand of THEN is total (`unless_then`). Every term of the language is total (`den_total`), so the law holds for all terms with no side condition (`term_unless_then`).
5. **Typing and the information order disagree on Optional.**
   - For types with Optional, typing is not monotone (`wt_not_mono_optional`). It is monotone only for types without Optional (`wt_mono`).
   - The semantics of Optional is left unchanged. Section 7.2 relates the two readings of an absence, final or not yet known, to the indicators E_x and ↓x, and leaves one question open.
6. **Fail-closed is enforcement, not the verdict.**
   - If an undefined condition counted as a breach, a prohibition would be breached on data that does not yet decide it. The verdict records a breach only when c = T.
   - The monitor blocks on ⊥ (`blocks`). Every breach is an action the monitor would have blocked (`breach_blocked`), enforcement prevents breach (`enforced_no_breach`), and on ⊥ the two roles differ (`undefined_guard_blocks_not_breach`). The monitor is also a function on traces, with soundness and transparency (decision 37).
7. **A breach is established strictly after the deadline, and deadlines are fixed at activation.**
   - Timestamps only need to be non-decreasing, so an action can still arrive with a timestamp equal to the deadline. A breach is final (`window_final`) only because it waits for an entry strictly past the deadline, and only because the deadline cannot move once resolved (`resolve`, `activates`).
   - An action exactly at the deadline fulfils (`fulfilled_at_deadline`).
8. **One continuation per breach, and no handler for a failed cure.**
   - Mutually exclusive continuation-determining actions give each breach a single status (`cont_unique`, `two_continuations_rejected`), which informational actions do not affect (`informational_irrelevant`).
   - A failed cure is final (`cure_failed`, `handle_breach_final`), so there is no cure–breach loop.
9. **Handlers only at the top level of a TERMS block, one per norm.**
   - Binding is defined on the list of top-level elements (`bound_to_nearest`). A handler nested in a composite term has nothing to bind to and no denotation, so it is rejected (`nested_handler_rejected`).
   - With at most one handler per obligation (`wf_one_handler`) the status of a norm is determined.
10. **A stale factor under BLOCK is absent.**
    - Treating stale values as absent, rather than as old values, is what makes a result computed on stale data safe against refresh (`stale_safe`). This is T2 applied to the blocked state, which is below every refreshed state (`blocked_le`).
11. **"Not yet known" is the partial indicator ↓x, and a verdict that must survive more data uses only equitone atoms.**
    - ↓x has the truth domain of E_x but an empty falsity domain (`T_DownInd_eq_T_Ex`, `DownInd_irrefutable`). It is equitone (`DownInd_equitone`), and partial presence is monotone on nominative data (`present_partial_mono`).
    - A condition built from equitone atoms by NOT, AND and OR keeps every definite verdict when data is added (`verdict_stable`, `verdict_stable_nd`), and so do the LTL3 verdicts of invariants with an equitone formula (`inv_data_mono_equitone`). With E_x as an atom this fails, on the data of `wt_not_mono_optional` (`Ex_breaks_stability`).
    - No new construct is added for ↓x: on the flat named sets of section 1 it is the comparison `x == x` (`self_eq_is_DownInd`), which is PRESENT-free, so T2 already covers it. On nominative data `p == p` is below ↓p (`self_eq_below_present_partial`): it is ⊥ when p leads to a record. `PRESENT` keeps its meaning E_x (decision 1). A condition whose verdict must not be overturned by later data uses `x == x`, not `PRESENT(x)`.
12. **The value order is a relation on values, not a partial function.**
    - `vless` and `vleq` give T or F on every pair of values, so a comparison is ⊥ only when an operand has no value, exactly like `=`. This keeps T4 for the comparisons: on fully defined data every condition is two-valued (`T4_classical`).
    - The price is that an ordering comparison of a number with a value that is not a number is F in the evaluator. The translator rejects such a comparison (section 10.6, rule 5), and the types of the data are checked before any verdict, so it does not arise for a translated specification.

13. **The condition of `IF` and `WHEN` is evaluated once, where the term is reached, and only T selects the `THEN` branch.**
    - `IF c THEN t₁ ELSE t₂` takes the traces of t₁ that start in a state where c = T, and the traces of t₂ that start in a state where c ≠ T (`den_if`). Without `ELSE`, the second part is the one-entry trace with outcome `Done`, like a permission that is not exercised (`if_no_else_not_true`). `ELIF` is a nested `IF` in the `ELSE` branch, and `WHEN c THEN t` is `IF c THEN t`.
    - An undefined c goes the way of F (`if_undefined_else`). This is the reading of an undefined `UNLESS` guard, which does not fire. It is justified by two theorems. On data that defines every name c reads, c is never ⊥ and the term is the two-valued `IF` (`if_classical`, from T4). Once c has a definite value, more data does not change the branch, for every c without `PRESENT` and `DEFAULT` (`if_branch_stable`, from T2).
    - The branch taken on ⊥ is not protected in this way: data that arrives later can make c true (`if_undefined_branch_not_stable`). Every rule that picks a branch on ⊥ has this property.
    - `IF` and the one-entry term preserve totality (`total_if`, `total_skip`), so every term is still total (`den_total`) and the laws of `UNLESS` hold for the extended term language with no side condition.
    - `WHEN c THEN t` does not wait for c (decision 23): it is evaluated once, as for `IF`. Waiting for an event is `ON event DO term`.
14. **A named term is in force, and `REF` refers only backwards.**
    - An element `name := t` of a `TERMS` block is an element like any other. `REF name` denotes the denotation of t (`resolve_den`, `block_den`).
    - A reference to an undeclared name, or to a name declared at or below the reference, is rejected (`refs_ok`). So the reference relation is contained in the order of the elements and has no cycle (`refs_forward_rejected`, `refs_ok_acyclic`, `refs_no_cycle`).
    - References are removed by substitution, and substitution preserves the denotation (`resolve_den`). A resolved term contains no reference, so totality and the laws of `UNLESS` carry over to it with no side condition (`benv_total`).
    - A `REF` to an element with a breach handler or a deadline is rejected too: a handler is not a term, and a composite term cannot carry a deadline (section 10.6, rule 7). Under these rules every element without a handler resolves (`benv_defined`).
15. **`DEFAULT` is excluded from the stability of verdicts, like `PRESENT`.**
    - DEFAULT(f, d) is the value of f if E_f, and the value of d otherwise (`evalV_default`).
    - DEFAULT is not monotone: on ∅ ⊑ [f ↦ v], DEFAULT(f, w) changes from w to v (`T3_default_not_monotone`), and the condition DEFAULT(f, w) = w changes its definite verdict from T to F (`default_breaks_stability`).
    - So "PRESENT-free" means free of `PRESENT` and `DEFAULT`, the two forms §2.9 excepts from monotonicity, and the comparison atoms of section 7.2 are equitone only without `DEFAULT` (`Ex_free_atom`). `verdict_stable` and `verdict_stable_nd` do not cover a condition with `DEFAULT`.
16. **The arguments of an action are part of the action, and they are not evaluated.**
    - `pay(bob, 100)` is the action `pay` with the argument list `bob, 100`. An event matches a norm only if its subject, action and arguments are the same; an event with other arguments, or with none, does not.
    - A literal argument is compared by value (`100` and `100.00` are the same number). A name, of a subject or a factor, is compared as a name and its value is not read, so `submit_proof(age)` does not read the hidden `age`, as TECHNICAL_REPORT.md §2.7 requires.
    - Every theory of sections 4–8 is generic in the type of actions, so every theorem about actions holds for actions with arguments without change; this includes `mem3_sound` and `mem3_definite`, and the term language and its laws are unchanged. In the evaluator an action is a name with a list of arguments (`Act`, `ArgName`, `ArgVal`), and an event matches only with the same arguments (`does_args`, `other_args_no_fulfil`); `1200` and `1200.00` are the same argument (`arg_1200`).
    - A factor in an argument stands for its name, not for its value (decision 24).
17. **`FROM s` opens the window of an obligation at s, and a duration in `BY` counts from s.**
    - The window of `s MUST a BY d FROM f` is [f, d]: an action before f does not fulfil it (`from_window`, `before_from_no_fulfil`, `fulfilled_at_from`). f is resolved at activation, like a deadline, and a factor that does not resolve rejects the activation (`activation_rejected_from`). A duration in BY counts from f (`from_duration`).
    - Without `FROM` the window and the origin of durations are those of section 8 (`no_from`). `ESCALATE_TO` gives the new obligation a window of length d − f. A window that starts after its deadline is breached at the deadline (`empty_window_breached`).
    - The verdicts stay final (`window_final`, `handle_breach_final`, now for every lower bound of the window).
    - `UNTIL` is removed from obligations (decision 21).
18. **A penalty is computed once, in the state in which the breach occurs.**
    - The amount of `PENALTY e CAP c` is read in the state of the entry just before the entry that establishes the breach: for a prohibition the state before the forbidden action (`pr_pen_state_condition`), for an obligation the last state not after the deadline (`ob_pen_state_at_deadline`). That entry is fixed once the breach is, so the amount does not change when the trace is extended (`ob_report_final`, `pr_report_final`).
    - `e` uses `+`, `-` and `*` on numbers, without division, so Integer and Decimal operands give a Decimal (`evalP_decimal`, `pen_amount_decimal`). An operand without a value makes the amount undefined, as in §2.9 (`evalP_strict`); it is reported as undefined, not as 0.
    - A negative amount violates the rule of §2.9 that the amount be non-negative. It is reported as negative and is not replaced by 0. Otherwise the amount is min(e, c), or e without `CAP` (`pen_amount_bounds`).
    - Arithmetic without `DEFAULT` is monotone like the comparisons, so a defined amount does not change when more data is present (`evalP_mono`, `pen_amount_mono`); with `DEFAULT` it can (`pen_default_not_mono`, decision 15).
19. **`EVENTUALLY φ WITHIN d` is decided by the entries up to its deadline, and missing data leaves it undefined.**
    - d is resolved once, at activation, like the deadline of an obligation (decision 7): a duration counts from τ₀, and a deadline that does not resolve rejects the activation (`activation_rejected_inv`). The window is the set of entries with time ≤ D.
    - The verdict is T as soon as φ = T at an entry of the window, an entry exactly at D included (`ew_at_deadline`). It is F only once the trace has an entry strictly after D and φ = F at every entry of the window (`ew_missed`). Otherwise it is ⊥. Before D it is never F (`ew_not_false_before`).
    - After D the verdict is the strong Kleene disjunction of φ over the window (`ew_after_deadline`), so an entry where φ is ⊥ prevents F (`ew_undefined_data`). If such an entry counted as F, data that arrives later could turn F into T. With this rule, for φ without `PRESENT` and `DEFAULT`, a definite verdict does not change when the states carry more data (`ew_data_mono`), and, with non-decreasing timestamps, when the trace is extended (`ew_final`), as for obligations (`window_final`).
    - A true `EVENTUALLY φ WITHIN d` makes `EVENTUALLY φ` true (`ew_eventually`).
20. **The heuristic scoring layer is metadata.**
    - TECHNICAL_REPORT.md section 4 states that `POLARITY`, `THRESHOLD`, `SENSITIVITY_BOUND`, `WEIGHT` and `CROSS_MODAL` have no formal semantics. The core does not invent one: the `POLARITY`, `THRESHOLD` and `SENSITIVITY_BOUND` of a factor are printed as metadata and do not enter any verdict, like `SOURCE`.
    - `CROSS_MODAL` (with `TOLERANCE`) and `CAUSED_BY` (with `WEIGHT`) are still rejected: each would add an invariant or a causal claim, and a claim without a verdict must not be accepted silently.

21. **`UNTIL` is removed from obligations.**
    - TECHNICAL_REPORT.md never gave `subject MUST a … UNTIL e` a meaning, and the end of the window of an obligation is already its deadline `BY`. The clause is removed from `obligation_stmt` in the grammar, so it is a syntax error, not a rejection by the translator. `UNTIL` stays a reserved word, as `Float` did in stage 9.
22. **`WITHIN d ELSE u` is a fallback, not a breach.**
    - `s MUST a WITHIN d ELSE s′ MUST a′ BY d′`, at the top level, is an obligation with a fallback (`SMustElse`, `else_verdict`). An action of s in (−∞, d] fulfils it (`else_fulfilled`). If the trace passes d with no such action, it is not breached: the fallback is in force from d, with the window (d, d′] (`else_taken`, `else_no_breach`). Only the fallback can be breached (`else_alt_breached`), and an action at or before d does not fulfil it (`else_alt_after`).
    - A duration in d′ counts from d, as `CURE_BY` counts from the moment of breach (`else_alt_duration`). Both deadlines are resolved at activation, and a deadline that does not resolve rejects the activation (`activation_rejected_else`). The verdicts stay final (`else_final`).
    - The fallback must be an obligation without `FROM`, the first obligation has no `FROM`, and `ELSE` inside a composite term, a nested `ELSE`, and a handler bound to an obligation with a fallback are rejected (`else_handlers_ok`): a fallback is what happens instead of a breach, so a handler for that obligation would never fire. In the trace semantics of §2.5, which has no time, the term is the choice of the two obligations.
23. **`WHEN c THEN t` is evaluated once.** The open question of decision 13 is closed this way: `WHEN c THEN t` is `IF c THEN t` without `ELSE`. Waiting for c is not part of `WHEN`; an event is waited for with `ON event DO term`, which is outside this core.
24. **A factor in an action argument stands for its name.** The open question of decision 16 is closed this way: the value of a factor is never read in an argument, so a `ZK` factor can be named in an action without its value being revealed (TECHNICAL_REPORT.md §2.7).

25. **A hidden factor is removed before evaluation, and the flow rule makes the removal harmless.**
    - A `ZK<T>` factor without `WITHOUT REVEALING ALL` is *hidden* (TECHNICAL_REPORT.md §2.7). The evaluator removes every hidden factor from the data of every entry before typing and evaluation (`erase_obs`, `run`). So two traces that differ only in the values of hidden factors get the same report (`run_noninterference`); in particular the hidden value cannot change a verdict, a penalty, an invariant or the result of typing.
    - The flow rule of §2.7 is checked by the translator: a hidden factor may not be read anywhere a value is evaluated (a condition, an invariant, `PRESENT`, `DEFAULT`, a `PENALTY`, a deadline or `FROM`), and may be named only as a bare action argument (decision 24). For a condition or a value that does not read a hidden factor, removing the hidden factors changes nothing at any entry of the trace the evaluator sees (`flow_safe_eval`, `flow_safe_evalV`), so a specification that passes the flow rule reads the same values with and without the removal.
    - The `PROVES` constraints are checked by the proof system, not by the core; they are metadata. A `ZK<T>` factor `WITHOUT REVEALING ALL` is an ordinary factor of type T.
26. **The cryptographic declarations are metadata, with the semantic rules of §2.8 checked at translation.** `PROOF_SYSTEM`, `CURVE`, `DID`, `BOUND_TO` and `PROVES` are printed and enter no verdict. A specification with a `ZK<T>` factor without `PROOF_SYSTEM` or `CURVE`, a `ZK<T>` factor sourced from a subject with a `DID` but without `BOUND_TO`, a `BOUND_TO` subject without a `DID`, and an undeclared nonce or salt are rejected. `Hash` and `Address` are opaque strings. Two more constructs are rejected because TECHNICAL_REPORT.md gives them no meaning yet: `PUBLIC_WITNESS`, and a `ZK<T>` type inside another type (`Optional`, a `Record` field), which §2.7 leaves open.
27. **A fallback must end after the first deadline.** In `s MUST a WITHIN d ELSE s′ MUST a′ BY d′`, if d′ resolves at activation to a time not later than d, the fallback window (d, d′] is empty and the fallback could never be fulfilled. Such a specification is rejected at activation (`else_order_ok`, `else_order_rejected`); after activation every fallback window is non-empty (`else_order_window`). This follows a recommendation of the independent review of stage 13: without it, a fallback deadline earlier than the first deadline was reported as a breach dated before the fallback came into force. An empty window of an obligation with `FROM` (decision 17) and a deadline already past at activation are unchanged: they are breached at the deadline.
28. **Oracle data require provenance, and a penalty requires a currency.** TECHNICAL_REPORT.md §2.9 and the SEMANTIC RULES of the grammar make two optional fields required: `PROVENANCE_REQUIRED: true` whenever the `SOURCE` of a factor is a subject declared `ORACLE`, and `CURRENCY` whenever a breach handler has a `PENALTY`. Until stage 15 the translator did not check either rule, and four examples of `examples/core` broke one of them. A specification that breaks a rule is now rejected at translation ("ORACLE source without PROVENANCE_REQUIRED", "PENALTY without CURRENCY"), like the rules of §2.8 (decision 26). Both fields stay metadata and enter no verdict: §2.9 leaves the attestation mechanism behind `PROVENANCE_REQUIRED` to the compiler, and the core has no monetary type, so a penalty is a number (section 8.4).
29. **Every subject and every factor is declared once, and every subject that is named is declared.** A second declaration of a factor or of a subject is rejected ("duplicate factor", "duplicate subject"). The subject of an obligation, a prohibition, a permission or a breach handler, the recipient of `NOTIFY` and of `ESCALATE_TO`, and the subject named in `SOURCE` must be declared in `SUBJECTS` ("undeclared subject"). This follows the independent review of stage 14: before, a factor declared twice and an undeclared recipient were accepted without a message. The core itself treats subjects as names (`act`, `bound_to`) and does not need a list of them, so this is a check of the translator, like the declared factors of a path.
30. **A subject and a factor do not share a name.** A name in an action argument stands for a subject or for a factor and is not evaluated (decision 24), so in `pay(bob)`, with bob declared both in `SUBJECTS` and in `FACTORS`, the argument would have two readings. Such a specification is rejected ("subject and factor with the same name"). This follows the independent review of stage 15.
31. **The polarity of an event is ignored in both layers** (version 2.5.1). Until version 2.5 the verdicts matched an event by subject and action (`does`), while the trace semantics required the polarity of the norm: an event `(alice, pay, may)` fulfilled `alice MUST pay BY d` but did not complete `alice MUST pay` in a composite term. The polarity written in an event says nothing about what happened, so `does` is moved to `TRIEL_Trace.thy` and used by MUST, MAY and MUST_NOT there too. The input format keeps the polarity, for the events of §2.5 (scenario `examples/core/scenarios/sequence_polarity.scn`).
32. **An action is the event of a later entry, and a prohibition can be violated** (version 2.5.1). This follows the third independent audit (findings S-1 and S-2).
    - The denotation of MUST had the one-entry trace whose event is the action, so in `alice MUST pay THEN alice MUST pay` the junction entry discharged both obligations and one payment was enough. A trace of MUST now has at least two entries (section 4.3, reading 5), as for MAY and as in the verdicts ("actions are the events of later entries", section 8.3, point 19). Two obligations in sequence need two actions (`must_then_must_two_actions`). MUST is still total, through the two-entry trace, so the laws of UNLESS, which hold for all denotations with a total second operand (`unless_then`, `unless_idem`, and the others of section 4.2), and their versions for terms in section 6 are unchanged; they were re-checked with the new denotations.
    - The denotation of MUST_NOT did not depend on its action or its condition, and no term had the outcome Violated. A prohibition now has the violated traces that end with its first forbidden action (section 4.3, reading 6). Violated is reached (`violated_reachable`), also inside a composite term (`then_mustnot_violated`).
    - *Scope.* Two readings were possible. (A) The reading adopted: the prohibition completes at once, as in §2.5, and its violated traces end with its first forbidden action, however late. Alone, or at the end of a sequence, it watches every later entry, and its violated traces are exactly the breached traces of `pr_verdict` cut at the breach (`mustnot_violated_breach`, `breach_mustnot_violated`). But a term that continues after it does not watch its action: in `bob MUST_NOT leak THEN alice MUST pay`, the trace activation, leak, pay is a Done trace of the term, and only its prefix activation, leak is a Violated one. (B) The prohibition stays in force while the rest of the enclosing term runs, so that the leak above violates the whole term. Reading B needs a denotation that runs the prohibition alongside the rest of the term, like `AND`, whose interleaving §2.5 leaves open; it is not adopted. The answers of the report for the whole observed trace therefore do not show a violation in the middle of the trace; the report also gives the status of the term, read on the first prefix that is a violated trace of it or completes it by an executed action, with Violated before Done (decision 34).
    - The prohibition still completes at once, with the one-entry trace and Done, so it does not hold up what follows it. A continuation in a handler bound to a prohibition is still rejected (section 10.6, rule 4).
33. **The evaluator checks the order of the times** (version 2.5.1, finding S-3). Every theorem of finality assumes a trace, whose times do not decrease (`is_trace`). Until version 2.5 only the scenario driver checked this, so the exported `run` gave verdicts on any list: with an entry of 15 July after an entry of 7 August, an obligation breached on 1 August was reported as fulfilled. `evaluate` now rejects such a list before anything else and reports the first entry that is earlier than the one before it (`time_order`, `evaluate_time_order`, `time_order_rejected`). The rejection is a separate line, not a failed activation: activation is a property of the specification at entry 0, and the order of the times is a property of the input, which the activation entry alone cannot show. Finality is then proved for `run` itself, with no assumption on its input (`run_final`): a decided line of the report stays the same when observations are appended, unless the longer list is rejected for its time order or for the types of its data.
34. **The status of a composite term is read on the first prefix that violates the term or completes it by an executed action; a violation takes precedence over Done; with several readings of a prefix the status is conservative** (version 2.5.1, decided after the independent checks of the errata). Under reading A of decision 32, the answers for the whole observed trace do not show a violation followed by more entries: in `bob MUST_NOT leak THEN alice MUST pay` the trace activation, leak, pay is a Done trace, and only its prefix activation, leak is a Violated one (`violation_over_done`). The line of a composite term therefore also reports its status (`status`, `cstatus`).
    - *Modes.* An immediate Done is not an execution: a prohibition completes at once, and so do a permission that is not exercised and `SKIP`, the conditional term with no branch taken. Each trace of a term therefore carries a mode (`mode`, `fden`): `Exec` if its last step is an executed action, an obligation discharged or a permission exercised; `Held` if a prohibition reached at the last entry completed at once there; `Inst` if the term completed at once without one. In a sequence whose second part has one entry, the two parts end at the same entry and the mode is the greater of the two in the order `Inst < Exec < Held` (`mmax`), so a prohibition reached at the end holds the term; an interrupted trace has the mode of its handler. Forgetting the mode gives the denotation (`fden_den`). `mem3m` decides membership with a mode; it is sound for terms without `AND` (`mem3m_dec`, `mem3m_sound`), and for terms without `UNLESS` and `AND` its answer is always definite (`mem3m_definite`), so there it is the characteristic function of `fden` (`mem3m_eq`).
    - *Readings.* A prefix can have several readings: the denotation of an obligation does not fix which of its actions discharges it, the guard of `UNLESS` may fire at the entry of an action, and a prohibition in a branch of `OR` completes at once while the other branch runs. A reading of a prefix has reached a prohibition as the last element of the term when the prefix is a Done or Interrupted trace of the term with the mode `Held` (`reached_prohibition`); `hstep` decides it for one prefix and `held_upto` for the prefixes up to an entry. Since `mmax` puts `Held` above `Inst`, an element that completes at once without executing anything does not hide a prohibition reached at the same entry: in `bob MUST_NOT leak THEN alice MAY ship`, the reading in which the permission is not exercised has reached the prohibition at the first entry, so the term is watched to the end of the trace, also after Alice ships.
    - *Observation.* The prefixes of the observed trace are examined in order (`step`, `pstep`). The observation ends at the first prefix that is a Violated trace of the term, or an Interrupted or Done trace with the mode `Exec`, provided no reading of that prefix or of an earlier one has reached a prohibition: once a reading has reached a prohibition, only a violation ends the observation. The status is Violated if the prefix is a Violated trace; otherwise Interrupted if it is an Interrupted trace with the mode `Exec`, and otherwise Done; so Violated takes precedence over Interrupted and Done, and Interrupted over Done, as in the order Done < Interrupted < Violated of ⊔. If no prefix ends the observation, the status is open (`COpen`); if `mem3`, `mem3m` or `held_upto` leave the first prefix that matters undecided, unknown (`CUnknown`).
    - *Principle.* The status does not miss a violation that a reading of a prefix admits; with several readings it is conservative. Proved for every term without `AND` (`status_no_missed_violation`): if a prefix of the observed trace is a Violated trace of the term, the status is Violated at that entry or before it, unless the status is unknown, which needs `UNLESS` in the term, or the observation has ended at an earlier entry, on a trace with the mode `Exec` that completes the term (Done or Interrupted), when no reading of that prefix or of an earlier one had reached a prohibition. The exception for an earlier completion cannot be dropped: on the trace activation, a', a, with `(s, a) ≠ (s', a')` and times that do not decrease, the term `s MUST_NOT a THEN s' MUST a'` is completed by a' at entry 1, when no reading has reached a prohibition, and its status is Done there, although the whole trace is a Violated trace of it (`violation_after_completion`). Consequences:
        - once a reading of a prefix has reached a prohibition, every later violation is reported, unless the status is unknown or the observation ended at an earlier entry (`reached_prohibition_watched`);
        - in `t THEN s MUST_NOT a`, with `t` without `AND`, a violated prefix that ends at entry k, in a reading where `t` is completed at entry k₀ and the prohibition is violated after it, is reported as a violation at entry k or before it, unless the status is unknown or the term was interrupted, with a handler completed by an executed action, before entry k₀; both exceptions need `UNLESS` in `t` (`then_mustnot_watched`). Without `UNLESS` and `AND` in `t` there is no exception (`then_mustnot_status`); on the reproduction of finding S-1, `alice MUST pay THEN bob MUST_NOT leak` on the trace activation, pay, leak, the status is Violated at entry 2 (scenario `examples/core/scenarios/sequence_prohibition_violated.scn`). Such a sequence is never completed by an executed action (`then_mustnot_held`);
        - in `t OR s MUST_NOT a`, with `t` without `AND`, every violated prefix is reported as a violation at its last entry or before it, unless the status is unknown (`or_mustnot_watched`): `alice MUST pay OR bob MUST_NOT leak` is violated when Bob leaks after Alice pays (scenario `examples/core/scenarios/readings_or_pay_leak.scn`). This is the conservative reading of OR;
        - with `UNLESS`: in `(alice MUST pay UNLESS flag DO alice MUST refund) THEN bob MUST_NOT leak`, when Alice pays before the guard fires and refunds after it, the reading in which the payment completed the first part has reached the prohibition, so the refund does not end the observation and a later leak is a violation; in `alice MUST pay UNLESS flag DO bob MUST_NOT leak`, when the guard fires at the entry of the payment, the reading in which it interrupts the obligation has reached the handler, and the status is open, then violated at a leak (scenarios `examples/core/scenarios/readings_guard_after_pay.scn`, `examples/core/scenarios/readings_guard_at_pay.scn`, `examples/core/scenarios/readings_guard_at_pay_leak.scn`).
    - Sound: at the reported entry the prefix is a Violated trace of the term, or a trace with the reported outcome and the mode `Exec` that is not a Violated one (and, for Done, not an interrupted one with the mode `Exec`), and no reading of it or of an earlier prefix has reached a prohibition; no shorter prefix is a Violated trace, and none is an Interrupted or Done trace with the mode `Exec` unless a reading of it or of an earlier prefix has reached a prohibition (`status_sound`). An open status means the same for every prefix (`status_open`). For terms without `UNLESS` and `AND` the status is never unknown (`status_definite`).
    - Final: once the observation has ended, the status stays, at the same entry, for every extension of the trace (`status_final`); `run_final` covers it, with `decided` and `same_verdict` for composite lines.
    - *Limit of version 2.5.1.* The exception of `status_no_missed_violation` for an earlier completion. If the term is completed by an executed action before any reading of a prefix has reached a prohibition as the last element of the term, the observation ends there, and a later violation of any of its prohibitions is not reported: in `bob MUST_NOT leak THEN alice MUST pay`, on the trace activation, pay, leak, the status is Done at entry 1, and the leak does not change it; in `alice MUST pay UNLESS flag DO bob MUST_NOT leak`, when Alice pays before the guard fires, the status is Done at the payment, and a leak after the guard has fired does not change it, although the whole trace is a Violated trace (the second term of `examples/core/scenarios/readings_guard_after_pay.scn`); and in `alice MUST pay OR (alice MUST ship THEN bob MUST_NOT leak)`, once Alice has paid, neither does a shipment followed by a leak. A term that completes at once without executing anything (a permission that is not exercised, `IF c THEN t` with `c` not true and no `ELSE`, `WHEN c THEN t` with `c` not true) stays open, and so does an interrupted term whose handler completes at once: their status shows no execution. The exact scope, a prohibition in force while the rest of the term runs (reading B of decision 32), is planned for version 2.6.
35. **The expressions the evaluator reads are terms of the composition algebra, and T2 is derived from the closure theorem.** Section 7.3 showed that the conditions of section 7.2 (atoms E_p, ↓p, type checks and comparisons under `NOT`, `AND`, `OR`) are terms of the algebra of [8], and that their stability follows from the closure. The expressions of section 1 are a different type: they also have the literals true and false and `IMPLIES`, and `DEFAULT` inside a comparison. They are now translated too (`expr_cond` to the conditions, `expr_fm` to the formulas directly), and T2 for flat states and for nested data is obtained from the closure (`T2_from_closure`, `T2_nd_from_closure`). Choices made for the translation: the literals are encoded with the algebra's own means rather than by new constant conditions — ↓[] on nested data (the empty complex name is present on every datum) and ∃x ↓x on flat states (true on every named set, for any name x), each with its negation for false; a comparison with `DEFAULT` is translated, not rejected, because the comparison atom of section 7.2 already takes value expressions with `DEFAULT`; what excludes it from the closure is that its atom is not one of the atoms without E_p and `DEFAULT` (`Ex_free_atom`, `expr_cond_Ex_free`), in agreement with `default_breaks_stability`. Nothing in the datatype `cond` or in `cond_fm` changed.
36. **Stability of verdicts under more data is a property of the report, not only of the conditions** (version 2.5.1, after the independent review of the paper). The theorems of stability of section 7.2 (`verdict_stable`, `verdict_stable_nd`) and T2 say that a definite *value* of a `PRESENT`-free condition survives more data. The verdicts of norms are built from such values over a whole trace, and for prohibitions the lifting is not immediate: when an earlier action, whose condition was ⊥, becomes forbidden on more data, the breach moves to that action. Two readings of the same observations are compared with `data_le` (section 4.1) on traces and `obs_le` on lists of observations: the same entries, times and events, and more data at each entry. Proved, for `PRESENT`-free conditions and formulas:
    - on traces: an obligation, with a handler or a fallback, has the same verdict and status (`ob_verdict_data_indep`, `handle_breach_data_indep`, `else_verdict_data_indep`); a breach of a prohibition is never withdrawn, and its time can only move earlier (`pr_verdict_pending_data_mono`, `pr_verdict_data_mono`); an exercised permission stays exercised (`may_verdict_data_mono`); a definite invariant stays the same (`inv_data_mono_le`, `sinv_data_mono_le`); the monitor of a prohibition decides the same actions, and a decision can only change from block to allow (`monitor_decisions_data_mono`, from `blocks_data_mono` of decision 37);
    - in the report: if the observations were accepted, the report on the observations with more data has the same number of lines and each of them refines the line of the original report (`run_data_mono`, with `line_refines`), unless the richer data fails the type check; the time order and the activation cannot fail, since the times are the same and every deadline that resolved resolves to the same time (`activates_mono`, `inv_activates_mono`, `else_order_ok_mono`). A decided line of a norm or an invariant stays decided, at the same index (`run_data_mono_decided`); a breach of a prohibition reported at τ is reported at some τ′ ≤ τ (`run_data_mono_breach`); a prohibition pending on the richer data was pending before (`run_data_mono_pending`).
    - The blocking of stale factors is compatible with this: freshness reads only times and events, so the blocked trace of the richer observations refines the blocked trace of the original ones (`fresh_data_le`, `blockp_data_le`, `btrace_data_le`); so does the removal of hidden factors (`erase_obs_le`).
    - *Limits.* The lines of composite terms are not compared: `IF c THEN t` takes its `ELSE` branch when c is ⊥ (decision 13), so more data can switch the branch and change the status. The actions reported with a breach are not compared either: a penalty is computed in the state of the breach (decision 18), which can move with the breach of a prohibition, and an undefined amount can become defined. And the exception for `PRESENT` cannot be dropped: `pr_verdict_present_not_mono` shows a breach withdrawn by more data when the condition is NOT PRESENT(x). This is the second kind of finality: `run_final` says that a decided verdict does not change when observations are appended; `run_data_mono` says that it is not withdrawn when the missing values of the recorded entries are filled in, in the sense in which a violation found by a monitor on a partial log is not revoked when the log is completed. An entry missing in the middle of the log, for example an unrecorded arrival of a factor under `MAX_AGE`, is covered by neither.
37. **The monitor is a function on traces, with soundness and transparency, and its decisions are part of the report** (decided after an independent review). Until this decision the fail-closed monitor was the predicate `blocks`, and the theorems about it (`breach_blocked`, `enforced_no_breach`, `undefined_guard_blocks_not_breach`) related the predicate to the verdict; the review found that there was no function "apply the monitor to a trace" with theorems about its result, that the column "blocked" of the comparison with Cedar was not an output of the evaluator, and that `undefined_guard_blocks_not_breach` restates the definition. Decided:
    - *The function.* `enforce s a c π` (section 8.1) replaces every blocked action of π by a clock tick with the same time and state and keeps everything else: a suppression automaton (Ligatti, Bauer and Walker, edit automata; Schneider, security automata). It changes exactly the blocked actions (`enforce_blocks_exactly`), its output is a trace (`enforce_is_trace`) with no blocked action (`blocked_action_enforce`), and it is idempotent (`enforce_idempotent`).
    - *Soundness.* The output of the monitor is never breached: `pr_verdict s a c (enforce s a c π) = Pending` (`enforce_sound`), from `enforced_no_breach`. For a PRESENT-free condition, every action let through was taken in a state in which the condition is false in every completion of the data (`enforce_allows_sound`).
    - *Transparency.* A trace the monitor leaves unchanged is not breached (`enforce_unchanged_no_breach`). When the condition is defined at every entry, the converse holds: the monitor leaves a trace unchanged exactly when its verdict is Pending (`enforce_transparent`), and no other edit of the trace that keeps its states and times and is breach-free keeps an action the monitor blocks (`enforce_minimal`). The hypothesis cannot be dropped: an action taken while the condition is undefined is blocked and is not a breach (`enforce_undefined_blocks`, from `undefined_guard_blocks_not_breach`). This is the fail-closed reading of ⊥ stated as a property of the function, not a restatement of `blocks`: the monitor is transparent with respect to the verdict exactly on defined data, and on undefined data it blocks more than the verdict records, which is what `FOUNDATIONS.md` asks of enforcement.
    - *The report.* The evaluator prints, after the invariants, one `MONITOR` line per top-level prohibition with the decision of its monitor at every action of the subject (`monitor_decisions`, `monitor_line`, `LMonitor`; `examples/core/README.md`). (j, T) is listed exactly when `enforce` changes entry j (`monitor_decisions_enforce`). A decision reads the state of the entry before the action, so it is final, and the list on a longer trace begins with the list on the shorter one (`monitor_decisions_append`); `run_final` covers monitor lines, with `same_verdict` reading "the list is extended, not revised". The column "blocked" of `artifact/comparison/README.md` is now quoted from these lines. Prohibitions inside composite terms have no monitor line, as they have no verdict of their own (section 8.3, point 20).
    - *Data.* For a condition without PRESENT, more data never makes the monitor block more: `blocks_data_mono`, and `blocked_action_data_mono` for the actions of a trace.
    - *Exported.* `enforce` and `check_action` are exported with `run`, so the monitor can be applied to a trace outside the evaluator. `check_action c σ` is defined as `blocks c σ` at the types of the evaluator, executed by its code equation `check_action c σ = (case eval c σ of Some False ⇒ False | _ ⇒ True)` (`check_action_code`); the output of `enforce` keeps the times and their order (`enforce_preserves_time_order`).

## 10. Invariants and the evaluator (`TRIEL_Invariants.thy`, `TRIEL_Exec.thy`)

### 10.1 Invariants on finite prefixes

`ALWAYS φ`, `EVENTUALLY φ` and `NEXT φ` are evaluated on the observed prefix of an implementation trace, with the three verdicts of LTL3 (A. Bauer, M. Leucker, C. Schallhart. Runtime verification for LTL and TLTL. *ACM TOSEM* 20(4), 2011). A verdict T or F is given only when every continuation of the prefix would give the same answer; otherwise the verdict is ⊥ (inconclusive).

- `ALWAYS φ` is F from the first entry where φ is F, and ⊥ otherwise; it is never T (`always_never_true`).
- `EVENTUALLY φ` is T from the first entry where φ is T, and ⊥ otherwise; it is never F (`eventually_never_false`).
- `NEXT φ` is the value of φ at entry 1, and ⊥ while the prefix has only the activation entry.
- A definite verdict does not change when the trace is extended (`inv_final`).
- An entry where φ is ⊥ because data is missing neither violates `ALWAYS` nor fulfils `EVENTUALLY` (`always_undefined_data`, `eventually_undefined_data`). For a `PRESENT`-free φ, a definite verdict survives more data at every entry (`inv_data_mono`, from T2).

**`EVENTUALLY φ WITHIN d`** (section 9, decision 19). The deadline d is resolved at the activation entry to a time D (`sinv_eval`); the window is the set of entries with time ≤ D (`ew_eval`).

- The verdict is T as soon as φ is T at an entry of the window (`ew_true`, `ew_at_deadline`), and then `EVENTUALLY φ` is T too (`ew_eventually`).
- It is F once an entry is strictly after D and φ is F at every entry of the window (`ew_missed`); before that it is never F (`ew_not_false_before`). After D it is the strong Kleene disjunction of φ over the window (`ew_after_deadline`), so an entry of the window where φ is ⊥ prevents F (`ew_undefined_data`).
- A definite verdict does not change when the trace is extended with non-decreasing timestamps (`ew_final`), nor, for a `PRESENT`-free φ, when the states carry more data (`ew_data_mono`). `sinv_final` and `sinv_data_mono` state the same for every invariant, with or without a deadline; `inv_data_mono_le` and `sinv_data_mono_le` restate the latter two with the hypothesis `data_le` of section 4.1.
- The invariants are activated only if every deadline in them resolves (`inv_activates`); a deadline from an absent factor rejects the activation (`activation_rejected_inv`), and after activation each one resolves (`inv_activates_resolves`).

### 10.2 Executable equations

`TRIEL_Exec.thy` restates every definition that uses unbounded quantifiers, `LEAST` or `GREATEST` with bounded quantifiers, `find` and `filter`, and proves each restatement equal to the definition: `acted_code`, `passed_code`, `ob_verdict_code`, `may_verdict_code`, `pr_verdict_code`, `bound_to_code`, `wf_block_code`, `fresh_code`, `inv_eval_code`, `ew_eval_code`, `inv_activates_code`, `else_handlers_ok_code`, `eval_code`, `first_at_code`, and, in `TRIEL_Numbers.thy`, `int_rat_code` and `decimal_code`. The entries of a breach, `breach_entry` and `first_forbidden` (section 8.4), are defined with `find` and need no code equation. Typing is a recursive function proved equal to the inductive judgement (`wt_fun_iff`). The code generator uses only these equations and the definitions themselves.

### 10.3 Membership of a composite term

Whether a trace with an outcome belongs to the denotation of a composite term is decided by a three-valued function `mem3` (yes, no, unknown). A companion function `ext3` decides whether a prefix can be continued to a trace of a term. An interrupted trace of `t UNLESS c DO u` needs a continuation of the prefix by `t`. `ext3` decides this for `MUST`, `THEN` chains, `IF` and skip, and for `MUST_NOT` when the prefix already has a forbidden action (no) or its last state makes the condition true (yes). It answers unknown where the answer would depend on the satisfiability of a guard (`MAY` and `MUST_NOT` with a condition that is not true in the last state, `UNLESS` inside the interrupted term).

- `IF` reads its condition in the first state of the trace, and so do `mem3` and `ext3` (`ext_if`, `ext_if_branch`); skip has only one-entry traces, which no proper prefix extends (`mem_skip`, `ext_skip`).
- Soundness: a definite answer is the truth, for every term without `AND` (`mem3_ext3_sound`, `mem3_sound`, in the locale `term_semantics`).
- Definiteness: for terms without `UNLESS` and `AND` the answer is always definite (`mem3_definite`); this includes `IF` and skip.
- Together: for terms without `UNLESS` and `AND`, `mem3` is the characteristic function of the denotation, `mem3 t π r = Some ((π, r) ∈ den t)` (`mem3_eq`; `mem3m_eq` for `mem3m` and `fden`). Soundness and definiteness are two independent properties of a three-valued decision procedure, not the two directions of one equivalence: soundness says that every definite answer is correct, definiteness that an answer is always given. "Completed" in this section means Done or Interrupted by an executed action; it is unrelated to the completions of the data in section 8.

**Named terms and `REF`.** In a `TERMS` block, `REF name` is the surface term `SRef k`, where k is the index of the element `name := t`, counted from 0. A composite element is translated into a term of `tm` under an environment Γ, a list whose entry k is the term of element k; `SRef k` is replaced by Γ ! k (`to_tm_env`). The environment of a block is built from left to right, each element under the terms of the elements before it (`benv`, `benv_nth`).

- `refs_ok`: every `REF` in element i names an element k < i that contains no breach handler. A reference to a later element, or to the element itself, violates it (`refs_forward_rejected`). The reference relation of a block that satisfies it is well-founded (`refs_ok_acyclic`) and has no cycle (`refs_no_cycle`).
- Under `refs_ok`, every element without a handler resolves to a term (`benv_defined`).
- Substitution preserves the denotation (`resolve_den`, `block_den`): the denotation of the resolved term is the reference semantics `sden`, in which `REF k` denotes the denotation of element k.
- A resolved element is a term of `tm`, so its denotation is total (`benv_total`) and the laws of `UNLESS` hold for it with no side condition.
- **Status** (decision 34). `status t π` examines the prefixes `take (Suc k) π` in order and stops at the first one for which `mem3` answers yes for Violated, or `mem3m` answers yes for Interrupted or Done with the mode `Exec` while `held_upto` answers no: no reading of this prefix or of an earlier one has reached a prohibition (`reached_prohibition`). The status is Violated, Interrupted or Done in this order of precedence, with the entry k (`CAt`). It is open (`COpen`) if no prefix stops it, and unknown (`CUnknown`) if the answers leave the first prefix that matters undecided. It is sound (`status_sound`, `status_open`), definite for terms without `UNLESS` and `AND` (`status_definite`), and final (`status_final`). It does not miss a violation that a reading of a prefix admits, with the exception stated in decision 34, which cannot be dropped (`violation_after_completion`; `status_no_missed_violation`, `reached_prohibition_watched`, `then_mustnot_watched`, `then_mustnot_status`, `or_mustnot_watched`).
- `AND` is answered unknown, and the translator rejects it: its denotation depends on the parameter `interleave` (section 6).

### 10.4 The evaluator

`run` takes a specification (factor declarations, the `TERMS` block, invariants) and a list of observations (data, time, event), and returns the report described in [`examples/core/README.md`](../../examples/core/README.md).

- **Hidden factors** (section 9, decision 25). A factor declaration says whether the factor is hidden (`fd_hidden`): a `ZK<T>` factor without `WITHOUT REVEALING ALL`. `run` removes every hidden factor from the data of every entry (`hidden`, `erase`, `erase_obs`) and passes the result to `evaluate`, which does everything below. After the removal a complex name that starts with a hidden factor has no value, and every other one keeps its value (`erase_flat`); the removal keeps times and events, so it commutes with the blocking of stale factors (`erase_btrace`).
  - Noninterference: two lists of observations that are equal once the hidden factors are removed get the same report, typing included (`run_noninterference`); in particular the report is the same with or without the hidden values in the data (`run_erase`). A hidden factor is never reported as ill-typed (`hidden_well_typed`).
  - An expression has the same value in two states that agree on the names it reads, `names` and `pnames` (`eval_agree`, `evalV_agree`). So a condition or a value that reads no hidden factor, as the flow rule requires, has the same value at every entry of the blocked trace with the hidden factors removed and with them left in (`flow_safe_eval`, `flow_safe_evalV`).

- Data are nominative data (section 7). The state of an entry is its data flattened to complex names. Basic values are Booleans, exact numbers, strings and times.
- **Numbers** (`TRIEL_Numbers.thy`). There is no floating point. A number is a rational q (`ANum`). It has type Integer if q ∈ ℤ (`int_rat`), and type Decimal if q = m / 10ᵏ for an integer m (`decimal`); a decimal literal with k digits after the point is m / 10ᵏ (`dec_atom`, `dec_atom_Decimal`). Every Integer is a Decimal (`int_rat_decimal`, `interp_int_dec`). A rational a/b in lowest terms is a Decimal exactly when b divides a power of 10 (`decimal_iff_denominator`), that is, when b has no prime factor other than 2 and 5 (`dec_den_iff`); so 1/3 is not a Decimal (`not_decimal_third`). The ordering comparisons compare numbers as rationals and are false on any other pair of values; `=` on numbers is equality of rationals, so 2500 = 2500.00 (`eval_cmp_num`).
- A factor under `MAX_AGE m` and `ON_STALE BLOCK` is absent, with every complex name that starts with it, at an entry where it has not arrived in the last m seconds (`blockp`). The safety claim of §2.9 holds for this blocking by factor (`blockp_stale_safe`, with `blockp_le` and `blockp_stale_absent`), as it does for `blocked` (section 8).
- **Time order** (section 9, decision 33). `evaluate` first checks that the times of the observations do not decrease (`time_order`); otherwise the report is the single line `LTimeOrder j`, j the first entry earlier than the one before it (`evaluate_time_order`, `time_order_rejected`). With non-decreasing times and at least one observation, the raw trace is a trace (`time_order_is_trace`), and so is the blocked trace (`btrace_is_trace`). The removal of hidden factors keeps the times (`time_order_erase`).
- **Finality of the report** (`run_final`). A line is *decided* (`decided`) if it is the verdict of an obligation that is fulfilled, or breached with a decided continuation; a breached prohibition; a fulfilled permission; a decided obligation with a fallback; or an invariant with a definite value; the line of a composite term whose status has an outcome; and every monitor line. For every list of observations, a decided line of `run` stays the same when observations are appended (for a composite line, its status stays the same, and for a monitor line its decisions are extended and not revised: `same_verdict`), unless the longer list is rejected for its time order or for the types of its data. The proof applies the theorems of finality of sections 8 and 10.1 to the blocked trace, whose prefix is the blocked trace of the shorter list (`btrace_prefix`). The answers of a composite line for the whole observed trace are not verdicts and are not decided: they say whether the whole observed trace is a trace of the term.
- **Stability of the report under more data** (`run_data_mono`, decision 36). `obs_le obs obs′` says that obs′ has the observations of obs, with the same times and events, and at each one data with more values (the information order on the flattened data; `obs_leI_nd` derives it from `nd_le`). `present_free_spec` says that the conditions of the top-level prohibitions and permissions and the formulas of the invariants are without `PRESENT` and `DEFAULT` (`present_free`). If obs was accepted (its report has the line `LTypes None`), then either obs′ is rejected for the types of its data, or the report on obs′ has the same number of lines and line i of it refines line i of the report on obs (`line_refines`): the lines of obligations, fallbacks and handlers are the same up to the reported actions; a prohibition Breached τ is Breached τ′ with τ′ ≤ τ, and a pending one may be anything; a fulfilled permission is fulfilled; a definite invariant is the same; a `MONITOR` line decides the same actions, each decision possibly changed from block to allow (`monitor_line_data_mono`); a composite line is only required to be the line of the same element. Hence `run_data_mono_decided`, `run_data_mono_breach` and `run_data_mono_pending`. The proof applies the theorems of section 8 to the blocked traces, which refine each other (`btrace_data_le`), after activation on more data (`activates_mono`, `inv_activates_mono`, `else_order_ok_mono`).
- Activation is checked next, in the blocked state of entry 0, for the deadlines of the `TERMS` block (`activates`) and of the invariants (`inv_activates`), and for the order of the deadlines of every fallback (`else_order_ok`, decision 27). Then the block is checked with `wf_block`, `cont_free_prohibitions` (section 10.6, rule 4), `else_handlers_ok` (rule 12) and `refs_ok` (section 10.3), and then the types of the data as given (`ill_typed`, `ill_typed_None`). Verdicts, invariants and composite terms are computed on the blocked trace (`btrace`, which keeps the times and events: `btrace_is_trace`).
- An action is a name with a list of arguments, each a name (`ArgName`, not evaluated) or a value (`ArgVal`) (`act`, decision 16).
- After the invariants, every top-level prohibition gets a monitor line (`monitor_line`, `monitor_lines`, `prohibitions`): `LMonitor` with its number and `monitor_decisions` on the blocked trace (decision 37). `run_final` covers these lines: the list of decisions of the longer trace begins with that of the shorter one (`monitor_line_final`, from `monitor_decisions_append`).
- A top-level obligation gets `handle_breach` with the handler bound to it, with its start, window and deadline from `start_of`, `lo_of` and `deadline_of` (`must_line`); a prohibition gets `pr_verdict`. After a breach, both are reported with the informational actions of their handler, each penalty with its amount in the state of the breach (`ob_report`, `pr_report`, section 8.4; `pr_report_actions` relates the latter to `pr_actions`). An obligation with a fallback gets `else_verdict`, with the deadline of the fallback from `else_deadline` (`else_line`). A permission gets `may_verdict`, a handler the element it is bound to, a composite term `mem3` for each outcome and `status` (decision 34), and an invariant `sinv_eval`. A composite term is resolved in the environment of the block first, so a `REF` is reported like the term it names.

`export_code` writes `run`, with `check_action` (the decision of the monitor on one action, `blocks` under its exported name) and `enforce`, to Haskell. `isabelle build -e -D .` exports the module to [`evaluator/generated/TRIEL.hs`](../../evaluator/generated/TRIEL.hs).

### 10.5 Time

- `DATETIME("YYYY-MM-DDThh:mm:ssZ")` is the number of seconds since 1970-01-01T00:00:00Z. Only this ISO-8601 form, in UTC, is accepted.
- `SECOND`, `MINUTE`, `HOUR` and `DAY` durations are converted to seconds. Calendar units (`BUSINESS_DAY`, `MONTH`, `YEAR`) are rejected: their length depends on a calendar, which the core does not model.

### 10.6 The translator and the trusted base

[`parser/triel_to_core.py`](../../parser/triel_to_core.py) parses a specification with the reference grammar and translates it into the input of `run`. Every construct is translated, printed as metadata, or rejected by name. Only the outermost unsupported construct is reported. The translator's table of grammar rules is checked against the grammar by [`parser/test_triel_to_core.py`](../../parser/test_triel_to_core.py).

Metadata: `JURISDICTION`, `STANDARD`, `CURRENCY`, `PROVENANCE_REQUIRED`, `PROOF_SYSTEM`, `CURVE`, the `DID` of a subject, the `POLARITY`, `THRESHOLD`, `SOURCE` and `SENSITIVITY_BOUND` of each factor (section 9, decision 20; `CAUSED_BY` is rejected), and the `PROVES` constraints and `BOUND_TO` of a `ZK<T>` factor (decision 26). The class of an invariant (`SAFETY`, `LIVENESS`, `FAIRNESS`) is a label.

Translation rules:

1. **`PENALTY`.** `PENALTY e CAP c` is `(penalty P CAP)`. The amount e is built from numeric literals, Integer and Decimal factors and `DEFAULT` with `+`, `-` and `*`: P ::= (val V) | (add P P) | (sub P P) | (mul P P) | (neg P). Division is rejected ("division in PENALTY"), and so is any operand that is not a number ("PENALTY of a non-number"). CAP is a numeric literal or `(none)` ("CAP (not a number)"). The amount is computed by the evaluator (section 8.4); informational actions still do not affect the status (`informational_irrelevant`).
2. **Boolean conditions.** A Boolean factor used as a condition, `x`, is translated to `x == true`, and `a != b` to `NOT (a == b)`. Both translations are visible in the printed core AST.
3. **`PRESENT`.** `PRESENT` is accepted only on a complex name of primitive type.
   - This is a restriction of the translator, not of the semantics. On nominative data, `PRESENT(p)` is the total indicator E_p for every complex name p, including one that leads to a record (`T5_nd_present`, `present_nd_is_Ex`, `Ex_nd_total`, section 7).
   - The evaluator works on the flattened state (section 10.4), where a record has no complex name of its own, so `PRESENT` of a record would be F there. The translator rejects it instead of giving a wrong answer.
4. **Handlers of prohibitions.** A handler binds as `bound_to` does: to the nearest preceding obligation or prohibition of its subject at the top level.
   - For a prohibition with a handler, the report shows the verdict and, after a breach, the informational actions of the handler, `NOTIFY` and `PENALTY`, in source order (`pr_actions`, `pr_actions_informational`, `pr_actions_breached`).
   - §2.6 defines continuations only for obligations. A continuation-determining action (`TERMINATE`, `CURE_BY`, `ESCALATE_TO`) in a handler bound to a prohibition is rejected with the message "§2.6 defines continuations only for obligations". The evaluator checks the same condition (`cont_free_prohibitions`) and otherwise reports `BLOCK REJECTED`, so after a breach every action of such a handler is reported (`pr_actions_cont_free`).

5. **Numbers and comparisons.** An integer literal is `(int N)`, and a decimal literal is `(dec M K)`, the number M / 10ᴷ: `12.50` is `(dec 1250 2)`. `a < b` and `a <= b` are `(lt a b)` and `(le a b)`; `a > b` is `(lt b a)` and `a >= b` is `(le b a)`. An ordering comparison whose operand is not of type Integer or Decimal, nor a numeric literal, is rejected ("ordering comparison of a non-number"), so the value order is applied only to numbers.

6. **Conditional terms.** `IF c THEN t ELIF c₂ THEN t₂ ELSE e` is `(if c t (if c₂ t₂ e))`; a missing `ELSE` is `(skip)`. `WHEN c THEN t` is `(if c t (skip))`. The branches are composite terms.
7. **Named terms.** `name := t` is the element t of the block; it is in force like any other element and is reported under its own number. `REF name` is `(ref K)`, K the index of that element counted from 0. Rejected: a reference to an undeclared name ("REF to an undeclared name"); to a name declared at or after the reference, which includes every cycle ("REF to a name declared later"); to an element with a breach handler ("REF to a breach handler"); to an element with a deadline, which a composite term cannot carry ("REF to a term with a deadline"); and a name declared twice ("duplicate term name").
8. **`DEFAULT`.** `DEFAULT(f, d)` is `(default PATH V)`. f must not lead to a record ("DEFAULT of a record"), for the reason given in rule 3. d must be a value of the type of f: a literal, a factor or another `DEFAULT` ("DEFAULT fallback (not a value)", "DEFAULT fallback of another type"); Integer and Decimal are compatible. A Boolean `DEFAULT` used as a condition is `DEFAULT(f, d) == true`.

9. **Action arguments.** `pay(bob, 100)` is `(action "pay" (path "bob") (int 100))`. An argument is a literal, or the name of a subject or a factor, which is printed as a path and not evaluated. Anything else is rejected ("action argument (not a name or literal)"), and so is a name that is neither a subject nor a factor ("action argument (undeclared name)").
10. **`FROM`.** An obligation is `(must S A DL ST)`, where ST, the start given by `FROM`, is `(at T)`, `(factor PATH 0)` or `(none)`. `UNTIL` is not part of an obligation (a syntax error, decision 21). `FROM` inside a composite term is rejected ("FROM in a composite term") and a `REF` to an obligation with `FROM` ("REF to a term with FROM"), for the reason given for deadlines.
11. **`EVENTUALLY … WITHIN`.** `EVENTUALLY(c) WITHIN d` is `(eventually_within X DL)`, where DL is translated as the deadline of an obligation: `(at T)`, `(after N)` or `(factor PATH N)`. A calendar unit is rejected, as in a deadline.
12. **`WITHIN … ELSE`.** `s MUST a WITHIN d ELSE s′ MUST a′ [BY d′]` at the top level is `(must_else S A DL S2 A2 DL2)`; DL2 is `(none)` without `BY`. In the trace semantics of §2.5 it is the choice `TOr` of the two obligations (`to_tm_env`). Rejected: `ELSE` in a composite term ("WITHIN ... ELSE in a composite term"), a fallback that is not an obligation ("ELSE (non-obligation)"), `FROM` in the fallback ("FROM in ELSE") or in the first obligation ("FROM with ELSE"), a handler bound to such an obligation ("ON_BREACH bound to WITHIN ... ELSE"), and a `REF` to it ("REF to a term with a deadline").
13. **`ZK<T>` factors** (decisions 25 and 26). A `ZK<T>` factor is a factor of type T; `Hash` and `Address`, also as T, are strings. Without `WITHOUT REVEALING ALL` it is `(hidden_factor NAME TY AGE)`, otherwise `(factor NAME TY AGE)`. A hidden factor read anywhere but as a bare action argument is rejected ("ZK flow rule"). Rejected by the rules of TECHNICAL_REPORT.md §2.8: a `ZK<T>` factor without `PROOF_SYSTEM` or `CURVE` ("ZK type without PROOF_SYSTEM", "ZK type without CURVE"), a `ZK<T>` factor whose `SOURCE` subject has a `DID` and which has no `BOUND_TO` ("ZK type without BOUND_TO"), a `BOUND_TO` subject without a `DID` ("BOUND_TO subject without DID"), a nonce or a `HASH` salt that is not a declared factor ("undeclared nonce", "undeclared salt"). Also rejected: `PUBLIC_WITNESS` and a `ZK<T>` type inside another type ("nested ZK type").

Further rejections:
- A deadline inside a composite term is rejected: the trace semantics of §2.5 has no time, so the deadline would be ignored. This includes the branches of `IF` and `WHEN`.
- `MAX_AGE` without `ON_STALE`, and `ON_STALE` without `MAX_AGE`, are rejected.
- A fallback whose deadline is a `DATETIME` not later than the `DATETIME` of the first deadline is rejected ("ELSE deadline not after the first deadline"). Other deadlines are compared by the evaluator at activation (decision 27).
- By the rules of TECHNICAL_REPORT.md §2.9 (decision 28), a factor sourced from an `ORACLE` subject without `PROVENANCE_REQUIRED: true` is rejected ("ORACLE source without PROVENANCE_REQUIRED"), and so is a `PENALTY` without `CURRENCY` ("PENALTY without CURRENCY").
- A subject or a factor declared twice is rejected ("duplicate subject", "duplicate factor"), and so is an undeclared subject of a term, of a handler, of `NOTIFY`, `ESCALATE_TO` or `SOURCE` ("undeclared subject", decision 29).
- A subject and a factor with the same name are rejected ("subject and factor with the same name", decision 30).
- The checks of `wf_block` are made at translation too (decisions 8 and 9), so that a translated specification is never reported `BLOCK REJECTED`: a handler inside a composite term ("ON_BREACH in a composite term"), a handler with no preceding obligation or prohibition of its subject at the top level, for example after a permission only ("ON_BREACH bound to no obligation or prohibition"), two handlers bound to one norm ("two ON_BREACH bound to one norm") and a handler with two continuation-determining actions ("two continuation-determining actions"). With two obligations of one subject and one trailing handler, the handler is bound to the second (`bound_to`).
- A record type with a field declared twice ("duplicate field"), and a deadline or a `FROM` read from a factor that is not a `DateTime` ("deadline of a non-DateTime factor", "FROM of a non-DateTime factor"), are rejected: such a deadline would never resolve (`time_of`), and the activation would be rejected.

Beyond Isabelle/HOL, the following are trusted:
- Isabelle's code generator and GHC;
- the translator;
- the reading of the input and the printing of the report in [`evaluator/Main.hs`](../../evaluator/Main.hs);
- the conversion of scenarios in [`parser/triel_eval.py`](../../parser/triel_eval.py), which reads strings with the escapes of `Main.hs`, rejects a factor or a field given twice in one entry, and leaves the order of the times to the evaluator.

Every verdict is computed by the exported code.
