# TRIEL core: definitions and theorems

This is a mechanised core of the TRIEL specification language, checked in Isabelle/HOL. The theories are [`TRIEL_Core.thy`](TRIEL_Core.thy) (expressions, sections 1–3), [`TRIEL_Trace.thy`](TRIEL_Trace.thy) (trace semantics, section 4), [`TRIEL_Ex.thy`](TRIEL_Ex.thy) (the indicator predicate *Ex*, section 5), [`TRIEL_Terms.thy`](TRIEL_Terms.thy) (the term language, section 6), [`TRIEL_ND.thy`](TRIEL_ND.thy) (nominative data, section 7) [`TRIEL_Breach.thy`](TRIEL_Breach.thy) (deadlines and breach, section 8), [`TRIEL_Invariants.thy`](TRIEL_Invariants.thy) (invariants, section 10), [`TRIEL_Indicators.thy`](TRIEL_Indicators.thy) (the indicators E_z and ↓z and the stability of verdicts, section 7.2), [`TRIEL_Compositions.thy`](TRIEL_Compositions.thy) (the quantifier, renomination, closure under the base compositions, and conditions as terms, section 7.3) and [`TRIEL_Exec.thy`](TRIEL_Exec.thy) (the evaluator exported to Haskell, section 10). [`ROOT`](ROOT) defines the session `TRIEL_Core`. `TRIEL_ND.thy` uses the finite maps of `HOL-Library`.

It is based only on the public material at <https://github.com/triel-lang/grammar>: TECHNICAL_REPORT.md §2.5, §2.6 and §2.9, and FOUNDATIONS.md. It makes no assumptions about any non-public implementation.

To build it, open `Isabelle2025-2\Cygwin-Terminal.bat` on Windows (or any shell on Linux/macOS), go to this folder, and run:

```
isabelle build -D .
```

`isabelle build -e -D .` also writes the exported evaluator to `evaluator/generated/`.

The build was checked with Isabelle2025-2. The output of a clean build (`isabelle build -c -v -D .`) is saved in [`build.log`](build.log).

The build also typesets the theories, with a short introduction ([`document/root.tex`](document/root.tex)), into `output/document.pdf`. This step needs a LaTeX installation that provides `lualatex`, for example MiKTeX or TeX Live.

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
4. **Law 3.** §2.5 states it without a side condition, but it needs ⟦t₂⟧ to be total (see the counterexample above). Every term form with a denotation in §2.5 gives a total denotation (AND under the interleaving assumption of item 3). For the term language of section 6 this is proved for every term (`den_total`), so law 3 holds there with no side condition (`term_unless_then`).
5. **MAY.** eval(c, σₙ₋₁) with n = |π| − 1 has no state to refer to when π has a single entry. So a taken action gives a trace of at least two entries, and c is evaluated in the state before the action.

### 4.4 Not formalised

These term forms have no denotation in §2.5 and are outside this theory: `IF c THEN t`, `WHEN c THEN t`, `ON … DO`, `WITHIN … ELSE`, `REF`, `EXECUTE` and `ON_BREACH`. The breach and deadline semantics of §2.6 and the satisfaction of `INVARIANTS` are not formalised either.

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

- **Denotation.** The denotation `den` maps each term, structurally, to the denotation of section 4. It is defined in the locale `term_semantics`, which extends `interleaving` with timestamps in a linear order, because AND needs `interleave`.

### 6.2 Theorems

- **`den_total`:** ⟦t⟧ is total for every term t.
  — Every term can start from any entry.
- **`term_unless_false`, `term_unless_or`, `term_unless_idem`:** laws 1, 2 and 4 of §2.5, stated for terms.
- **`term_unless_then`:** ⟦(t₁ THEN t₂) UNLESS c DO e⟧ = ⟦(t₁ UNLESS c DO e) THEN (t₂ UNLESS c DO e)⟧ for all terms t₁, t₂, e and every guard c.
  — Law 3 holds for the term language with no side condition, because every term is total.

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
- **`T4_nd`:** agreement with two-valued logic, with PRESENT read as presence of a node.
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
- A *condition* (`cond`) is built from atoms by NOT, AND and OR, and evaluated with the strong Kleene connectives of section 1 (`cond_eval`). Its verdict is T, F or ⊥. Over nominative data the atoms are E_p (`AEx`), ↓p (`ADown`), and "p is an atom of primitive type q" (`AIs`, `is_prim`), which is ⊥ when p leads to nothing and F when it leads to a record.

*Theorems* (all in `TRIEL_Indicators.thy`):

- **`T_DownInd_eq_T_Ex`:** T(↓z) = T(E_z).
- **`DownInd_P_pred`, `DownInd_irrefutable`, `DownInd_mono`, `DownInd_equitone`, `DownInd_equitone_R`:** ↓z is a P-predicate, F(↓z) = ∅, and ↓z is monotone and equitone.
- **`DownInd_is_eq_zz`, `self_eq_is_DownInd`:** ↓z is =zz, so on the flat named sets of section 1 ↓z is the comparison `z == z`. On nominative data `p == p` is below ↓p (`self_eq_below_present_partial`): it is ⊥ when p leads to a record.
- **`Ex_R_P_pred`, `Ex_R_total`, `pval_Ex_R_present`:** E_z is single-valued and total, and it is PRESENT(z).
- **`Ex_R_counterexample`, `Ex_R_not_mono`, `Ex_R_not_equitone_R`:** ∅ ⊑ [z ↦ v], with E_z(∅) = F and E_z([z ↦ v]) = T. So E_z[∅] = {F} is not a subset of E_z[[z ↦ v]] = {T}, and E_z is not monotone.
- **`present_partial_domains`, `present_partial_below_present`, `present_partial_mono`, `present_partial_equitone`, `DownInd_nd_equitone_R`:** partial presence has the truth domain of E_p and an empty falsity domain. Wherever it is defined it agrees with PRESENT(p), and it is monotone under the extension ≤ of nominative data.
  — `self_eq_below_present_partial`: the comparison p == p is below ↓p. It is ⊥ when p leads to a record, because comparisons see only atoms.
- **`cond_equitone`, `verdict_stable`, `verdict_stable_nd`:** if every atom of a condition is equitone, the condition is equitone: a definite verdict T or F stays the same under every extension of the data. Over nominative data this holds for every condition whose atoms are ↓p and type checks, without E_p.
- **`opt_cond_Ex_wt`, `Ex_breaks_stability`, `Ex_cond_not_equitone`:** with the atom E_p the property fails. The condition "NOT E_f OR f has type q" is the typing judgement of Record {f: Optional⟨q⟩} (`opt_cond_Ex_wt`). On the data of `wt_not_mono_optional` (the empty record, extended by [f ↦ b] where b is not of type q) its verdict changes from T to F.
- **`opt_cond_Down_wt`, `Down_cond_equitone`:** the same condition with ↓f agrees with typing when f is present and is ⊥ when f is absent. On the same data its verdict changes from ⊥ to F, so no definite verdict is overturned.
- **`inv_data_mono_equitone`:** the LTL3 verdicts of invariants (section 10.1) survive more data for every state formula whose predicate is equitone. `inv_data_mono` is the case of PRESENT-free formulas.
- **`equitone_R_not`, `equitone_R_or`, `equitone_closure_equitone`:** the equitone P-predicates are closed under the negation and the disjunction of R-predicates (`R_not`, `R_or`; on P-predicates these are the Kleene ¬ and ∨, `pval_R_not`, `pval_R_or`), and ↓z is one of them. So every predicate built from ↓z and equitone P-predicates by ¬ and ∨ is an equitone P-predicate.

*Reading.* "The field is absent for good" corresponds to E_x on a closed record: E_x(d) = F is a definite answer, and it is right only if no extension can add the field. "The value is not yet known" corresponds to the undefinedness of ↓x: ↓x(d) = ⊥, and an extension can only make it T. A condition written with ↓ never gives a verdict that more data would overturn (`verdict_stable_nd`). A condition written with E_x can (`Ex_breaks_stability`). The meanings of `PRESENT` and of Optional are unchanged: `PRESENT` is E_x (section 9, decision 1), and typing with Optional is still not monotone.

**Open question.** Does this reading match the intent of the composition-nominative approach for data that arrive over time? That is: should an absence in data that may still arrive be read as ↓ (not yet known), and an absence in a closed record as E_x (absent for good)?

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
- **Conditions as formulas.** A nominative datum d is read as the named set p ↦ d(p) over complex names (`nd_named`). The translation `cond_fm` sends E_p to `FE p`, ↓p to `FDown p`, and "p is an atom of primitive type q" to a base predicate symbol, interpreted by `is_R`. NOT and OR go to ¬ and ∨. AND goes to ¬(¬Φ ∨ ¬Ψ), because conjunction is not a base composition.

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
- **`cond_fm_correct`:** for every condition φ of section 7.2 and every datum d, the interpretation of `cond_fm φ` on p ↦ d(p) has the value of φ on d. So every TRIEL condition is a term of the composition algebra.
- **`cond_equitone_from_closure`, `verdict_stable_from_closure`:** the stability of verdicts of section 7.2 (`verdict_stable_nd`) follows from the closure. A condition without E_p translates to a formula without E_z, and that formula denotes an equitone P-predicate.

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
  - **Prohibition.** s MUST_NOT a WHEN c is Breached at the first action a of s before which ⟦c⟧ = T, where c is evaluated in the state before the action (`pr_verdict`).
  - **Permission.** s MAY a WHEN c is never breached (`may_verdict`).
- **Enforcement and verdict: two roles.** A monitor *enforces* a prohibition fail-closed: it blocks the action unless c is known to be false, so it also blocks on ⊥ (`blocks`). The *verdict* records a breach only when c = T. The fail-closed rule listed in `FOUNDATIONS.md` belongs to enforcement, not to the verdict.
- **Breach actions.** NOTIFY and PENALTY are informational. TERMINATE, CURE_BY and ESCALATE_TO determine the continuation (`baction`, `is_cont`). A handler is well formed if it has at least one action and at most one continuation-determining action (`wf_actions`).
- **Status after a breach** (`handle_breach`):
  - with no continuation-determining action, or with TERMINATE, the obligation stays breached and is closed;
  - CURE_BY k opens the window (τ_b, τ_b + k] from the moment of breach τ_b;
  - ESCALATE_TO s′ gives s′ a new obligation for the same action, with a window of the same length counted from the moment of transfer.
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
- **`breach_blocked`:** every breach of a prohibition is an action the monitor would have blocked.
- **`enforced_no_breach`:** if no action was taken in a blocking state, there is no breach.
- **`undefined_guard_blocks_not_breach`:** if c = ⊥, the monitor blocks, but the verdict is not a breach.
  — Enforcement is strictly stronger than the verdict.
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
- **`fresh_at_max_age`:** an age equal to MAX_AGE is still fresh.
- **`stale_absent`:** under BLOCK a stale factor is absent, so PRESENT is F.
- **`stale_safe`:** a result computed with stale factors treated as absent is not overturned by whatever values those factors have when refreshed.
  — This is the safety claim of §2.9, derived from T2.

### 8.3 Clarifications of §2.6

Points 1–14 are the points where §2.6 is ambiguous or contradictory. Points 15–21 are further readings needed to formalise it.

1. **Binding.** §2.6 binds a handler to the nearest preceding obligation and also says that two obligations with one trailing handler have no defined meaning. The binding rule is adopted: the handler binds to the nearest one, and the others have no handler.
2. **Handlers are top-level.** Syntactically a handler is a term, but it has no denotation as one. It is allowed only at the top level of a TERMS block; a nested handler is rejected (`nested_handler_rejected`).
3. **Polarity.** An implementation event is matched by subject and action; the polarity belongs to the norm.
4. **Prohibitions.** The condition c of MUST_NOT WHEN c is evaluated in the state before the action. The verdict is Breached only when c = T. Fail-closed handling of ⊥ belongs to enforcement (see 8.1).
5. **Origin of durations.** Durations in BY and in a term-level WITHIN count from the activation time τ₀. CURE_BY counts from the moment of breach.
6. **Boundary.** An action at the deadline fulfils. A breach is established only when the trace has an entry strictly after the deadline, and the time of breach is the deadline.
7. **Deadline from a factor.** It is fixed at activation; if the factor is absent there, the activation is rejected.
8. **WITHIN without ELSE.** A missed deadline is a breach (`within_missed_breach`). WITHIN … ELSE is not formalised.
9. **Failed cure.** A failed cure is a second breach and is final: no handler applies to it, so there is no loop.
10. **ESCALATE_TO s′.** The original obligation stays breached. s′ gets a new obligation for the same action, with a window of the same length (d − τ₀) counted from the moment of transfer.
11. **TERMINATE** closes the obligation, not the whole specification.
12. **Only informational actions.** The obligation stays breached and is closed.
13. **FROM … UNTIL** is not formalised.
14. **MAX_AGE.** An age equal to MAX_AGE is still fresh. Under USE_LAST the last value is kept and is present.
15. **Binding target.** A handler binds to an obligation *or a prohibition* of the same subject, as §2.6 states.
16. **One handler per norm.** At most one handler per obligation or prohibition (`wf_one_handler`).
17. **No deadline.** An obligation without a deadline is never breached. This is semantically sound, but a future analyser of specifications should warn about it: no verdict can hold such an obligation to account.
18. **CURE_BY** takes a duration.
19. **Activation entry.** Entry 0 of an implementation trace is the activation entry; actions are the events of later entries.
20. **Scope of verdicts.** Verdicts are given to the top-level elements of a TERMS block. Deadlines inside composite terms are resolved at activation (and can reject it), but have no verdict of their own.
21. **Handlers of prohibitions.** §2.6 defines continuations only for obligations. A handler bound to a prohibition may have only informational actions; the evaluator and the translator reject a continuation there (section 10.6, rule 4).

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
   - The monitor blocks on ⊥ (`blocks`). Every breach is an action the monitor would have blocked (`breach_blocked`), enforcement prevents breach (`enforced_no_breach`), and on ⊥ the two roles differ (`undefined_guard_blocks_not_breach`).
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

## 10. Invariants and the evaluator (`TRIEL_Invariants.thy`, `TRIEL_Exec.thy`)

### 10.1 Invariants on finite prefixes

`ALWAYS φ`, `EVENTUALLY φ` and `NEXT φ` are evaluated on the observed prefix of an implementation trace, with the three verdicts of LTL3 (A. Bauer, M. Leucker, C. Schallhart. Runtime verification for LTL and TLTL. *ACM TOSEM* 20(4), 2011). A verdict T or F is given only when every continuation of the prefix would give the same answer; otherwise the verdict is ⊥ (inconclusive).

- `ALWAYS φ` is F from the first entry where φ is F, and ⊥ otherwise; it is never T (`always_never_true`).
- `EVENTUALLY φ` is T from the first entry where φ is T, and ⊥ otherwise; it is never F (`eventually_never_false`).
- `NEXT φ` is the value of φ at entry 1, and ⊥ while the prefix has only the activation entry.
- A definite verdict does not change when the trace is extended (`inv_final`).
- An entry where φ is ⊥ because data is missing neither violates `ALWAYS` nor fulfils `EVENTUALLY` (`always_undefined_data`, `eventually_undefined_data`). For a `PRESENT`-free φ, a definite verdict survives more data at every entry (`inv_data_mono`, from T2).

### 10.2 Executable equations

`TRIEL_Exec.thy` restates every definition that uses unbounded quantifiers, `LEAST` or `GREATEST` with bounded quantifiers, `find` and `filter`, and proves each restatement equal to the definition: `acted_code`, `passed_code`, `ob_verdict_code`, `may_verdict_code`, `pr_verdict_code`, `bound_to_code`, `wf_block_code`, `fresh_code`, `inv_eval_code`, `eval_code`, `first_at_code`. Typing is a recursive function proved equal to the inductive judgement (`wt_fun_iff`). The code generator uses only these equations and the definitions themselves.

### 10.3 Membership of a composite term

Whether a trace with an outcome belongs to the denotation of a composite term is decided by a three-valued function `mem3` (yes, no, unknown). A companion function `ext3` decides whether a prefix can be continued to a trace of a term. An interrupted trace of `t UNLESS c DO u` needs a continuation of the prefix by `t`. `ext3` decides this for `MUST` and for `THEN` chains, and answers unknown where the answer would depend on the satisfiability of a guard (`MAY` with a condition that is not true, `UNLESS` inside the interrupted term).

- Soundness: a definite answer is the truth, for every term without `AND` (`mem3_ext3_sound`, `mem3_sound`, in the locale `term_semantics`).
- Completeness: for terms without `UNLESS` and `AND` the answer is always definite (`mem3_complete`).
- `AND` is answered unknown, and the translator rejects it: its denotation depends on the parameter `interleave` (section 6).

### 10.4 The evaluator

`run` takes a specification (factor declarations, the `TERMS` block, invariants) and a list of observations (data, time, event), and returns the report described in [`examples/core/README.md`](../../examples/core/README.md).

- Data are nominative data (section 7). The state of an entry is its data flattened to complex names. Basic values are Booleans, integers, strings and times.
- A factor under `MAX_AGE m` and `ON_STALE BLOCK` is absent, with every complex name that starts with it, at an entry where it has not arrived in the last m seconds (`blockp`). The safety claim of §2.9 holds for this blocking by factor (`blockp_stale_safe`, with `blockp_le` and `blockp_stale_absent`), as it does for `blocked` (section 8).
- Activation is checked first, in the blocked state of entry 0. Then the block is checked with `wf_block` and `cont_free_prohibitions` (section 10.6, rule 4), and then the types of the data as given (`ill_typed`, `ill_typed_None`). Verdicts, invariants and composite terms are computed on the blocked trace (`btrace`, which keeps the times and events: `btrace_is_trace`).
- A top-level obligation gets `handle_breach` with the handler bound to it, a prohibition `pr_verdict` with the informational actions of its handler after a breach (`pr_actions`), a permission `may_verdict`, a handler the element it is bound to, a composite term `mem3` for each outcome, and an invariant `inv_eval`.

`export_code` writes `run` to Haskell. `isabelle build -e -D .` exports the module to [`evaluator/generated/TRIEL.hs`](../../evaluator/generated/TRIEL.hs).

### 10.5 Time

- `DATETIME("YYYY-MM-DDThh:mm:ssZ")` is the number of seconds since 1970-01-01T00:00:00Z. Only this ISO-8601 form, in UTC, is accepted.
- `SECOND`, `MINUTE`, `HOUR` and `DAY` durations are converted to seconds. Calendar units (`BUSINESS_DAY`, `MONTH`, `YEAR`) are rejected: their length depends on a calendar, which the core does not model.

### 10.6 The translator and the trusted base

[`parser/triel_to_core.py`](../../parser/triel_to_core.py) parses a specification with the reference grammar and translates it into the input of `run`. Every construct is translated, printed as metadata, or rejected by name. Only the outermost unsupported construct is reported. The translator's table of grammar rules is checked against the grammar by [`parser/test_triel_to_core.py`](../../parser/test_triel_to_core.py).

Metadata: `JURISDICTION`, `STANDARD`, `CURRENCY`, `PROVENANCE_REQUIRED`, and the `SOURCE` of each factor. The class of an invariant (`SAFETY`, `LIVENESS`, `FAIRNESS`) is a label.

Translation rules:

1. **`PENALTY`.** The amount must be a literal and is kept as an opaque value, since informational actions do not affect the status (`informational_irrelevant`). Arithmetic in `PENALTY` is rejected.
2. **Boolean conditions.** A Boolean factor used as a condition, `x`, is translated to `x == true`, and `a != b` to `NOT (a == b)`. Both translations are visible in the printed core AST.
3. **`PRESENT`.** `PRESENT` is accepted only on a complex name of primitive type.
   - This is a restriction of the translator, not of the semantics. On nominative data, `PRESENT(p)` is the total indicator E_p for every complex name p, including one that leads to a record (`T5_nd_present`, `present_nd_is_Ex`, `Ex_nd_total`, section 7).
   - The evaluator works on the flattened state (section 10.4), where a record has no complex name of its own, so `PRESENT` of a record would be F there. The translator rejects it instead of giving a wrong answer.
4. **Handlers of prohibitions.** A handler binds as `bound_to` does: to the nearest preceding obligation or prohibition of its subject at the top level.
   - For a prohibition with a handler, the report shows the verdict and, after a breach, the informational actions of the handler, `NOTIFY` and `PENALTY`, in source order (`pr_actions`, `pr_actions_informational`, `pr_actions_breached`).
   - §2.6 defines continuations only for obligations. A continuation-determining action (`TERMINATE`, `CURE_BY`, `ESCALATE_TO`) in a handler bound to a prohibition is rejected with the message "§2.6 defines continuations only for obligations". The evaluator checks the same condition (`cont_free_prohibitions`) and otherwise reports `BLOCK REJECTED`, so after a breach every action of such a handler is reported (`pr_actions_cont_free`).

Further rejections:
- A deadline inside a composite term is rejected: the trace semantics of §2.5 has no time, so the deadline would be ignored.
- `MAX_AGE` without `ON_STALE`, and `ON_STALE` without `MAX_AGE`, are rejected.

Beyond Isabelle/HOL, the following are trusted:
- Isabelle's code generator and GHC;
- the translator;
- the reading of the input and the printing of the report in [`evaluator/Main.hs`](../../evaluator/Main.hs);
- the conversion of scenarios in [`parser/triel_eval.py`](../../parser/triel_eval.py).

Every verdict is computed by the exported code.
