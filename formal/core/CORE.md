# TRIEL core: definitions and theorems

This is a mechanised core of the TRIEL specification language, checked in Isabelle/HOL. The theory is [`TRIEL_Core.thy`](TRIEL_Core.thy), and [`ROOT`](ROOT) defines the session `TRIEL_Core`.

It is based only on the public material at <https://github.com/triel-lang/grammar>: TECHNICAL_REPORT.md §2.9 and FOUNDATIONS.md. It makes no assumptions about any non-public implementation.

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
