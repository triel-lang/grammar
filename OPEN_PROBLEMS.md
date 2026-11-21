# Open problems

These are problems about the formal core of TRIEL (`formal/core`, described in `formal/core/CORE.md`) that are open and that the maintainers are not working on. Nothing in the project depends on their solution. Each is stated with the place in `CORE.md` that leaves it open and with what counts as a result.

## Terms

- The maintainers do not work on these problems, and nothing in the language, the tools or the plans of the project waits for them.
- This is not a list of every open point in `CORE.md`. Some of the others are part of the maintainers' own work; a contribution on them may be declined.
- No problem here changes the language, the grammar, the translator or the evaluator. A parameter that a problem adds to the theory, such as a latency bound, is a parameter of the theory, as the rate bound of section 11 is (`CORE.md`, 11.3, decision 5).
- A result in Isabelle/HOL is a new theory in a session of its own outside `formal/core`. It imports the session `TRIEL_Core` (for problem 3 also the session of `LTL3_Semantics`, [20] in `RELATED_WORK.md`) and changes no file of `formal/core`. It builds with the Isabelle release set in `ISABELLE_VERSION` of `.github/workflows/isabelle.yml`, without `sorry`, `oops`, `axiomatization`, `quick_and_dirty` or `skip_proofs`, and its theorems depend on no oracle beyond the one exception stated for the core in the opening paragraphs of `CORE.md`. A theorem stated inside a locale counts only together with an interpretation of the locale.
- Building `TRIEL_Core` as its `ROOT` stands also typesets its document and needs LaTeX (opening paragraphs of `CORE.md`). For a build without LaTeX, the document may be switched off in a working copy of `ROOT`, as CI does (`.github/workflows/isabelle.yml`, step `Switch off the PDF document for this build`); the result does not depend on that change.
- A result for problem 2 is a Mizar article accepted by the Mizar verifier, with the versions of the Mizar system and of the Mizar Mathematical Library named in it.
- A contribution to this repository is accepted under the [TRIEL Contributor License Agreement](CLA.md); see [CONTRIBUTING.md](CONTRIBUTING.md). The theories of `formal/core` are under Apache-2.0 OR BSD-3-Clause ([LICENSE.md](LICENSE.md)), so work published elsewhere can build on them under either license and needs no agreement with the maintainers. To let others know that a problem is being worked on, open an issue.
- In this file, "the finality theorems of 11.2" are `pr_verdictI_final`, `monitor_decisionsI_append`, `inv_evalI_final`, `ew_evalI_final` and their checked forms `checked_pr_verdictI_final`, `checked_monitor_decisionsI_final`, `checked_inv_evalI_final`, `checked_ew_evalI_final`.

## 1. A rate bound together with `MAX_AGE`

**Where it is open.** `CORE.md`, 11.4, "A fresh reading is not exact"; the reading of section 11 in 11.1; `MAX_AGE` and `ON_STALE BLOCK` in 8.1 (`fresh`, `blocked`); the stale reading in 10.4.

Section 11 reads a name with a rate bound from all its samples, whatever their age: `MAX_AGE` and `ON_STALE BLOCK` have no effect on it, and no theorem relates the enclosure (`enclosed`) to the stale reading of section 10.4 (`blockp`, `btrace`). The combined reading is not implemented: for a bounded name under `MAX_AGE` and `ON_STALE BLOCK`, the enclosure while its last reading is at most m seconds old, and no value afterwards. `CORE.md` notes that it would be stricter than the enclosure alone and still sound, since an absent name only makes a `PRESENT`-free condition less defined (T2), and that this is not proved.

**Result.** A definition of the combined interval state of an entry:
- a name without a rate bound is read as the stale reading of section 10.4 reads it;
- a bounded name under `MAX_AGE` m and `ON_STALE BLOCK` has its enclosure at the time of the entry when it is fresh there in the sense of `fresh`, and no value otherwise;
- any other bounded name, without `MAX_AGE` or under `USE_LAST`, has its enclosure, as in `enclosed`.

And proofs of:
1. on a consistent trace, for every `PRESENT`-free condition, its value on the combined interval state is ≼ its value on `enclosed` (the combined reading is never more defined; compare `evalI_mono`), and the two are equal at an entry where every name under `MAX_AGE` and `ON_STALE BLOCK` is fresh;
2. the counterparts of `evalI_sound_signals` and `monitor_sound_signals` for the combined reading;
3. the counterparts of the finality theorems of 11.2.

Items 2 and 3 are expected to follow from item 1 and the theorems of 11.2; the substance of the problem is the definition and item 1.

## 2. A Mizar formalisation of the nominative data of TRIEL

**Where it is open.** `CORE.md`, section 7 (`TRIEL_ND.thy`), which formalises the definitions below in Isabelle/HOL only; the article [7] listed in `FOUNDATIONS.md`.

Section 7 gives the data of TRIEL the structure of multi-level nominative data, following the Mizar formalisation of simple-named complex-valued nominative data by Ivanov, Nikitchenko, Kryvolap and Korniłowicz ([7] in `FOUNDATIONS.md`). On top of the operations of [7] it defines complex names and their values, an information order, flattening to a state over complex names, and the indicator predicate E_p. Which of them already exist in [7] or elsewhere in the Mizar Mathematical Library is part of the problem.

**Result.** A Mizar article, building on [7], that defines the value of a complex name (`den_path`), the information order (`nd_le`), flattening (`flat`), E_p (`Ex_nd`) and equitone predicates on nominative data (`equitone_nd`: a predicate whose value is defined at d keeps that value at every d′ with d ≤ d′), and proves the counterparts, with the same statements, of `nd_le_refl`, `nd_le_trans`, `nd_le_antisym`, `flat_mono`, `Ex_nd_total` and `Ex_nd_not_equitone` (`CORE.md`, 7.1 and 7.2; `TRIEL_ND.thy`). For `flat_mono` the order on states is ⊑ of `CORE.md`, section 1.

## 3. The verdicts of the invariants compared with LTL3

**Where it is open.** `CORE.md`, 10.1; `RELATED_WORK.md` (LTL3 [14], `LTL3_Semantics` [20]).

The verdicts of `ALWAYS φ`, `EVENTUALLY φ` and `NEXT φ` on a finite prefix are three-valued in the style of LTL3 and final once decided (`inv_final`). Correspondence with LTL3 is not proved, and the verdicts differ: for a state formula φ that is true in every state, such as the literal true, LTL3 gives `ALWAYS φ` the verdict T on every prefix, while in TRIEL it stays ⊥ (`always_never_true`).

**Result.** A comparison, not a change of the verdicts of TRIEL:
- a translation of `ALWAYS φ`, `EVENTUALLY φ` and `NEXT φ` into LTL3 that maps the Boolean structure of φ (`true`, `false`, `NOT`, `AND`, `OR`, `IMPLIES`) to the propositional connectives of LTL3 and each atom of φ (a comparison or `PRESENT`) to an atomic proposition;
- theorems that characterise, in terms of φ and the prefix, for example by the validity or unsatisfiability of the propositional skeleton of φ, the finite prefixes on which the TRIEL verdict of an invariant differs from the LTL3 verdict of its translation, among the prefixes where φ has the value T or F at every entry;
- among them, proofs of the two differences: for `ALWAYS true` the TRIEL verdict is ⊥ (`always_never_true`) and the LTL3 verdict is T; for `EVENTUALLY false` the TRIEL verdict is ⊥ (`eventually_never_false`) and the LTL3 verdict is F.

Verdicts are written T, F and ⊥ (inconclusive) for both logics, as in `CORE.md`, 10.1. The semantics of LTL3 may be taken from [20]. `EVENTUALLY … WITHIN` is not part of the problem. A state formula of TRIEL can be ⊥ on a state with missing data; how to compare such prefixes is part of the problem.

## 4. Latency between measurement and arrival

**Where it is open.** `CORE.md`, 11.3, decision 4; 11.1 and 11.2.

In section 11 the time of a sample is the time of its arrival entry. If the sensor measured earlier, the enclosure is wrong by the latency times the bound; the theory assumes no latency.

**Result.** A theory with a latency bound δ ≥ 0, a rational parameter. A sample (t, v) of a name arrives at time t and was measured at some time in [t − δ, t]. A family of signals is admissible if each signal f is a signal under the rate bound of its name and, for every sample (t, v) of that name, f(s) = v for some s in [t − δ, t]. An enclosure and a consistency check for this assumption, both computed from the samples, δ and the bound in rational arithmetic with executable equations, as in 11.1, and proofs of the counterparts of:
- `adm_in_enc`, `evalI_sound_signals`, `monitor_sound_signals` and the finality theorems of 11.2 (soundness and finality);
- `consistent_iff_adm` and `adm_family_exists` (a trace is accepted exactly when an admissible family exists, so the soundness theorems are not vacuous);
- `enc_tight`, in the form that fits latency: for a finite non-empty set of samples consistent in the new sense, both bounds of the enclosure at a time are values that admissible signals take there, so the enclosure is the least closed interval that contains those values. With latency these values need not form an interval: with the bound 1, δ = 1 and two samples of one name that arrive at time 0 with the values 0 and 1, the admissible signals take at time 0 exactly the values 0 and 1;
- and that for δ = 0 the enclosure is the enclosure of section 11.

The language is unchanged: carrying a measurement time in the data would be a question of the language (11.3, decision 4) and is not part of this problem.

## 5. Optimality of the interval evaluation

**Where it is open.** `CORE.md`, 11.4, "Soundness and finality only"; 8.5 (`evalG`, `kleene_optimal`).

For the completions of the data and a type of values with two different values, `kleene_optimal` shows that strong Kleene evaluation is the most defined sound compositional evaluation: among the evaluations `evalG G` that read the atoms as `eval` does and combine subformulas with connectives G on three values, sound with respect to every completion. For the evaluation on interval states of section 11 (`evalI`), only soundness and finality are proved. That evaluation is not complete: x < c OR x ≥ c is ⊥ when the enclosure straddles c (`straddle_undefined`), and two occurrences of one factor, or two factors from one sensor, are treated as independent. No analogue of `kleene_optimal` is proved.

**Result.**
- (a) The family `evalIG G`: atoms are read as `evalI` reads them, and `NOT`, `AND`, `OR` and `IMPLIES` are combined with connectives G on three values. A definition of soundness of G: for every `PRESENT`-free condition, every interval state whose numeric intervals are non-empty (`proper`) and every real valuation inside it, the value of the condition under `evalIG G` is ≼ its value under `evalR`; and a proof or a refutation that every sound G is pointwise ≼ the strong Kleene connectives, so that `evalI` is the most defined sound evaluation of the family (the analogue of `kleene_optimal`).
- (b) Optionally, a larger class that reads atoms differently, with its most defined sound element. For example, on an interval [p, q] with p < q, `evalI` gives x < x the value ⊥, while x < x is false for every real value of x; an evaluation that reads x < x as F is sound and more defined than `evalI`.
