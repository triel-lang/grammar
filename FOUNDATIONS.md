# Foundations

TRIEL's semantics builds on the composition-nominative approach (CNA) to program logics developed at Taras Shevchenko National University of Kyiv.

## References

1. M. S. Nikitchenko, S. S. Shkilnyak. *Applied Logic* (Прикладна логіка). Textbook. Kyiv: Kyiv University Publishing Centre, 2013.
2. M. Nikitchenko, S. Shkilniak. Algebras and logics of partial quasiary predicates. *Algebra and Discrete Mathematics*, 23(2), 2017, 263–278.
3. M. Nikitchenko. Composition-Nominative Methods and Models in Program Development. *SN Computer Science*, 3, 507, 2022. https://doi.org/10.1007/s42979-022-01335-2
4. M. Nikitchenko, O. Shkilniak, S. Shkilniak. Pure first-order logics of quasiary predicates. *Problems in Programming*, No. 2–3, 2016, 73–86 (in Ukrainian).
5. O. Shkilniak, S. Shkilniak. Transitional modal logics of quasiary predicates with equality and sequent calculi for these logics. UkrPROG'2024, *CEUR Workshop Proceedings*, Vol. 3806, 2024. https://ceur-ws.org/Vol-3806/S_49_Shkilniak.pdf
6. I. Ivanov, M. Nikitchenko, U. Abraham. Event-based proof of the mutual exclusion property of Peterson's algorithm. *Formalized Mathematics*, 2015.

Section numbers (§) refer to the textbook [1]. Page numbers are omitted because the available edition is a preliminary version with approximate pagination.

## How each construct rests on these works

The table states, for each TRIEL construct, which part of these works it rests on and how far the connection goes:

* **Adopted** — the definition from these works is used as is.
* **Defined here** — these works provide the basis; the TRIEL-specific definition is given in `TECHNICAL_REPORT.md`.
* **Open** — no settled definition yet; these works provide at most background.

| TRIEL construct | Basis | Status |
|---|---|---|
| Partial truth values (⊥) and the connectives `AND`, `OR`, `NOT` | §5.1 (propositional compositions of partial predicates, Kleene algebras); §6.2.1 (three-valued logics) | Adopted |
| Rule states as named data | §4.1 (nominative data) | Adopted |
| Nested records in rule states | §4.2 (logics over hierarchical data); [3] | Adopted |
| Invariants stable under extension of the state | §1.1.2 and §2.5 (equitone functions and predicates) | Defined here: satisfiability of invariants over states |
| `PRESENT(x)` (value-presence predicate) | Chapter 3, conclusions (indicator predicates); the total indicator predicate *Ex*, true where `x` has a value and false where it has none [4], [5]; the related composition εx [2] | Adopted: on a value that is not stale, `PRESENT(x)` is *Ex*. As in [5], *Ex* is total and not monotone, which agrees with `PRESENT` being the deliberate non-monotone exception in `TECHNICAL_REPORT.md` §2.9. Defined here: a stale value is treated as absent, so `PRESENT(x)` is false for a stale `x` (see Staleness) |
| Fail-closed evaluation of prohibitions when a condition is ⊥ | none | Open: TRIEL-specific rule |
| Parameter passing into `EXECUTE` | §2.4 (renomination composition); §5.5 (infinitary renominative logics) | Adopted for renaming; isolation is Open (classical renomination overrides values, isolation also requires restriction) |
| Obligations, permissions, prohibitions | §7.3.2 (deontic logic) | Background only; the denotations of TRIEL obligations are Open |
| `WITHIN` and other deadlines | §7.2 (temporal modal logics), §7.2.3 (temporal logics for specification and verification of programs) | Background only; the denotation of `WITHIN` is Open |
| Execution outcomes (`Done`, `Interrupted`, `Violated`) and verdicts (`Fulfilled`, `Violated`, `Pending`) | §7.4 (composition-nominative modal systems); §7.5 (properties of transition modal systems) | Open: the mapping from outcomes to verdicts |
| Staleness (`ON_STALE`) | none | Open: two options are compatible with the approach — extending the value carrier, or tracking access to a name and checking a dedicated staleness predicate; the choice depends on the overall semantics |
| Interruption and compositionality | [6] (relating state-based and event-based semantics on an example) | Open: interruption breaks compositionality; candidate treatments are continuation semantics, a combination of state-based and event-based semantics, and state-machine semantics |

The open rows correspond to the open items of `TECHNICAL_REPORT.md`. The denotations of `IF`, `WHEN` and `ON_BREACH` and of named terms are also open, and are not tied to a specific section of these works.

## Method

Formal work on TRIEL follows the practice of the approach: it starts from a small, precisely stated core fragment of the language, for which an axiomatic system and the corresponding soundness and completeness results can be established, with proofs mechanised in a proof assistant such as Isabelle. Further constructs are added to the core one at a time.
