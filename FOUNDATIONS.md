# Foundations

TRIEL's semantics builds on the composition-nominative approach (CNA) to program logics developed at Taras Shevchenko National University of Kyiv.

## References

1. M. S. Nikitchenko, S. S. Shkilnyak. *Applied Logic* (Прикладна логіка). Textbook. Kyiv: Kyiv University Publishing Centre, 2013.
2. M. Nikitchenko, S. Shkilniak. Algebras and logics of partial quasiary predicates. *Algebra and Discrete Mathematics*, 23(2), 2017, 263–278.
3. M. Nikitchenko. Composition-Nominative Methods and Models in Program Development. *SN Computer Science*, 3, 507, 2022. https://doi.org/10.1007/s42979-022-01335-2
4. M. Nikitchenko, O. Shkilniak, S. Shkilniak. Pure first-order logics of quasiary predicates. *Problems in Programming*, No. 2–3, 2016, 73–86 (in Ukrainian).
5. O. Shkilniak, S. Shkilniak. Transitional modal logics of quasiary predicates with equality and sequent calculi for these logics. UkrPROG'2024, *CEUR Workshop Proceedings*, Vol. 3806, 2024. https://ceur-ws.org/Vol-3806/S_49_Shkilniak.pdf
6. I. Ivanov, M. Nikitchenko, U. Abraham. Event-based proof of the mutual exclusion property of Peterson's algorithm. *Formalized Mathematics*, 2015.
7. I. Ivanov, M. Nikitchenko, A. Kryvolap, A. Korniłowicz. Simple-named complex-valued nominative data – definition and basic operations. *Formalized Mathematics*, 25(3), 2017, 205–216.

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
| Nested records in rule states | §4.2 (logics over hierarchical data); [3]; [7] (the definition followed in `formal/core/TRIEL_ND.thy`) | Adopted |
| Invariants stable under extension of the state | §1.1.2 and §2.5 (equitone functions and predicates) | Defined here: satisfiability of invariants over states |
| `PRESENT(x)` (value-presence predicate) | Chapter 3, conclusions (indicator predicates); the total indicator predicate *Ex*, true where `x` has a value and false where it has none [4], [5]; the related composition εx [2] | Adopted: on a value that is not stale, `PRESENT(x)` is *Ex* (theorem `present_is_Ex` in [`formal/core/TRIEL_Ex.thy`](formal/core/TRIEL_Ex.thy)). As in [5], *Ex* is total and not monotone, which agrees with `PRESENT` being the deliberate non-monotone exception in `TECHNICAL_REPORT.md` §2.9. Defined here: a stale value is treated as absent, so `PRESENT(x)` is false for a stale `x` (see Staleness) |
| Fail-closed evaluation of prohibitions when a condition is ⊥ | none | Open: TRIEL-specific rule |
| Parameter passing into `EXECUTE` | §2.4 (renomination composition); §5.5 (infinitary renominative logics) | Adopted for renaming; isolation is Open (classical renomination overrides values, isolation also requires restriction) |
| Obligations, permissions, prohibitions | §7.3.2 (deontic logic) | Background only; the denotations of TRIEL obligations are Open |
| `WITHIN` and other deadlines | §7.2 (temporal modal logics), §7.2.3 (temporal logics for specification and verification of programs) | Background only; the denotation of `WITHIN` is Open |
| Execution outcomes (`Done`, `Interrupted`, `Violated`) and verdicts (`Fulfilled`, `Violated`, `Pending`) | §7.4 (composition-nominative modal systems); §7.5 (properties of transition modal systems) | Open: the mapping from outcomes to verdicts |
| Staleness (`ON_STALE`) | none | Open: two options are compatible with the approach — extending the value carrier, or tracking access to a name and checking a dedicated staleness predicate; the choice depends on the overall semantics |
| Interruption and compositionality | [6] (relating state-based and event-based semantics on an example) | Open: interruption breaks compositionality; candidate treatments are continuation semantics, a combination of state-based and event-based semantics, and state-machine semantics |

The open rows correspond to the open items of `TECHNICAL_REPORT.md`. The denotations of `IF`, `WHEN` and `ON_BREACH` and of named terms are also open, and are not tied to a specific section of these works.

## Standard results and their authors: map of verified foundations

Beyond the composition-nominative approach, TRIEL rests on standard results of logic, semantics and cryptography. For each layer of TRIEL, the table names the classical result and its original source, and the theorems of the Isabelle/HOL formalisation in [`formal/core`](formal/core/CORE.md) that check it. The status column has three values:

- **Proved**: the listed theorems are machine-checked, with no unproved steps and no added axioms.
- **Open question**: the formalisation exposes a question that the language definition does not settle.
- **Ahead**: not yet formalised.

| TRIEL layer | Classical result and author | Theorem in Isabelle (file) | Status |
|---|---|---|---|
| Expressions: `Boolean`; `AND`, `OR`, `NOT` on defined values | Algebra of logic. G. Boole. *The Mathematical Analysis of Logic*. Cambridge: Macmillan, Barclay & Macmillan, 1847; *An Investigation of the Laws of Thought*. London: Walton and Maberly, 1854 | `T4_classical`, `T4_total` ([`TRIEL_Core.thy`](formal/core/TRIEL_Core.thy)); `T4_nd` ([`TRIEL_ND.thy`](formal/core/TRIEL_ND.thy)) | Proved: on fully defined data, three-valued evaluation is two-valued evaluation |
| Expressions: ⊥ and the connectives on undefined data | Strong three-valued logic. S. C. Kleene. On notation for ordinal numbers. *Journal of Symbolic Logic*, 3(4), 1938, 150–155 | `T1_and_commute`, `T1_or_commute`, `T1_and_assoc`, `T1_or_assoc`, `T1_de_morgan_and`, `T1_de_morgan_or`, `T1_not_not`, `kimp_kor_knot` ([`TRIEL_Core.thy`](formal/core/TRIEL_Core.thy)); `T1_nd` ([`TRIEL_ND.thy`](formal/core/TRIEL_ND.thy)) | Proved |
| Expressions and data: monotonicity under the information order (`TECHNICAL_REPORT.md` §2.9) | Information ordering of partial values. D. S. Scott. *Outline of a Mathematical Theory of Computation*. Technical Monograph PRG-2, Oxford University Computing Laboratory, 1970; Data types as lattices. *SIAM Journal on Computing*, 5(3), 1976, 522–587 | `T2_monotone`, `info_le_antisym` ([`TRIEL_Core.thy`](formal/core/TRIEL_Core.thy)); `present_free_equitone` ([`TRIEL_Ex.thy`](formal/core/TRIEL_Ex.thy)); `T2_nd_monotone`, `nd_le_antisym`, `flat_mono` ([`TRIEL_ND.thy`](formal/core/TRIEL_ND.thy)) | Proved, for flat states and for nested nominative data |
| `PRESENT(x)` | Existence predicate of free logic. H. S. Leonard. The logic of existence. *Philosophical Studies*, 7(4), 1956, 49–64; K. Lambert. Existential import revisited. *Notre Dame Journal of Formal Logic*, 4(4), 1963, 288–292 | `Ex_ind_exists` (E!x ≡ ∃y. y = x), `present_is_Ex` ([`TRIEL_Ex.thy`](formal/core/TRIEL_Ex.thy)); `present_nd_is_Ex` ([`TRIEL_ND.thy`](formal/core/TRIEL_ND.thy)) | Proved for the existence predicate. Quantifiers of free logic are not formalised |
| Temporal invariants: `ALWAYS`, `EVENTUALLY`, `NEXT`; LTL operators | Linear temporal logic. A. Pnueli. The temporal logic of programs. *18th Annual Symposium on Foundations of Computer Science*, IEEE, 1977, 46–57 | none | Ahead |
| CTL operators (`AX` … `ER`) | Computation tree logic. E. M. Clarke, E. A. Emerson. Design and synthesis of synchronization skeletons using branching time temporal logic. *Logics of Programs* (1981), LNCS 131, Springer, 1982, 52–71 | none | Ahead |
| Terms: `MUST`, `MAY`, `MUST_NOT` | Deontic logic. G. H. von Wright. Deontic logic. *Mind*, 60(237), 1951, 1–15 | `total_must`, `total_may`, `total_mustnot`, `wf_must`, `wf_may`, `wf_mustnot` ([`TRIEL_Trace.thy`](formal/core/TRIEL_Trace.thy)) | Proved for the trace denotations of §2.5. The deontic reading of satisfaction and breach (§2.6) is Ahead |
| `ON_BREACH`, `CURE_BY` | Contrary-to-duty obligations. R. M. Chisholm. Contrary-to-duty imperatives and deontic logic. *Analysis*, 24(2), 1963, 33–36 | none | Ahead |
| Terms: `THEN`, `OR`, `UNLESS` | Process and program logics. C. A. R. Hoare. Communicating sequential processes. *Communications of the ACM*, 21(8), 1978, 666–677; D. Harel. *First-Order Dynamic Logic*. LNCS 68, Springer, 1979 | `unless_false`, `unless_or`, `unless_then`, `unless_idem`, `unless_then_counterexample`, `unless_nested_ne_or` ([`TRIEL_Trace.thy`](formal/core/TRIEL_Trace.thy)); `den_total`, `term_unless_then` ([`TRIEL_Terms.thy`](formal/core/TRIEL_Terms.thy)) | Proved: the laws of `UNLESS` in §2.5, and distributivity over `THEN` for every term |
| Terms: `AND` | Interleaving of processes. C. A. R. Hoare, 1978 (as above) | `interleaving.total_and`, `interleaving_satisfiable` ([`TRIEL_Trace.thy`](formal/core/TRIEL_Trace.thy)) | Open question: `interleave` is not defined in §2.5. It is a parameter with one stated assumption |
| Interruption (open item) | Continuation semantics. C. Strachey, C. P. Wadsworth. *Continuations: A Mathematical Semantics for Handling Full Jumps*. Technical Monograph PRG-11, Oxford University Computing Laboratory, 1974; J. C. Reynolds. Definitional interpreters for higher-order programming languages. *Proceedings of the ACM Annual Conference*, vol. 2, 1972, 717–740 | `den` and the laws of `UNLESS` for terms ([`TRIEL_Terms.thy`](formal/core/TRIEL_Terms.thy)) | Open question. For the terms of §2.5 the denotation is defined by structural recursion: outcomes record the interruption, and no continuations are used. Deadlines and breach handling are not covered |
| `HASH` | SHA-256. NIST. *Secure Hash Standard (SHS)*. FIPS PUB 180-4, August 2015 | none | Ahead |
| `PROOF_SYSTEM: GROTH16` | Pairing-based SNARK. J. Groth. On the size of pairing-based non-interactive arguments. *EUROCRYPT 2016*, Part II, LNCS 9666, Springer, 2016, 305–326 | none | Ahead |
| `PROOF_SYSTEM: PLONK` | PLONK. A. Gabizon, Z. J. Williamson, O. Ciobotaru. PLONK: Permutations over Lagrange-bases for oecumenical noninteractive arguments of knowledge. Cryptology ePrint Archive, 2019/953, 2019 | none | Ahead |
| `PROOF_SYSTEM: STARK` | Transparent arguments of knowledge. E. Ben-Sasson, I. Bentov, Y. Horesh, M. Riabzev. Scalable, transparent, and post-quantum secure computational integrity. Cryptology ePrint Archive, 2018/046, 2018 | none | Ahead |
| `PROOF_SYSTEM: BULLETPROOFS` | Bulletproofs. B. Bünz, J. Bootle, D. Boneh, A. Poelstra, P. Wuille, G. Maxwell. Bulletproofs: Short proofs for confidential transactions and more. *IEEE Symposium on Security and Privacy*, 2018, 315–334 | none | Ahead |
| `CURVE: "BN254"` | Barreto–Naehrig curves. P. S. L. M. Barreto, M. Naehrig. Pairing-friendly elliptic curves of prime order. *Selected Areas in Cryptography – SAC 2005*, LNCS 3897, Springer, 2006, 319–331 | none | Ahead |
| The grammar notation | Extended Backus–Naur Form. N. Wirth. What can we do about the unnecessary diversity of notation for syntactic definitions? *Communications of the ACM*, 20(11), 1977, 822–823; ISO/IEC 14977:1996 | none. The examples are checked against the grammar by the workflow `parse-examples.yml`, outside Isabelle | Ahead |

Defined by TRIEL itself, with no external source: fail-closed evaluation of prohibitions, the treatment of stale values by `PRESENT` and `DEFAULT`, `ON_STALE`, `BOUND_TO`, `PROVENANCE_REQUIRED`, `CURRENCY` and the `PENALTY` cap, and the trace semantics of `TECHNICAL_REPORT.md` §2.5. Of these, the trace semantics of §2.5 is formalised in [`TRIEL_Trace.thy`](formal/core/TRIEL_Trace.thy) and [`TRIEL_Terms.thy`](formal/core/TRIEL_Terms.thy).

## Method

Formal work on TRIEL follows the practice of the approach: it starts from a small, precisely stated core fragment of the language, for which an axiomatic system and the corresponding soundness and completeness results can be established, with proofs mechanised in a proof assistant such as Isabelle. Further constructs are added to the core one at a time.

A first core fragment is mechanised in Isabelle/HOL in [`formal/core`](formal/core/CORE.md): strong Kleene evaluation over partial named data, the monotonicity claim of `TECHNICAL_REPORT.md` §2.9, the non-monotonicity of `PRESENT`, and agreement with two-valued logic on fully defined states.
