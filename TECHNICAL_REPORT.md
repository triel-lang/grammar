# TRIEL: A Declarative Specification Language with Native Temporal and Zero-Knowledge Constraints

**Technical Report — Draft v0.1**

---

## Abstract

TRIEL is an open, declarative specification language in which a single, human-readable source expresses subjects, obligations, factors, and temporal invariants over a system's behavior. Unlike specifications expressed in natural language or in general-purpose programming languages, a TRIEL specification's invariants are drawn from a decidable fragment of linear and branching-time temporal logic (LTL/CTL), and its data fields may carry zero-knowledge constraints — provable predicates that do not require revealing the underlying value. This report describes the language's syntax and semantics (Section 2), motivates the specification-implementation gap it addresses (Section 3), positions it relative to existing specification and policy languages (Section 4), and states plainly what the language does and does not claim to guarantee (Section 5).

The grammar described here (v2.4) is published under the Open Web Foundation Agreement 1.0 at `github.com/triel-lang/grammar`; every example in this report is drawn from that repository and can be independently checked against the published EBNF.

---

## 1. The Specification–Implementation Gap

### 1.1 The Problem

A specification is typically written once, in natural language or in a semi-formal document, and the system that implements it is built, maintained, and modified separately. Over the life of a project, the two diverge: the implementation accumulates edge-case handling, bug fixes, and expedient decisions that the original specification never mentioned, while the specification itself is rarely revisited once the implementation exists. This divergence is a well-documented source of compliance failures, audit findings, and — in systems with autonomous or semi-autonomous components — behavior that satisfies no one's actual intent.

Three common responses to this gap each fall short in a specific, identifiable way:

- **Natural-language specifications** ("the system shall process refunds within 5 business days") are readable by anyone, but provide no mechanical way to check whether an implementation actually satisfies them, and no way to detect when two clauses of the same specification are in tension with each other.
- **Pointing a capable code-reading tool at the implementation** — increasingly common now that large language models can navigate large codebases — conflates *what the code does* with *what the code was meant to do*. Code captures implementation, including its bugs and shortcuts; a tool reading only the code has no independent signal for which behaviors were intended and which were accidental.
- **Markdown or prose requirements documents** improve on pure natural language by giving structure, but provide no mechanism for surfacing contradictions. Two sections can assert incompatible constraints without the document format doing anything to flag the conflict; catching it is left entirely to the diligence of whoever wrote or last reviewed the document.

### 1.2 Why Temporal Logic and Not Just Assertions

Even specification approaches that do use formal or semi-formal constructs — assertions, unit tests, schema validators — typically check a system's state at a single point in time: "the balance is non-negative right now." Many real specifications are not single-point claims but claims about *sequences of states over time*: "a refund request must eventually be resolved," "a payment must never be split once initiated," "once an account is flagged, it must remain flagged until a reviewer clears it." These are properties of *traces*, not of individual states, and expressing them naturally requires temporal operators — `ALWAYS`, `EVENTUALLY`, `NEXT` — as first-class parts of the specification language, not as a library convention layered on top of an otherwise atemporal assertion mechanism.

### 1.3 Why Zero-Knowledge Constraints, Natively

A related but distinct gap appears whenever a specification must express a compliance condition on a value without disclosing the value itself — "the applicant is over 18," "the account balance exceeds the required threshold," "the vehicle stayed within its permitted zone" — without revealing the birth date, the exact balance, or the route. These conditions are usually implemented by reaching for a separate zero-knowledge proof toolkit, disconnected from whatever specification language governs the rest of the system's behavior: the *business rule* ("an adult may proceed") lives in one artifact, and the *cryptographic circuit* proving the rule's precondition lives in another, with no machine-checked relationship between the two. TRIEL treats a zero-knowledge provability constraint as a type-level annotation on a field — `ZK<Decimal> PROVES (self >= threshold) WITHOUT REVEALING self` — so that the business rule and the disclosure boundary are stated in the same place, by the same author, and checked by the same compiler.

---

## 2. The TRIEL Language (v2.4)

This section summarizes the published grammar's structure; the full EBNF (`TRIEL-grammar-v2_4-core.ebnf`) is authoritative and should be consulted for exact syntax. All examples below are drawn verbatim or near-verbatim from the repository's `examples/` directory.

### 2.1 Top-Level Structure

A TRIEL specification consists of a declaration header, a set of typed subjects, a set of terms (obligations, permissions, prohibitions, and event-triggered rules), a set of factors (typed, optionally zero-knowledge-constrained data fields), and a set of temporal invariants:

```triel
SPECIFICATION age_verification VERSION 1.0.0
    JURISDICTION "EU"

SUBJECTS {
    Applicant : PARTY
}

FACTORS {
    age : ZK<Integer> PROVES (self >= 18) WITHOUT REVEALING self
}

TERMS {
    ON verification_requested(applicant) DO
        Applicant MAY proceed WHEN age >= 18
}

INVARIANTS {
    age_gate_enforced : SAFETY : ALWAYS (proceed_granted IMPLIES age >= 18)
}
```

### 2.2 Deontic Primitives

Obligations, permissions, and prohibitions are the language's three deontic primitives, each binding a subject to an action under an optional condition or deadline:

- `subject MUST action [BY deadline] [FROM start] [UNTIL end]` — an obligation.
- `subject MAY action [WHEN condition] [WITHIN deadline]` — a permission.
- `subject MUST_NOT action [WHEN condition]` — a prohibition.

These compose through `AND` (parallel), `OR` (choice), `THEN` (sequence), and `UNLESS ... DO` (guarded alternative evaluated once at entry), and can be attached to events via `ON event DO term`.

### 2.3 Factors and Zero-Knowledge Constraints

A factor is a typed, named value — a piece of state the specification reasons about. Factors carry a `POLARITY` (whether the factor's increase counts toward or against compliance) or are marked `METADATA` (a value supplied from outside the specification, such as a configurable threshold). A factor's type may additionally be a zero-knowledge type:

```
zk_type ::= "ZK" "<" primitive_type ">" zk_constraints
zk_constraints ::= "PROVES" "(" zk_constraint {"," zk_constraint} ")"
                   ["WITHOUT" "REVEALING" zk_visibility]
```

A `zk_constraint` is restricted, by design, to comparisons against a literal, a range, a set, or a hash — not to an arbitrary expression over other factors. This is a deliberate simplification relative to general-purpose zero-knowledge circuit languages (Section 4.2): TRIEL's zero-knowledge constraints express *what must be provable about a single field*, not the full circuit logic a dedicated ZK-DSL would compile. Where a specification needs to relate a zero-knowledge-constrained factor to another factor (e.g., "assets exceed liabilities," where liabilities are also specification-level state), that relationship is expressed as an ordinary invariant over both factors, keeping the ZK-constraint syntax itself simple and the cross-factor relationship visible in the same `INVARIANTS` block as every other temporal property.

### 2.4 Temporal Invariants

An invariant is either a state invariant (`ALWAYS(expr)`, `EVENTUALLY(expr) [WITHIN deadline]`, `NEXT(expr)`) or a full LTL/CTL formula built from the standard temporal operators (`G`, `F`, `X`, `U`, `R`, `W` for LTL; `A`/`E` path quantifiers combined with `X`/`F`/`G`/`U`/`R` for CTL). Both logics may appear in the same specification's `INVARIANTS` block, each validated according to its own semantics; mixing is permitted because the two logics answer different questions (LTL: does *this* trace satisfy the property; CTL: does *every*/*some* trace from this state satisfy it) that a single specification may need to ask about different parts of its behavior.

### 2.5 Trace Semantics

Write `⟦t⟧` for the set of traces — finite sequences of deontic events `(subject, action, polarity)` — that a `TERMS` block `t` admits. The semantics follows the structure of the grammar directly:

```
⟦subject MUST action⟧                = { ⟨(subject, action, must)⟩ }
⟦subject MAY action WHEN c⟧          = { ⟨(subject, action, may)⟩ }        if eval(c), else ∅
⟦subject MUST_NOT action WHEN c⟧     = { ⟨(subject, action, must_not)⟩ }   if ¬eval(c), else ∅

⟦t1 THEN t2⟧   = { σ1++σ2 | σ1 ∈ ⟦t1⟧, σ2 ∈ ⟦t2⟧ }
⟦t1 AND t2⟧    = { interleave(σ1,σ2) | σ1 ∈ ⟦t1⟧, σ2 ∈ ⟦t2⟧ }
⟦t1 OR t2⟧     = ⟦t1⟧ ∪ ⟦t2⟧

⟦t1 UNLESS c DO t2⟧  = { σ ∈ ⟦t1⟧ | ¬eval(c) } ∪ { σ ∈ ⟦t2⟧ | eval(c) }
```

In every rule above, `eval(c)` is evaluated once, at the point the enclosing term is reached in the trace — the state available at that point in the specification's execution, not at some later or earlier point. This applies uniformly to `WHEN`-guarded permissions and prohibitions and to `UNLESS`'s guard: none of the language's guard constructs re-evaluate their condition mid-term.

A specification's `INVARIANTS` block is satisfied by a trace `σ` in the ordinary sense of LTL/CTL satisfaction over `σ`'s sequence of deontic events, with `ALWAYS`/`EVENTUALLY`/`NEXT` as the abbreviations `G`/`F`/`X` restricted to state-formula arguments (Section 2.4).

*(This semantics governs the surface language as published in the v2.4 grammar. It is stated here at the level of detail needed to support the claims of Section 5; a fully worked compilation-soundness proof is future work, tracked openly in the repository.)*

---

## 3. Related Work

TRIEL overlaps, in stated purpose, with several existing languages; the comparisons below are drawn at the level of publicly observable syntax and semantics, not implementation internals.

**OPA/Rego.** Rego is a mature declarative policy language evaluating rules against a snapshot of input data — a stateless, single-query evaluation model. TRIEL shares the goal of separating policy from the systems it governs, but adds trace semantics with native LTL/CTL operators and zero-knowledge field constraints, neither of which Rego's evaluation model addresses. This is a difference in scope, not a claim of superiority: Rego's runtime maturity and integration ecosystem for real-time authorization decisions is not something TRIEL, as a specification language without a released runtime, currently offers.

**Wysteria/Wys\*.** Wysteria-family languages express deontic-style obligations over distributed participants and compile toward secure multi-party computation protocols. TRIEL's deontic primitives are similar in spirit, but TRIEL is a specification language without a compilation target into any specific MPC protocol; its zero-knowledge constraints annotate individual fields rather than compiling an entire computation into a provable circuit.

**ZK-SecreC (Cybernetica).** ZK-SecreC is a full programming language for zero-knowledge proofs, with an information-flow type system distinguishing prover-private and shared data. TRIEL is not a programming language in this sense: its zero-knowledge constraints are restricted to predicates over a single field (range, set membership, hash equality against a literal), not general circuit logic. Where a specification needs to relate a ZK-constrained field to other specification state, that relationship is expressed as an ordinary temporal invariant, not as an extension of the zero-knowledge constraint syntax itself (Section 2.3).

**Allium (JUXT).** Allium is a behavioral specification language explicitly designed to be authored and maintained by an LLM on the user's behalf, embedded in a host-language (Clojure) ecosystem. TRIEL specifications are authored directly, independent of any host language, and are defined by a standalone grammar rather than a hosted DSL. The similarity is one of motivation — both aim to give durable, structured form to behavioral intent — rather than of mechanism.

**ZoKrates / Noir.** These are zero-knowledge circuit-writing languages: their job is to compile an entire program into a zkSNARK circuit. TRIEL does not compile programs into circuits; its ZK constraints express a provability predicate on a specification-level field, one order of abstraction above circuit design. A specification requiring genuinely novel circuit logic beyond range/set/hash predicates is better served by ZoKrates, Noir, or ZK-SecreC directly; TRIEL's zero-knowledge constraints are deliberately narrow so that the specification author is not required to reason about circuit design at all.

---

## 4. Scope of Claims

Consistent with the discipline this report holds itself to: TRIEL's grammar and semantics establish what a specification *says* and what traces satisfy it. This report does not claim that a TRIEL specification, once written, is automatically enforced by any particular runtime, nor that translating a natural-language requirement into TRIEL is itself a mechanical or unambiguous process — that translation remains a specification-authoring task requiring human judgment, same as writing any formal specification.

What is mechanically checkable today, and what is not, can be stated precisely rather than left as a general disclaimer: a TRIEL specification's well-formedness — type-correctness of its factors, and structural non-contradiction of its deontic terms (Section 1.1) — can be checked mechanically by a grammar-conformant parser. Whether a given implementation's execution trace satisfies a specification's temporal invariants is *defined* by the semantics of Section 2.5, but verifying that satisfaction against a released model-checking tool is not yet available; this is stated explicitly as future work, tracked openly in the repository, rather than implied to already exist.

---

*Draft v0.1 — all grammar excerpts verified against `github.com/triel-lang/grammar`, tag v2.4.*
