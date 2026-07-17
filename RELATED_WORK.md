# Related Work & Architectural Positioning

The design intent of TRIEL is to treat specification-to-implementation translation as the explicit point where correctness evidence should be generated. This document outlines how TRIEL's architectural goals position it relative to existing infrastructure policy engines, domain-specific languages (DSLs) for secure computation, and formal declassification frameworks.

## 1. TRIEL vs. Infrastructure Policy Languages (OPA / Rego)

Modern compliance and access control often rely on declarative policy engines like **Open Policy Agent (OPA)** and its query language, **Rego**.

* **The Existing Paradigm:** OPA excels at infrastructure-level decision-making (e.g., Kubernetes admission control, API gateways, and CI/CD pipelines). It operates as a perimeter gateway, evaluating structured JSON queries *before* a process is executed or auditing logs *after* the fact.
* **The TRIEL Alignment & Distinction:** OPA and Rego are fundamentally decoupled from the cryptographic primitives execution layer. They cannot inspect or enforce compliance logic *within* a secure multiparty computation (MPC) circuit or a zero-knowledge proof (ZKP) pipeline. TRIEL **aims to express compliance constraints directly at the data-field level**, allowing these rules to be woven into the compiled cryptographic downstream artifacts rather than acting as an external, trusted gatekeeper.

## 2. TRIEL vs. Cryptographic Domain-Specific Languages (Wysteria / Wys*)

There is a rich academic history of developing programming languages specifically for secure multiparty computation (SMC) and verified execution.

* **Wysteria (Rastogi, Hammer, Hicks; IEEE S&P 2014):** Introduced a language for mixed-mode SMC that compiles into cryptographic circuits while supporting multiple distinct security principals.
* **Wys\* (Rastogi, Swamy, Hicks; 2019):** Advanced this concept into a DSL for *verified* secure multi-party computations using dependent and refinement types.
* **The TRIEL Alignment & Distinction:** Languages like Wysteria and Wys\* are engineered *by* cryptographers *for* developers writing cryptographic logic. They require explicit understanding of type theory, security domain splits, and low-level protocol orchestration.

  TRIEL is designed not as a low-level cryptographic programming language, but as a **human-readable specification language**. The goal of TRIEL is to allow non-cryptographers (e.g., compliance officers, business analysts) to audit and write declarative invariants. The architecture intends to abstract the complexities of principal-splitting, targeting these lower-level DSLs or execution circuits during the compilation phase.

## 3. Language-Based Security & Declassification Policies

A major challenge in MPC systems handling sensitive aggregation (such as institutional or financial data) is defining *what* information can be safely revealed and *under what conditions* (the declassification policy).

* **The Existing Paradigm:** In practical MPC deployments, the eligibility or compliance logic dictating data release is frequently hand-coded inside the "ideal functionality" of a specific deployment. Recent research, such as *Language-Based Security for Low-Level MPC* (Bogdanov et al., 2024), formalizes noninterference and declassification for low-level MPC code, but this remains bound to the implementation layer.
* **The TRIEL Alignment & Distinction:** TRIEL seeks to shift declassification and liveness policies (such as conditional obligations and bounded deadlines via the `WITHIN` syntax) up into the authoritative specification layer. By doing so, the language aims to make compliance logic explicitly scannable and verifiable before any underlying cryptographic circuits are generated.

---

## References

1. **Rastogi, A., Hammer, M. A., & Hicks, M. (2014).** *Wysteria: A Programming Language for Generic, Mixed-Mode Secure Multiparty Computation.* In IEEE Symposium on Security and Privacy (S&P).
2. **Rastogi, A., Swamy, N., & Hicks, M. (2019).** *Wys\*: A DSL for Verified Secure Multi-Party Computations.*
3. **Bogdanov, D., et al. (2024).** *Language-Based Security for Low-Level MPC.* arXiv preprint arXiv:2407.16504.
4. **Jagomägis, R. (2010).** *SecreC: a privacy-aware programming language with applications in data mining.* Master's thesis, Institute of Computer Science, University of Tartu.
