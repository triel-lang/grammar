# Related Work

The comparison of TRIEL with related languages is in `TECHNICAL_REPORT.md` §3: OPA/Rego, Wysteria and Wys\*, ZK-SecreC, Allium, and ZoKrates and Noir. The semantic foundations of the language, and the results each construct rests on, are in `FOUNDATIONS.md`.

This file adds a related line of research on information release in secure multiparty computation (MPC).

**Declassification in MPC.** In practical MPC deployments, the logic that decides which data may be released is often hand-coded in a specific deployment. *Language-Based Security for Low-Level MPC* (Bogdanov et al., 2024) formalizes noninterference and declassification for low-level MPC code. TRIEL works at the level of the specification: conditions, obligations and deadlines are stated there, and the information-flow rule for zero-knowledge factors (`TECHNICAL_REPORT.md` §2.7) is checked on the specification itself. TRIEL does not define how such a specification is implemented.

## References

1. Rastogi, A., Hammer, M. A., & Hicks, M. (2014). *Wysteria: A Programming Language for Generic, Mixed-Mode Secure Multiparty Computation.* IEEE Symposium on Security and Privacy (S&P).
2. Rastogi, A., Swamy, N., & Hicks, M. (2019). *Wys\*: A DSL for Verified Secure Multi-Party Computations.*
3. Bogdanov, D., et al. (2024). *Language-Based Security for Low-Level MPC.* arXiv preprint arXiv:2407.16504.
4. Jagomägis, R. (2010). *SecreC: a privacy-aware programming language with applications in data mining.* Master's thesis, Institute of Computer Science, University of Tartu.
