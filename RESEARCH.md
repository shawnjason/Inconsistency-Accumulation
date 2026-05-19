# Constraint-Based Limits of Bounded Sequential Systems

**An eight-paper research program by Shawn Kevin Jason on the structural limits of bounded local evaluation in sequential systems.**

ORCID: [0009-0003-9208-1556](https://orcid.org/0009-0003-9208-1556)

---

## The Question

This program studies a single question across eight papers:

> **What can a bounded system guarantee about a full trajectory when it only acts on a limited representation of that trajectory?**

The answer is developed in three tiers — a foundational theoretical core, two domain specializations, and three empirical instruments — each reinforcing the same structural conclusion.

---

## Core Claim

> **Bounded local evaluation cannot, in general, guarantee globally extendable or globally consistent trajectory construction when the relevant constraints are non-local.**

---

## Program Architecture

The eight papers are organized into three tiers:

| Tier | Papers | Function |
|---|---|---|
| **Foundations** | PIT, NEO, IA | Theoretical core — establish the impossibility, the forward-case specialization, and the stochastic extension |
| **Specializations** | HAL, RLM | Domain-specific applications — language-model hallucination and recursive language model architectures |
| **Empirical** | OOL, SUD, HAM | Empirical instruments — pair construction, controlled microscope, cross-provider pilot |

The progression moves:

> general projection obstruction → forward-local impossibility → stochastic accumulation → language-model specialization → recursive-scaffolding architecture → empirical validation across three instruments

---

## Foundations

### 1. Projection Insufficiency and Trajectory Realization

**Role: Foundational theorem.**

This paper establishes the general result: when a representation is non-injective on the distinctions that matter, a trajectory-dependent property cannot, in general, be recovered from that representation alone.

It introduces the broad projection-theoretic framework and shows how the same structural obstruction appears across lossy reconstruction, future extendability, and sequential admissibility.

*Read first if you want the full theoretical foundation.*

- **Paper (concept DOI):** [10.5281/zenodo.19633241](https://doi.org/10.5281/zenodo.19633241)
- **Lean 4 formalization (concept DOI):** [10.5281/zenodo.19687628](https://doi.org/10.5281/zenodo.19687628)
- **Repository:** [github.com/shawnjason/Projection-Insufficiency](https://github.com/shawnjason/Projection-Insufficiency)

---

### 2. The Non-Locality of Extendability

**Role: Forward-local impossibility theorem.**

This paper specializes the general obstruction to generative sequential systems such as planning, reinforcement learning, and language generation.

Its central result is the **Non-Observability of Extendability (NEO)** theorem: for every finite horizon, there exist environments in which no function of the bounded horizon projection can determine whether a globally consistent continuation remains available.

It isolates the key failure mode of **non-extendable commitment**: a locally acceptable move can destroy all globally consistent completions before any local signal reveals the problem.

*Read second if you want the direct impossibility result for forward-local systems.*

- **Paper (concept DOI):** [10.5281/zenodo.19688367](https://doi.org/10.5281/zenodo.19688367)
- **Lean 4 formalization (concept DOI):** [10.5281/zenodo.19687798](https://doi.org/10.5281/zenodo.19687798)
- **Repository:** [github.com/shawnjason/Non-Locality](https://github.com/shawnjason/Non-Locality)

---

### 3. Inconsistency Accumulation in Forward-Local Sequential Policies

**Role: Stochastic extension and accumulation result.**

This paper strengthens the one-shot impossibility into an accumulation result and lifts it from deterministic to stochastic policies.

It shows that under delayed constraints, non-extendable commitments do not merely occur in isolated cases: in the worst case, they accumulate with a quantitative lower bound **E[I_N] ≥ N/|U|** that is uniform across the entire forward-local policy class.

It also establishes the positive side: when an environment family admits a sequentially updatable **extendability-preserving summary state**, zero accumulated inconsistency is achievable. This is the **admissibility-dynamics framework** on which the program's subsequent recursive-scaffolding and empirical-validation results build.

*Read third if you want the accumulation bound and the representational escape condition.*

- **Paper (concept DOI):** [10.5281/zenodo.19688628](https://doi.org/10.5281/zenodo.19688628)
- **Lean 4 formalization (concept DOI):** [10.5281/zenodo.19687093](https://doi.org/10.5281/zenodo.19687093)
- **Repository:** [github.com/shawnjason/Inconsistency-Accumulation](https://github.com/shawnjason/Inconsistency-Accumulation)

---

## Specializations

### 4. Language Model Hallucinations: An Impossibility Theorem and Its Architectural Consequences

**Role: Language-model specialization.**

This paper establishes hallucination as a structural failure class — **delayed constraint failure (DCF)** — necessarily arising in any bounded-context autoregressive generator. The impossibility is the language-model specialization of the NEO theorem: no function of the bounded context projection alone can determine whether the next token preserves global consistency under non-local constraints.

It then classifies common language-model mitigation strategies — retrieval augmentation, chain-of-thought prompting, grammar-constrained decoding, verifier-reranking, and process supervision — by the structural mechanism through which each acts on the forward-local obstruction, identifying which satisfy the constraint requirement and on which constraint sub-class.

The result identifies a structural failure mode that contributes to hallucination independently of training quality or model scale.

- **Paper (concept DOI):** [10.5281/zenodo.19715059](https://doi.org/10.5281/zenodo.19715059)
- **Lean 4 formalization (concept DOI):** [10.5281/zenodo.20059771](https://doi.org/10.5281/zenodo.20059771)
- **Repository:** [github.com/shawnjason/Hallucinations](https://github.com/shawnjason/Hallucinations)

---

### 5. Recursive Language Models Through the Admissibility-Dynamics Framework

**Role: Recursive-scaffolding architecture.**

This paper applies the admissibility-dynamics framework of Paper 3 to Recursive Language Models (RLMs), introduced by Zhang et al. as a long-context reasoning architecture that treats the input prompt as an external REPL environment and processes it through recursive sub-calls.

It establishes three structural results under a formal RLM execution model: a **sufficiency** theorem characterizing when the architecture satisfies the constraint requirement, an **insufficiency** theorem identifying constraint classes whose certification depth exceeds the architectural information bound, and an **accumulation** theorem inheriting the N/|U| lower bound from Paper 3.

These results recover Zhang et al.'s reported performance pattern as structural consequences, position their six baselines within a mitigation taxonomy, and generate thirteen novel predictions — three testable against existing data, ten requiring new benchmarks.

- **Paper (concept DOI):** [10.5281/zenodo.19753549](https://doi.org/10.5281/zenodo.19753549)
- **Lean 4 formalization (concept DOI):** [10.5281/zenodo.20060154](https://doi.org/10.5281/zenodo.20060154)
- **Repository:** [github.com/shawnjason/Recursive-Language](https://github.com/shawnjason/Recursive-Language)

---

## Empirical

### 6. From Recursive Scaffolding to Admissibility-First Construction (OOLONG-Pairs)

**Role: RLM empirical companion.**

This paper empirically tests the predictions of Paper 5 on a Zhang-style OOLONG-Pairs setting. It decomposes recursive scaffolding into its mechanism components — filter-mode GAF, construction-mode GAF, and the admissibility-relevant summary state — and shows that the essential mechanism is not recursion itself but the construction or approximation of an admissibility-relevant state.

Key empirical results: RLM(GPT-5) recovers from a 0.1% F1 baseline to 0.9064 micro-F1; model-based admissibility-first construction without RLM achieves 0.9212 micro-F1 with different precision-recall trade-offs; and on the seed-7702 robustness probe, RLM suffers a catastrophic recall collapse (0.1379 micro-F1) while construction-mode GAF remains stable across seeds.

The result separates filter-mode GAF (recall-bounded by the candidate set) from construction-mode GAF (robust to candidate-generation failure), and isolates the admissibility-relevant summary state as the underlying mechanism that both RLM and direct admissibility classifiers approximate.

- **Paper (concept DOI):** [10.5281/zenodo.20277804](https://doi.org/10.5281/zenodo.20277804)
- **Lean 4 formalization (concept DOI):** [10.5281/zenodo.20062396](https://doi.org/10.5281/zenodo.20062396)
- **Repository:** [github.com/shawnjason/OOLONG-Pairs](https://github.com/shawnjason/OOLONG-Pairs)

---

### 7. Commitment Failure Under Local Decision-Making in AI Systems: The Sudoku Microscope

**Role: Controlled empirical validation of GAF.**

This paper validates the global admissibility filtering (GAF) framework using Sudoku as a controlled constraint microscope — not as a Sudoku-solving benchmark, but as a controlled domain in which valid next steps, admissible completions, and catastrophic commitments can be separated and measured exactly.

It compares three decision regimes — no admissibility tools, optional admissibility tools, and mandatory pre-commit admissibility gating — across both synthetic and real-model conditions. Across all 36 seeded runs in the synthetic exact-counter suite, local-only and ungated optional-tool policies fail catastrophically; admissibility-conditioned policies solve 12/12 rows and reject 131 zero-completion candidates before commitment. The real-model ladder with GPT-5.5 shows the same structural separation: 0/12 solving under no-tool, 7/12 under optional-tool, 12/12 under forced-gate.

The result is a **costed safety separation**: tool availability is not equivalent to safety, and valid-looking next-step choice is not equivalent to safe completion. Catastrophic commitments disappear only when admissibility evidence is made a mandatory precondition for commitment.

- **Paper (concept DOI):** [10.5281/zenodo.20277939](https://doi.org/10.5281/zenodo.20277939)
- **Lean 4 formalization (concept DOI):** [10.5281/zenodo.20072388](https://doi.org/10.5281/zenodo.20072388)
- **Repository:** [github.com/shawnjason/Sudoku-Microscope](https://github.com/shawnjason/Sudoku-Microscope)

---

### 8. Minimal Topologies of Forward-Local Failure in AI Systems: The Hamiltonian Microscope

**Role: Cross-provider pilot.**

This paper extends the Sudoku Microscope methodology to a structurally distinct problem class — the 4×4 Hamiltonian-path traversal task — providing a second independent lens on forward-local commitment failure across two frontier providers.

The central architectural finding unifies both providers: across **all 195 catastrophic commitments** observed in the cross-provider corpus (GPT-5.5 and Claude Opus 4.7), the model committed the failing move without having acquired positive admissibility evidence for the committed move tuple — the **Layer 2 silent-commit signature**, satisfied 195/195. Under forced admissibility verification, both models reliably solve the canonical instance: 50/50 for GPT-5.5 and 15/15 across all Claude batches.

The paper is positioned as a custom-domain pilot and mechanism-discovery study, not a comprehensive cross-provider benchmark.

- **Paper (concept DOI):** [10.5281/zenodo.20278073](https://doi.org/10.5281/zenodo.20278073)
- **Lean 4 formalization (concept DOI):** [10.5281/zenodo.20073715](https://doi.org/10.5281/zenodo.20073715)
- **Repository:** [github.com/shawnjason/Hamiltonian-Microscope](https://github.com/shawnjason/Hamiltonian-Microscope)

---

## How the Eight Papers Fit Together

| Paper | Tier | Role | Central Contribution |
|---|---|---|---|
| **1. Projection Insufficiency** | Foundations | Foundational theorem | General projection-theoretic obstruction |
| **2. Non-Locality of Extendability** | Foundations | Forward-local specialization | NEO impossibility theorem |
| **3. Inconsistency Accumulation** | Foundations | Stochastic extension | Accumulation bound + summary-state escape |
| **4. Language Model Hallucinations** | Specializations | LM specialization | Hallucination as DCF + mitigation taxonomy |
| **5. Recursive Language Models** | Specializations | RLM architecture | Three-theorem RLM analysis + thirteen predictions |
| **6. OOLONG-Pairs** | Empirical | RLM empirical companion | Mechanism decomposition of recursive scaffolding |
| **7. Sudoku Microscope** | Empirical | Controlled validation | Costed safety separation |
| **8. Hamiltonian Microscope** | Empirical | Cross-provider pilot | Layer 2 silent-commit signature (195/195) |

The Foundations tier establishes the theoretical core. The Specializations tier applies that core to two specific architectural patterns — bounded-context language models and recursive-scaffolding language models. The Empirical tier instruments the framework's predictions through three independent measurement designs.

---

## What This Work Does *Not* Claim

This program does **not** claim that:

- Bounded local systems never succeed.
- Scaling is useless.
- All constraint classes are equally hard.
- Every failure in planning, RL, and language generation is identical in detail.
- Current AI systems across domains are literally the same object.
- Recursive scaffolding doesn't help — it does, in favorable cases, by approximating an admissibility-relevant summary state.

The claim is narrower and structural:

> When global validity depends on information outside the operative local representation, no method defined only on that bounded local representation can provide a uniform guarantee in general.

---

## Why This Matters

Many modern AI systems operate through local-sequential construction: token by token, action by action, step by step.

That pattern works well in many settings. But when correctness depends on a whole trajectory rather than a bounded local slice, local success and global success can come apart structurally.

This matters for:

- **Hallucination and contradiction** in language generation (treated formally in Paper 4)
- **Dead-end states** in planning (treated formally in Paper 1, Section 9.2)
- **Absorbing failure states** in reinforcement learning (treated formally in Paper 1, Section 9.3)
- **Recursive-scaffolding architectures** for long-context reasoning (treated formally in Paper 5, empirically in Paper 6)
- Any bounded sequential system operating under non-local constraints

The aim of this program is not merely to describe these failures, but to identify the common structural reason they arise, clarify what kind of representational change is required to move beyond them, and provide empirical instruments that can detect the failure mode in controlled domains.

---

## Formal Verification

Every load-bearing theorem in this program has a machine-checked Lean 4 proof, independently verifiable through the Lean 4 web editor at [live.lean-lang.org](https://live.lean-lang.org) against current Mathlib. Each companion repository's README includes a mapping from paper results to Lean files and verification instructions.

Two technical features of the formalization deserve mention:

- The stochastic measure-theoretic main theorem of Paper 3 is verified through **two architecturally independent proof paths** — one via fiber-partitioning with an explicit coordinate-update bijection, one via canonical product isomorphism using `Fin.insertNthEquiv` — providing redundant certification of the central probabilistic result.
- Paper 7 introduces an abstract **`ConstraintSystem` framework** in Lean 4 that Paper 8 instantiates for Hamiltonian path-games, allowing the four Sudoku Microscope structural theorems (local-global separation, catastrophic-commitment foreclosure, forced-gate safety, bucket sufficiency) to apply to path-games by inheritance without redundant proof.

---

## Citation Summary

### Papers (concept DOIs — always resolve to latest version)

| Tier | Paper | Concept DOI |
|---|---|---|
| Foundations | Projection Insufficiency and Trajectory Realization | [10.5281/zenodo.19633241](https://doi.org/10.5281/zenodo.19633241) |
| Foundations | The Non-Locality of Extendability | [10.5281/zenodo.19688367](https://doi.org/10.5281/zenodo.19688367) |
| Foundations | Inconsistency Accumulation in Forward-Local Sequential Policies | [10.5281/zenodo.19688628](https://doi.org/10.5281/zenodo.19688628) |
| Specializations | Language Model Hallucinations | [10.5281/zenodo.19715059](https://doi.org/10.5281/zenodo.19715059) |
| Specializations | Recursive Language Models Through the Admissibility-Dynamics Framework | [10.5281/zenodo.19753549](https://doi.org/10.5281/zenodo.19753549) |
| Empirical | From Recursive Scaffolding to Admissibility-First Construction (OOLONG-Pairs) | [10.5281/zenodo.20277804](https://doi.org/10.5281/zenodo.20277804) |
| Empirical | Commitment Failure Under Local Decision-Making (Sudoku Microscope) | [10.5281/zenodo.20277939](https://doi.org/10.5281/zenodo.20277939) |
| Empirical | Minimal Topologies of Forward-Local Failure (Hamiltonian Microscope) | [10.5281/zenodo.20278073](https://doi.org/10.5281/zenodo.20278073) |

### Lean 4 Formalizations (concept DOIs)

| Repository | Concept DOI |
|---|---|
| [Projection-Insufficiency](https://github.com/shawnjason/Projection-Insufficiency) | [10.5281/zenodo.19687628](https://doi.org/10.5281/zenodo.19687628) |
| [Non-Locality](https://github.com/shawnjason/Non-Locality) | [10.5281/zenodo.19687798](https://doi.org/10.5281/zenodo.19687798) |
| [Inconsistency-Accumulation](https://github.com/shawnjason/Inconsistency-Accumulation) | [10.5281/zenodo.19687093](https://doi.org/10.5281/zenodo.19687093) |
| [Hallucinations](https://github.com/shawnjason/Hallucinations) | [10.5281/zenodo.20059771](https://doi.org/10.5281/zenodo.20059771) |
| [Recursive-Language](https://github.com/shawnjason/Recursive-Language) | [10.5281/zenodo.20060154](https://doi.org/10.5281/zenodo.20060154) |
| [OOLONG-Pairs](https://github.com/shawnjason/OOLONG-Pairs) | [10.5281/zenodo.20062396](https://doi.org/10.5281/zenodo.20062396) |
| [Sudoku-Microscope](https://github.com/shawnjason/Sudoku-Microscope) | [10.5281/zenodo.20072388](https://doi.org/10.5281/zenodo.20072388) |
| [Hamiltonian-Microscope](https://github.com/shawnjason/Hamiltonian-Microscope) | [10.5281/zenodo.20073715](https://doi.org/10.5281/zenodo.20073715) |

---

## Summary

This is a tiered research program:

- **Foundations (Papers 1–3)** give the theorem, the forward-local impossibility, and the stochastic accumulation result with summary-state escape.
- **Specializations (Papers 4–5)** apply the framework to language-model hallucination and recursive language model architectures.
- **Empirical (Papers 6–8)** instrument the framework's predictions through pair construction, controlled microscope, and cross-provider pilot.

That is the map.

---

## Author

**Shawn Kevin Jason** — Independent Researcher, Las Vegas, NV
ORCID: [0009-0003-9208-1556](https://orcid.org/0009-0003-9208-1556)

## License

Papers: CC-BY 4.0
Lean 4 formalizations: MIT
