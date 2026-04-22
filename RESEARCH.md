# Constraint-Based Limits of Bounded Sequential Systems

**A three-paper research program by Shawn Kevin Jason on the structural limits of bounded local evaluation in sequential systems.**

ORCID: [0009-0003-9208-1556](https://orcid.org/0009-0003-9208-1556)

---

## The Question

This project studies a single question across three papers:

> **What can a bounded system guarantee about a full trajectory when it only acts on a limited representation of that trajectory?**

The answer is developed in stages:

1. **[Projection Insufficiency and Trajectory Realization](https://doi.org/10.5281/zenodo.19633241)** establishes the general projection-theoretic obstruction.
2. **[The Non-Locality of Extendability](https://doi.org/10.5281/zenodo.19688367)** specializes that obstruction to forward-local sequential systems.
3. **[Inconsistency Accumulation in Forward-Local Sequential Policies](https://doi.org/10.5281/zenodo.19688628)** shows how these failures can accumulate and identifies the representational escape condition.

Taken together, the papers argue that bounded local evaluation cannot, in general, guarantee globally extendable or globally consistent trajectory construction when the relevant constraints are non-local.

---

## Core Claim

> **Bounded local evaluation cannot, in general, guarantee globally extendable or globally consistent trajectory construction when the relevant constraints are non-local.**

---

## Start Here — Recommended Reading Order

### 1. Projection Insufficiency and Trajectory Realization

**Role: Foundational theorem.**

This paper establishes the general result: when a representation is non-injective on the distinctions that matter, a trajectory-dependent property cannot, in general, be recovered from that representation alone.

It introduces the broad projection-theoretic framework and shows how the same structural obstruction appears across lossy reconstruction, future extendability, and sequential admissibility.

*Read first if you want the full theoretical foundation.*

- **Paper (concept DOI, always resolves to latest):** [10.5281/zenodo.19633241](https://doi.org/10.5281/zenodo.19633241)
- **Lean 4 formalization:** [10.5281/zenodo.19687629](https://doi.org/10.5281/zenodo.19687629)
- **Repository:** [github.com/shawnjason/Projection-Insufficiency](https://github.com/shawnjason/Projection-Insufficiency)

---

### 2. The Non-Locality of Extendability

**Role: Forward-local impossibility theorem.**

This paper specializes the general obstruction to generative sequential systems such as planning, reinforcement learning, and language generation.

Its central result is the **Non-Observability of Extendability (NEO)** theorem: for every finite horizon, there exist environments in which no function of the bounded horizon projection can determine whether a globally consistent continuation remains available.

It isolates the key failure mode of **non-extendable commitment**: a locally acceptable move can destroy all globally consistent completions before any local signal reveals the problem.

*Read second if you want the direct impossibility result for forward-local systems.*

- **Paper (concept DOI):** [10.5281/zenodo.19688367](https://doi.org/10.5281/zenodo.19688367)
- **Lean 4 formalization:** [10.5281/zenodo.19687799](https://doi.org/10.5281/zenodo.19687799)
- **Repository:** [github.com/shawnjason/Non-Locality](https://github.com/shawnjason/Non-Locality)

---

### 3. Inconsistency Accumulation in Forward-Local Sequential Policies

**Role: Accumulative consequence and architectural separation.**

This paper strengthens the one-shot impossibility into an accumulation result.

It shows that under delayed constraints, non-extendable commitments do not merely occur in isolated cases: in the worst case, they accumulate without any policy-independent finite bound for forward-local policy classes.

It also establishes the positive side: when an environment family admits a sequentially updatable **extendability-preserving summary state**, zero accumulated inconsistency is achievable.

*Read third if you want the architectural consequence and the positive escape condition.*

- **Paper (concept DOI):** [10.5281/zenodo.19688628](https://doi.org/10.5281/zenodo.19688628)
- **Lean 4 formalization:** [10.5281/zenodo.19687094](https://doi.org/10.5281/zenodo.19687094)
- **Repository:** [github.com/shawnjason/Inconsistency-Accumulation](https://github.com/shawnjason/Inconsistency-Accumulation)

---

## How the Three Papers Fit Together

These papers are connected, but they are not redundant.

| Paper | Role | Central Contribution |
|---|---|---|
| **1. Projection Insufficiency** | Foundational theorem | General projection-theoretic obstruction |
| **2. Non-Locality of Extendability** | Forward-local specialization | NEO impossibility theorem |
| **3. Inconsistency Accumulation** | Accumulative consequence | Accumulation bound + summary-state escape |

The progression moves:

> general projection obstruction → forward-local extendability obstruction → accumulation result and representational escape condition

---

## What This Work Does *Not* Claim

This program does **not** claim that:

- Bounded local systems never succeed.
- Scaling is useless.
- All constraint classes are equally hard.
- Every failure in planning, RL, and language generation is identical in detail.
- Current AI systems across domains are literally the same object.

The claim is narrower and structural:

> When global validity depends on information outside the operative local representation, no method defined only on that bounded local representation can provide a uniform guarantee in general.

---

## Why This Matters

Many modern AI systems operate through local-sequential construction: token by token, action by action, step by step.

That pattern works well in many settings. But when correctness depends on a whole trajectory rather than a bounded local slice, local success and global success can come apart structurally.

This matters for:

- **Hallucination and contradiction** in language generation
- **Dead-end states** in planning
- **Absorbing failure states** in reinforcement learning
- Any bounded sequential system operating under non-local constraints

The aim of this project is not merely to describe these failures, but to identify the common structural reason they arise and to clarify what kind of representational change is required to move beyond them.

---

## Formal Verification

Every load-bearing theorem in this program has a machine-checked Lean 4 proof, independently verifiable through the Lean 4 web editor at [live.lean-lang.org](https://live.lean-lang.org) against current Mathlib. Each companion repository's README includes a mapping from paper results to Lean files and verification instructions.

The stochastic measure-theoretic main theorem of Paper 3 is verified through **two architecturally independent proof paths** — one via fiber-partitioning, one via canonical product isomorphism — providing redundant certification of the central probabilistic result.

---

## Citation Summary

### Papers

| Paper | Concept DOI |
|---|---|
| Projection Insufficiency and Trajectory Realization | [10.5281/zenodo.19633241](https://doi.org/10.5281/zenodo.19633241) |
| The Non-Locality of Extendability | [10.5281/zenodo.19688367](https://doi.org/10.5281/zenodo.19688367) |
| Inconsistency Accumulation in Forward-Local Sequential Policies | [10.5281/zenodo.19688628](https://doi.org/10.5281/zenodo.19688628) |

### Lean 4 Formalizations

| Repository | Concept DOI |
|---|---|
| [Projection-Insufficiency](https://github.com/shawnjason/Projection-Insufficiency) | [10.5281/zenodo.19687629](https://doi.org/10.5281/zenodo.19687629) |
| [Non-Locality](https://github.com/shawnjason/Non-Locality) | [10.5281/zenodo.19687799](https://doi.org/10.5281/zenodo.19687799) |
| [Inconsistency-Accumulation](https://github.com/shawnjason/Inconsistency-Accumulation) | [10.5281/zenodo.19687094](https://doi.org/10.5281/zenodo.19687094) |

---

## Summary

This is a layered research program:

- **Paper 1** gives the theorem.
- **Paper 2** gives the forward-local impossibility.
- **Paper 3** gives the accumulative consequence and the representational escape.

That is the map.

---

## Author

**Shawn Kevin Jason** — Independent Researcher, Las Vegas, NV
ORCID: [0009-0003-9208-1556](https://orcid.org/0009-0003-9208-1556)

## License

Papers: CC-BY 4.0
Lean 4 formalizations: MIT
