# Inconsistency Accumulation — Lean Proofs

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.19687094.svg)](https://doi.org/10.5281/zenodo.19687094)

Machine-checked Lean 4 proofs for:

**"Inconsistency Accumulation in Forward-Local Sequential Policies: A Lower Bound under Delayed Constraints"**

Paper DOI (concept, always resolves to latest): [10.5281/zenodo.19688628](https://doi.org/10.5281/zenodo.19688628)

---

## Author

Shawn Kevin Jason — Independent Researcher, Las Vegas, NV
ORCID: [![ORCID iD](https://orcid.org/sites/default/files/images/orcid_16x16.png)](https://orcid.org/0009-0003-9208-1556) [0009-0003-9208-1556](https://orcid.org/0009-0003-9208-1556)

---

## What This Repository Contains

Thirteen standalone Lean 4 proof files covering the principal formal results of the paper. The proofs split into four groups: an **arithmetic witness core** that mechanically verifies the specific sum-based witness family used in Section 7; a **policy-level group** that formalizes the paper's main lemmas, both clauses of the main theorem in finite-combinatorial form, and the randomization class-closure corollary of Theorem 1(ii); a **measure-theoretic integration group** that constructs the trajectory probability space and proves the main integration theorem in its full measure-theoretic form — verified twice, via two architecturally distinct proof paths; and a **summary sufficiency group** that establishes Proposition 1 together with its non-vacuity witness and its representation/computation separation companion.

Each file is independent and verifies against the current Mathlib release.

---

## Dual-Path Measure-Theoretic Verification

The paper's load-bearing product-measure independence identity — the core fact underlying the tower-property argument of §5 — is verified twice in this repository through entirely different Mathlib infrastructure. Either file compiles in isolation; neither depends on the other. The shared conclusion is therefore certified through two independent machine-checked proofs.

**`079a_accumulation_stochastic_measure_pathA.lean`** — Path A verifies the identity via fiber-partitioning with an explicit coordinate-update bijection. Uses `Finset.sum_fiberwise`, `Function.update`, and `Finset.sum_bij` with a per-fiber invariance argument.

**`079b_accumulation_stochastic_measure_pathB.lean`** — Path B verifies the identity via the canonical product isomorphism. Uses Mathlib's `Fin.insertNthEquiv`, `Fintype.sum_prod_type`, and `Fin.prod_univ_succAbove` to establish the Fubini-style factorization on the discrete product space.

Both files prove the same main theorem `accumulation_stochastic_measure` with identical signatures. A reviewer can compile either file independently to verify the full measure-theoretic formalization.

---

## Files

### Arithmetic Witness Core (Section 7)

**`031_extendability_indistinguishability.lean`** — Section 7 arithmetic witness (extendability)
Concrete arithmetic witness for Section 7: two prefix sums agree on the bounded projection but differ in extendability. Specifically, prefix sum 7 extends to target 7, while prefix sum 8 does not.

**`036_horizon_nonconvergence.lean`** — Section 7 arithmetic witness (horizon non-convergence)
For every horizon `h`, a separating pair exists at depth `h+1`: two states with identical bounded projections that differ in extendability. No finite evaluation horizon eliminates the failure class.

**`046_forced_inconsistency.lean`** — Section 7 arithmetic witness (forced inconsistency)
Arithmetic core of the forced inconsistency construction underlying the witness family: once the prefix sum exceeds the target, no completion can reach the target. The companion result formalizes that if the prefix sum equals the target, a zero-length completion suffices.

### Policy-Level Results

**`060_forward_local_indistinguishability.lean`** — Lemma 1
A forward-local policy cannot condition its action on any distinction that is not present in its bounded local window. Formalized via a `ForwardLocalPolicy` abbreviation (a function of the trailing observation window) and proved near-definitionally.

**`061_single_block_failure.lean`** — Lemma 2 (deterministic)
For every forward-local policy, there exists a policy-indexed delayed-violation block in which the policy commits non-extendably. Formalized via a `DelayedBlock` structure with explicit admissibility and non-admissibility witnesses; the construction admits exactly those actions distinct from the policy's choice at the target window.

**`062a_accumulation_deterministic.lean`** — Theorem 1 (deterministic clause)
For every forward-local policy, every window, and every `N`, there exists an `N`-block environment in which every block forces a non-extendable commitment. The cumulative inconsistency counter satisfies `I_N = N` exactly. Constructed as `List.replicate` of the Lemma 2 policy-indexed block.

**`062b_accumulation_stochastic.lean`** — Theorem 1 (stochastic clause, finite-combinatorial form)
For every stochastic forward-local policy with `|U| ≥ 2` and every `N`, there exists an `N`-block environment in which the expected cumulative inconsistency satisfies `E[I_N] ≥ N/|U|`. The Lean formalization delivers the uniform policy-independent bound `1/|U|` via a pigeonhole-on-probabilities argument and finite-sum linearity, so no measure-theoretic infrastructure is required.

**`064_randomization_preserves_accumulation_floor.lean`** — Theorem 1(ii) corollary (randomization class-closure)
Class-closure consequence of the stochastic clause: the uniform lower bound `E[I_N] ≥ N/|U|` survives any within-class transformation. The file proves both directions — that randomization preserves the accumulation floor (`randomization_preserves_accumulation_floor`), and that no randomization scheme can break it (`no_randomization_breaks_floor`) — formalized via an `AccumulationFloor` predicate over policy classes and a `RandomizationScheme` definition that captures within-class re-mixing.

### Measure-Theoretic Integration (Two Independent Proofs)

**`079a_accumulation_stochastic_measure_pathA.lean`** — Theorem 1 (stochastic clause, full measure-theoretic form, Path A)
The full measure-theoretic integration theorem via fiber-partitioning. Constructs the trajectory probability space as the `N`-fold product of the policy's action distribution on the finite action space `U`; constructs the filtration `F_k` as the σ-algebra generated by the first `k` coordinate projections; defines the per-block failure indicators `X_k` with measurability and integrability; proves the **bridge lemma** that the conditional expectation `μ[X_k | F_k]` is almost-surely bounded below by `1/|U|` via `MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq`; and proves the main integration theorem `E_μ[I_N] ≥ N/|U|` via the tower property and linearity of expectation. The product-measure independence identity `setIntegral_X_eq_of_determined` is closed by partitioning the sum via `Finset.sum_fiberwise`, factoring at the adversarial action, and using an explicit coordinate-`k` update bijection (`Function.update`) together with `π.sums_to_one`. The bridge from `F_k`-measurability to the determined-by-prefix property (`F_measurable_determined`) is closed by σ-algebra induction on the generating cylinders using `MeasurableSpace.induction_on`. Zero `sorry`.

**`079b_accumulation_stochastic_measure_pathB.lean`** — Theorem 1 (stochastic clause, full measure-theoretic form, Path B)
The same measure-theoretic integration theorem via the canonical product-isomorphism factorization. All shared infrastructure from Path A is included verbatim (trajectory space construction, filtration, measurability, integrability, `F_measurable_determined`); the load-bearing product-measure identity `setIntegral_X_eq_of_determined_via_equiv` is proved independently using `Fin.insertNthEquiv` to establish the product equivalence `(Fin (N+1) → U) ≃ U × (Fin N → U)`, then `Fintype.sum_prod_type` to split the Cartesian sum into nested sums, `Fin.prod_univ_succAbove` to factor the trajectory-measure product at position `k`, and `π.sums_to_one` to close. The main theorem wrapper `setIntegral_X_eq` dispatches from the standard `Fin N` interface to the `Fin (M+1)` implementation via a case-split on `N`. Zero `sorry`.

### Summary Sufficiency (Section 6)

**`067_summary_sufficiency.lean`** — Proposition 1 (both clauses)
Given an `AdmissibilityOracle` satisfying the extendability-preservation axioms (initial-admits, successor-admits), both clauses of Proposition 1 are formalized: first, a summary-safe trajectory contains no non-admissible commitment; second, a summary-safe trajectory of any length exists, with the inductive step invoking the successor-admits axiom.

**`069_full_prefix_summary_exists.lean`** — Remark 2 (non-vacuity of Proposition 1)
Companion to Proposition 1 establishing that the result is genuinely positive rather than vacuous: in the finite-horizon, finite-action setting where extendability is decidable, the full prefix itself is an extendability-preserving summary. The identity map `S = Prefix` together with the `ExtendabilityPreservingSummary` structure witnesses that some such summary always exists.

**`070_representation_computation_separation.lean`** — Remark 3 (representation/computation separation)
Quantitative form of Remark 3: the architectural separation of Proposition 1 is representation-theoretic, not computational. Three theorems together establish the separation — that the full-prefix summary size (`fullPrefixSize`) grows unboundedly with trajectory length, that it lies outside every finite size class, and that informational existence of an extendability-preserving summary does not bound the representation size of any specific instance.

---

## Mapping to the Paper

| Paper Result | File | Lean Theorem |
|---|---|---|
| Lemma 1 | `060_forward_local_indistinguishability.lean` | `forward_local_indistinguishability` |
| Lemma 2 | `061_single_block_failure.lean` | `single_block_failure_det` |
| Theorem 1 (deterministic clause) | `062a_accumulation_deterministic.lean` | `accumulation_deterministic` |
| Theorem 1 (stochastic, finite-combinatorial form) | `062b_accumulation_stochastic.lean` | `accumulation_stochastic` |
| Theorem 1(ii) corollary (randomization class-closure) | `064_randomization_preserves_accumulation_floor.lean` | `randomization_preserves_accumulation_floor`, `no_randomization_breaks_floor` |
| Theorem 1 (stochastic, measure-theoretic Path A) | `079a_accumulation_stochastic_measure_pathA.lean` | `accumulation_stochastic_measure` |
| Theorem 1 (stochastic, measure-theoretic Path B) | `079b_accumulation_stochastic_measure_pathB.lean` | `accumulation_stochastic_measure` |
| Proposition 1 (both clauses) | `067_summary_sufficiency.lean` | `summary_safe_zero_inconsistency`, `summary_safe_trajectory_exists` |
| Remark 2 (non-vacuity of Proposition 1) | `069_full_prefix_summary_exists.lean` | `full_prefix_summary_exists` |
| Remark 3 (representation/computation separation) | `070_representation_computation_separation.lean` | `full_prefix_size_unbounded`, `full_prefix_outside_finite_size_class`, `representation_existence_not_bounded` |
| Section 7 arithmetic witness (extendability) | `031_extendability_indistinguishability.lean` | `extendability_indistinguishability` |
| Section 7 arithmetic witness (horizon non-convergence) | `036_horizon_nonconvergence.lean` | `horizon_nonconvergence` |
| Section 7 arithmetic witness (forced inconsistency) | `046_forced_inconsistency.lean` | `forced_inconsistency`, `admissible_action_preserved` |

---

## How to Verify

1. Open [live.lean-lang.org](https://live.lean-lang.org)
2. Confirm the dropdown in the upper right is set to **Latest Mathlib**
3. Paste the contents of any `.lean` file into the editor
4. Wait for checking to complete — "No goals" on each theorem and no errors in the Problems pane confirms verification

Each file is independent; no cross-file imports are required. In particular, `079a_accumulation_stochastic_measure_pathA.lean` and `079b_accumulation_stochastic_measure_pathB.lean` each provide a complete, self-contained proof of the measure-theoretic main theorem — a reviewer wishing to verify the stochastic clause may compile either file alone.

---

## Scope

These proofs establish the full formal skeleton of the paper's principal results, including: both clauses of Theorem 1 in both finite-combinatorial and full measure-theoretic forms, with the measure-theoretic form verified through two independent proof paths; the randomization class-closure corollary of Theorem 1(ii); and Proposition 1 (Summary Sufficiency) together with its non-vacuity witness and its representation/computation separation companion. They do not establish:

- The empirical corroboration of Section 8 (simulation results), which is reported separately
- The application to bounded-context language models (Section 9.2), which is motivational rather than formal

Both measure-theoretic files (`pathA` and `pathB`) are complete end to end, with no `sorry` remaining. The stochastic clause of Theorem 1 is proved in Lean with a uniform bound `E[I_N] ≥ N/|U|`, which is strictly stronger than the original `E[I_N] ≥ p_π · N` form in earlier drafts of the paper: the constant `1/|U|` is uniform across all stochastic policies and depends only on the action-space cardinality.

---

## Related Work

The foundational projection-theoretic result underlying this paper is developed in:

*Projection Insufficiency and Trajectory Realization: A Unified Constraint-Based Framework for Bounded Systems* — [DOI: 10.5281/zenodo.19633241](https://doi.org/10.5281/zenodo.19633241) (Lean proofs: [10.5281/zenodo.19687629](https://doi.org/10.5281/zenodo.19687629))

The forward-case impossibility result which this paper extends into the stochastic regime is developed in:

*The Non-Locality of Extendability: An Impossibility Theorem for Bounded Information Systems, with Applications to Generative Sequential Systems* — [DOI: 10.5281/zenodo.19688367](https://doi.org/10.5281/zenodo.19688367) (Lean proofs: [10.5281/zenodo.19687799](https://doi.org/10.5281/zenodo.19687799))

---

## License

MIT
