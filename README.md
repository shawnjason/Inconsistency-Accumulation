# Lean 4 Formalization — Inconsistency Accumulation in Forward-Local Sequential Policies

Machine-checked Lean 4 proofs for

> **Inconsistency Accumulation in Forward-Local Sequential Policies: A Lower Bound under Delayed Constraints**

## Author

Shawn Kevin Jason — Independent Researcher, Las Vegas, NV
ORCID: [0009-0003-9208-1556](https://orcid.org/0009-0003-9208-1556)

## What This Repository Contains

Ten standalone Lean 4 proof files covering all policy-level results of
the paper. The proofs split into three groups: an **arithmetic witness
core** that mechanically verifies the specific sum-based witness family
used in Section 7, a **policy-level group** that formalizes the paper's
main lemmas, both clauses of the main theorem, and the positive
summary-sufficiency result, and a **measure-theoretic integration**
group that constructs the trajectory probability space and proves the
main integration theorem in its full measure-theoretic form — verified
twice, via two architecturally distinct proof paths.

Each file verifies in the Lean 4 web editor at
[live.lean-lang.org](https://live.lean-lang.org) against the current
Mathlib release.

## Dual-Path Measure-Theoretic Verification

The paper's load-bearing product-measure independence identity — the
core fact underlying the tower-property argument of §5 — is verified
twice in this repository through entirely different Mathlib
infrastructure. Either file compiles in isolation; neither depends on
the other. The shared conclusion is therefore certified through two
independent machine-checked proofs.

**`accumulation_stochastic_measure_pathA.lean`** — Path A verifies the
identity via fiber-partitioning with an explicit coordinate-update
bijection. Uses `Finset.sum_fiberwise`, `Function.update`, and
`Finset.sum_bij` with a per-fiber invariance argument.

**`accumulation_stochastic_measure_pathB.lean`** — Path B verifies the
identity via the canonical product isomorphism. Uses Mathlib's
`Fin.insertNthEquiv`, `Fintype.sum_prod_type`, and `Fin.prod_univ_succAbove`
to establish the Fubini-style factorization on the discrete product space.

Both files prove the same main theorem `accumulation_stochastic_measure`
with identical signatures. A reviewer can compile either file
independently to verify the full measure-theoretic formalization.

## Files

### Arithmetic Witness Core (Section 7 of the paper)

**`extendability_indistinguishability.lean`**
Concrete arithmetic witness for Section 7: two prefix sums agree on the
bounded projection but differ in extendability. Specifically, prefix sum 7
extends to target 7, while prefix sum 8 does not.

**`forced_inconsistency.lean`**
Arithmetic core of the forced inconsistency construction underlying the
witness family: once the prefix sum exceeds the target, no completion can
reach the target. The companion result formalizes that if the prefix sum
equals the target, a zero-length completion suffices.

**`horizon_nonconvergence.lean`**
For every horizon `h`, a separating pair exists at depth `h+1`: two states
with identical bounded projections that differ in extendability. No finite
evaluation horizon eliminates the failure class.

### Policy-Level Results

**`forward_local_indistinguishability.lean`** — Lemma 1
A forward-local policy cannot condition its action on any distinction that
is not present in its bounded local window. Formalized via a
`ForwardLocalPolicy` abbreviation (a function of the trailing observation
window) and proved near-definitionally.

**`single_block_failure.lean`** — Lemma 2 (deterministic)
For every forward-local policy, there exists a policy-indexed
delayed-violation block in which the policy commits non-extendably.
Formalized via a `DelayedBlock` structure with explicit admissibility and
non-admissibility witnesses; the construction admits exactly those actions
distinct from the policy's choice at the target window.

**`accumulation_deterministic.lean`** — Theorem 1 (deterministic clause)
For every forward-local policy, every window, and every `N`, there exists
an `N`-block environment in which every block forces a non-extendable
commitment. The cumulative inconsistency counter satisfies `I_N = N` exactly.
Constructed as `List.replicate` of the Lemma 2 policy-indexed block.

**`accumulation_stochastic.lean`** — Theorem 1 (stochastic clause, finite-combinatorial form)
For every stochastic forward-local policy with `|U| ≥ 2` and every `N`,
there exists an `N`-block environment in which the expected cumulative
inconsistency satisfies `E[I_N] ≥ N/|U|`. The Lean formalization delivers
the uniform policy-independent bound `1/|U|` via a pigeonhole-on-
probabilities argument and finite-sum linearity, so no measure-theoretic
infrastructure is required.

### Measure-Theoretic Integration (two independent proofs)

**`accumulation_stochastic_measure_pathA.lean`** — Theorem 1 (stochastic clause, full measure-theoretic form, Path A)
The full measure-theoretic integration theorem via fiber-partitioning.
Constructs the trajectory probability space as the `N`-fold product of
the policy's action distribution on the finite action space `U`;
constructs the filtration `F_k` as the σ-algebra generated by the first
`k` coordinate projections; defines the per-block failure indicators
`X_k` with measurability and integrability; proves the **bridge lemma**
that the conditional expectation `μ[X_k | F_k]` is almost-surely bounded
below by `1/|U|` via
`MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq`; and proves the
main integration theorem `E_μ[I_N] ≥ N/|U|` via the tower property and
linearity of expectation. The product-measure independence identity
`setIntegral_X_eq_of_determined` is closed by partitioning the sum via
`Finset.sum_fiberwise`, factoring at the adversarial action, and using
an explicit coordinate-`k` update bijection (`Function.update`)
together with `π.sums_to_one`. The bridge from `F_k`-measurability to
the determined-by-prefix property (`F_measurable_determined`) is closed
by σ-algebra induction on the generating cylinders using
`MeasurableSpace.induction_on`. Zero `sorry`.

**`accumulation_stochastic_measure_pathB.lean`** — Theorem 1 (stochastic clause, full measure-theoretic form, Path B)
The same measure-theoretic integration theorem via the canonical
product-isomorphism factorization. All shared infrastructure from Path A
is included verbatim (trajectory space construction, filtration,
measurability, integrability, `F_measurable_determined`); the load-
bearing product-measure identity `setIntegral_X_eq_of_determined_via_equiv`
is proved independently using `Fin.insertNthEquiv` to establish the
product equivalence `(Fin (N+1) → U) ≃ U × (Fin N → U)`, then
`Fintype.sum_prod_type` to split the Cartesian sum into nested sums,
`Fin.prod_univ_succAbove` to factor the trajectory-measure product at
position `k`, and `π.sums_to_one` to close. The main theorem wrapper
`setIntegral_X_eq` dispatches from the standard `Fin N` interface to
the `Fin (M+1)` implementation via a case-split on `N`. Zero `sorry`.

**`summary_sufficiency.lean`** — Proposition 1 (both clauses)
Given an `AdmissibilityOracle` satisfying the extendability-preservation
axioms (initial-admits, successor-admits), both clauses of Proposition 1 are
formalized: first, a summary-safe trajectory contains no non-admissible
commitment; second, a summary-safe trajectory of any length exists, with
the inductive step invoking the successor-admits axiom.

## How to Verify

1. Open [live.lean-lang.org](https://live.lean-lang.org)
2. Confirm that the dropdown in the upper right is set to **Latest Mathlib**
3. Paste the contents of any `.lean` file into the editor
4. Wait for checking to complete — "No goals" on each theorem and no errors
   in the Problems pane confirms verification

Each file is independent; no cross-file imports are required. In
particular, `accumulation_stochastic_measure_pathA.lean` and
`accumulation_stochastic_measure_pathB.lean` each provide a complete,
self-contained proof of the measure-theoretic main theorem — a reviewer
wishing to verify the stochastic clause may compile either file alone.

## Mapping to the Paper

| Paper result | File | Lean theorem |
|---|---|---|
| Lemma 1 | `forward_local_indistinguishability.lean` | `forward_local_indistinguishability` |
| Lemma 2 | `single_block_failure.lean` | `single_block_failure_det` |
| Theorem 1 (deterministic clause) | `accumulation_deterministic.lean` | `accumulation_deterministic` |
| Theorem 1 (stochastic clause, finite-combinatorial form) | `accumulation_stochastic.lean` | `accumulation_stochastic` |
| Theorem 1 (stochastic clause, measure-theoretic form, Path A) | `accumulation_stochastic_measure_pathA.lean` | `accumulation_stochastic_measure` |
| Theorem 1 (stochastic clause, measure-theoretic form, Path B) | `accumulation_stochastic_measure_pathB.lean` | `accumulation_stochastic_measure` |
| Proposition 1 (both clauses) | `summary_sufficiency.lean` | `summary_safe_zero_inconsistency`, `summary_safe_trajectory_exists` |
| §7 arithmetic witness (extendability) | `extendability_indistinguishability.lean` | `extendability_indistinguishability` |
| §7 forced inconsistency | `forced_inconsistency.lean` | `forced_inconsistency`, `admissible_action_preserved` |
| §7 horizon non-convergence | `horizon_nonconvergence.lean` | `horizon_nonconvergence` |

## Scope and Limitations

These proofs establish the full formal skeleton of the paper's
policy-level results, including both the deterministic and stochastic
clauses of Theorem 1 in both finite-combinatorial and full
measure-theoretic forms, with the measure-theoretic form verified
through two independent proof paths. They do not establish:

- **The empirical corroboration** of Section 8 of the paper (simulation
  results). Those are reported separately.
- **The application to bounded-context language models** (Section 9.2 of
  the paper), which is motivational rather than formal.

Both measure-theoretic files (`pathA` and `pathB`) are complete end to
end, with no `sorry` remaining. All supporting probability-space
infrastructure — singleton measure identities, product-measure
independence, the `F_k`-measurability bridge, the conditional-
expectation bridge lemma, and the main integration theorem
`E_μ[I_N] ≥ N/|U|` — is machine-checked against current Mathlib in
each file.

Note that the stochastic clause of Theorem 1 is proved in Lean with a
uniform bound `E[I_N] ≥ N/|U|`, which is strictly stronger than the
original `E[I_N] ≥ p_π · N` form in earlier drafts of the paper: the
constant `1/|U|` is uniform across all stochastic policies and depends
only on the action-space cardinality.

## License

Proofs are released for open academic verification and reference.
