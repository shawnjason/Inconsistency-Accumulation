# Lean 4 Formalization — Inconsistency Accumulation in Forward-Local Sequential Policies

Machine-checked Lean 4 proofs for the discrete-case results of

> **Inconsistency Accumulation in Forward-Local Sequential Policies: A Lower Bound under Delayed Constraints**

## Author

Shawn Kevin Jason — Independent Researcher, Las Vegas, NV
ORCID: [0009-0003-9208-1556](https://orcid.org/0009-0003-9208-1556)

## What This Repository Contains

Seven standalone Lean 4 proof files covering all policy-level discrete results
of the paper that admit a concise machine-checked formalization. The proofs
split into two groups: an **arithmetic witness core** that mechanically
verifies the specific sum-based witness family used in Section 7 of the paper,
and a **policy-level group** that formalizes the paper's main lemmas and the
deterministic clause of the main theorem.

Each file is independent, imports only `Mathlib.Tactic`, and verifies in the
Lean 4 web editor at [live.lean-lang.org](https://live.lean-lang.org) against
the current Mathlib release.

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

Each file is independent; no cross-file imports are required.

## Mapping to the Paper

| Paper result | File | Lean theorem |
|---|---|---|
| Lemma 1 | `forward_local_indistinguishability.lean` | `forward_local_indistinguishability` |
| Lemma 2 | `single_block_failure.lean` | `single_block_failure_det` |
| Theorem 1 (deterministic clause) | `accumulation_deterministic.lean` | `accumulation_deterministic` |
| Proposition 1 (both clauses) | `summary_sufficiency.lean` | `summary_safe_zero_inconsistency`, `summary_safe_trajectory_exists` |
| §7 arithmetic witness (extendability) | `extendability_indistinguishability.lean` | `extendability_indistinguishability` |
| §7 forced inconsistency | `forced_inconsistency.lean` | `forced_inconsistency`, `admissible_action_preserved` |
| §7 horizon non-convergence | `horizon_nonconvergence.lean` | `horizon_nonconvergence` |

## Scope and Limitations

These proofs establish the formal skeleton of the paper's discrete
policy-level results. They do not establish:

- **The stochastic clause of Theorem 1** (`E[I_N] ≥ p_π · N`). This requires
  Mathlib's conditional-expectation infrastructure and a tower-property
  argument over trajectory distributions. Its formalization is in progress
  and not claimed in this release.
- **The empirical corroboration** of Section 8 of the paper (simulation
  results). Those are reported separately.
- **The application to bounded-context language models** (Section 9.2 of
  the paper), which is motivational rather than formal.

## Associated Paper

The paper is under review at SSRN (Abstract ID 6570761). Once peer-review
status clears, the arXiv preprint link will be added here.

## License

Proofs are released for open academic verification and reference.
