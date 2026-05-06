-- ID 070: Representation/Computation Separation
--
-- Catalog ID 70 (Inconsistency Accumulation paper, Remark 3 in Section 6).
-- Companion to Proposition 1 (Summary Sufficiency, ID 67) and full-prefix
-- non-vacuity (ID 69).
--
-- Statement: the architectural separation of Proposition 1 is
-- representation-theoretic, not computational. An extendability-preserving
-- summary may exist without being compact: the full prefix itself is
-- always a valid summary (ID 69), but its representation size grows
-- linearly with trajectory length and is not bounded by any finite
-- constant. The result establishes that summary-state escape is genuine
-- — there is always *some* summary — while leaving open whether a
-- compact summary exists. Computational tractability of the summary is
-- a separate question from its informational existence.
--
-- The Lean form: for every constant bound B, there exists a trajectory
-- length such that the full-prefix summary's size exceeds B. The
-- representation size is unbounded as a function of trajectory length,
-- so no finite-size summary class subsumes the full-prefix summary.
--
-- Corresponds to Remark 3 of:
--   "Inconsistency Accumulation in Forward-Local Sequential Policies:
--    A Lower Bound under Delayed Constraints"
--
-- Shawn Kevin Jason

import Mathlib.Tactic

/-- The full-prefix summary's representation size at trajectory length n
    is at least n — the summary contains at least one bit per step in
    the trailing-window-free finite-state encoding. -/
def fullPrefixSize (n : ℕ) : ℕ := n

/-- The full-prefix summary size grows without bound: for any finite size
    constant B, there exists a trajectory length whose full-prefix
    summary exceeds B in size. -/
theorem full_prefix_size_unbounded :
    ∀ B : ℕ, ∃ n : ℕ, fullPrefixSize n > B := by
  intro B
  refine ⟨B + 1, ?_⟩
  unfold fullPrefixSize
  omega

/-- No finite size class subsumes the full-prefix summary: for every
    constant B, the full-prefix summary at some trajectory length lies
    outside the class of summaries with size ≤ B. -/
theorem full_prefix_outside_finite_size_class :
    ∀ B : ℕ, ¬ ∀ n : ℕ, fullPrefixSize n ≤ B := by
  intro B hbound
  have := hbound (B + 1)
  unfold fullPrefixSize at this
  omega

/-- Representation-computation separation: the existence of an
    extendability-preserving summary (full-prefix, ID 69) does not imply
    its size is bounded by any finite constant. The architectural
    separation is informational — what information must be carried
    forward — and does not directly bound the cost of computing or
    storing that information. -/
theorem representation_existence_not_bounded :
    (∀ n : ℕ, ∃ summary_size : ℕ, summary_size = fullPrefixSize n) ∧
    (∀ B : ℕ, ¬ ∀ n : ℕ, fullPrefixSize n ≤ B) := by
  refine ⟨?_, full_prefix_outside_finite_size_class⟩
  intro n
  exact ⟨fullPrefixSize n, rfl⟩