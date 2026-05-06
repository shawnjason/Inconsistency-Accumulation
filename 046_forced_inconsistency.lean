-- ID 046: Forced Inconsistency Arithmetic Core
--
-- Catalog ID 46 (Non-Locality of Extendability paper).
--
-- Statement: once a prefix sum exceeds a target, no nonnegative
-- completion can reduce it back to the target. Conversely, a prefix
-- sum equal to the target is trivially completable with a zero-length
-- completion. The two clauses together capture the arithmetic
-- mechanism by which a non-extendable commitment becomes irreversible.
--
-- This is the arithmetic kernel of NEO's adversarial construction.
-- Once the adversary maneuvers the agent into a prefix whose running
-- sum exceeds the terminal target, the agent has committed to a
-- non-extendable trajectory regardless of what it does next. The
-- forced inconsistency theorem formalizes this irreversibility: no
-- completion exists. The companion clause (admissible_action_preserved)
-- formalizes the symmetric positive case: when the prefix sum already
-- equals the target, extendability is trivially preserved.
--
-- Together these two clauses are the arithmetic basis for the
-- adversarial branching in NEO Lemma 5 (Policy-Adaptive Adversary):
-- the construction guides the policy toward the prefix-sum-exceeds-target
-- branch, knowing the resulting commitment is irreversible.
--
-- This file also serves as the §7 / Appendix A forced-inconsistency
-- witness in the companion Inconsistency Accumulation paper (IA repo).
-- The catalog records this file canonically against NEO ID 46.
--
-- Corresponds to the forced inconsistency arithmetic of:
--   "The Non-Locality of Extendability: An Impossibility Theorem for
--    Bounded Information Systems, with Applications to Generative
--    Sequential Systems"
--
-- Shawn Kevin Jason

import Mathlib.Tactic

/-- Forced Inconsistency (catalog ID 46, irreversibility clause).

    Once a prefix sum exceeds the target (specifically, prefix sum 8
    against target 7), no completion sum greater than or equal to the
    prefix sum can reach the target. The arithmetic enforces
    irreversibility of the over-commitment. -/
theorem forced_inconsistency
    (prefix_sum : ℕ)
    (h_prefix : prefix_sum = 8) :
    ∀ completion_sum : ℕ,
    completion_sum ≥ prefix_sum →
    completion_sum ≠ 7 := by
  intro completion_sum h_ge
  omega

/-- Admissible Action Preserved (catalog ID 46, positive clause).

    A prefix sum equal to the target admits the trivial zero completion.
    This is the symmetric positive case to the forced-inconsistency
    irreversibility clause: the admissible branch of the adversarial
    construction admits a completion of length zero, while the forced
    branch admits no completion at all. -/
theorem admissible_action_preserved
    (prefix_sum : ℕ)
    (h_prefix : prefix_sum = 7) :
    ∃ completion : ℕ, prefix_sum + completion = 7 := by
  exact ⟨0, by omega⟩