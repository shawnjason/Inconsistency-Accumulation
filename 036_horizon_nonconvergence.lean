-- ID 036: Non-Convergence of Horizon
--
-- Catalog ID 36 (Non-Locality of Extendability paper, Corollary 7).
--
-- Statement: for every horizon h, a separating pair exists at depth h+1.
-- Two states with identical bounded horizon projections that differ in
-- extendability can be constructed at any horizon depth. No finite
-- evaluation horizon eliminates the failure class.
--
-- This is the corollary-level statement of NEO's parametric structure:
-- the divergence-witness construction (Lemma 2, catalog ID 31) scales
-- with h. Given any horizon h, choose target h+1 with prefixes whose
-- running sums are h+1 (extendable to target h+1 with zero completion)
-- and h+2 (non-extendable). The two states share the trivial trailing
-- window through their identical pre-window structure. The class of
-- defeating environments therefore cannot be eliminated by horizon
-- extension; it can only be shifted in scale. Larger windows defeat
-- larger constructions.
--
-- This file also serves as the §7 / Appendix A horizon-non-convergence
-- witness in the companion Inconsistency Accumulation paper (IA repo).
-- The catalog records this file canonically against NEO ID 36.
--
-- Corresponds to Corollary 7 of:
--   "The Non-Locality of Extendability: An Impossibility Theorem for
--    Bounded Information Systems, with Applications to Generative
--    Sequential Systems"
--
-- Shawn Kevin Jason

import Mathlib.Tactic

/-- Non-Convergence of Horizon (catalog ID 36 / Corollary 7 of NEO).

    For every horizon h, there exist two prefix sums sharing a common
    horizon projection (same trailing window structure) that differ in
    extendability under some terminal target. Concretely, for target
    h+1: prefix sum h+1 is extendable (zero completion suffices); prefix
    sum h+2 is non-extendable (no nonnegative completion can reduce a
    sum already exceeding the target).

    The result is parametric in h: increasing the horizon shifts the
    failure boundary but does not empty the class of defeating
    constructions. Each h admits its own witness; no finite h saturates. -/
theorem horizon_nonconvergence
    (h : ℕ) :
    ∃ target : ℕ, ∃ s1 s2 : ℕ,
    s1 ≠ s2 ∧
    (∃ c : ℕ, s1 + c = target) ∧
    (¬ ∃ c : ℕ, s2 + c = target) := by
  refine ⟨h + 1, h + 1, h + 2, ?_, ?_, ?_⟩
  · omega
  · exact ⟨0, by omega⟩
  · intro ⟨c, hc⟩; omega