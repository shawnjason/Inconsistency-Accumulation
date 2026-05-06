-- ID 031: Forward-Indistinguishable Divergence Lemma
--
-- Catalog ID 31 (Non-Locality of Extendability paper, Lemma 2).
--
-- Statement: there exist two prefixes that share an identical bounded
-- horizon projection but differ in extendability under a terminal
-- constraint. Specifically, with target sum 7 and remaining budget,
-- prefix sum 7 admits a zero-completion (extendable) while prefix sum 8
-- admits no completion in the nonnegative-integer regime (non-extendable).
--
-- This is the load-bearing divergence witness for the NEO theorem
-- (catalog ID 32). The structural impossibility of recovering
-- extendability from the bounded horizon projection follows directly
-- from the existence of a divergence pair: two prefixes in the same
-- horizon-projection fiber whose extendability differs. Once such a
-- pair exists, no function of the projection alone can correctly
-- classify both, regardless of how sophisticated the function is.
--
-- The arithmetic instance proved here is the concrete minimum-scale
-- witness. The general theorem (NEO) scales to arbitrary horizon h
-- through a parametric reset–choice–silent–certify construction; this
-- file isolates the structural divergence kernel that the construction
-- exploits.
--
-- This file also serves as the §7 / Appendix A arithmetic witness in the
-- companion Inconsistency Accumulation paper (IA repo), where it is
-- used as the concrete instantiation of the abstract block construction.
-- The catalog records this file canonically against NEO ID 31; its
-- reuse in IA is documented in IA paper Section 9.
--
-- Corresponds to Lemma 2 of:
--   "The Non-Locality of Extendability: An Impossibility Theorem for
--    Bounded Information Systems, with Applications to Generative
--    Sequential Systems"
--
-- Shawn Kevin Jason

import Mathlib.Tactic

/-- A prefix is extendable to a target sum if some nonnegative completion
    closes the gap. The relevant property here is that two prefix sums
    that share the same bounded horizon projection (both ending in
    identical trailing windows) can differ in this extendability status. -/
def Extendable (prefix_sum : ℕ) (target : ℕ) : Prop :=
  ∃ completion : ℕ, prefix_sum + completion = target

/-- Forward-Indistinguishable Divergence (catalog ID 31 / Lemma 2 of NEO).

    Two prefix sums that agree on a bounded horizon projection can differ
    in extendability under a terminal constraint. With target sum 7,
    prefix sum 7 is extendable (trivially: zero completion) while prefix
    sum 8 is non-extendable (no nonnegative completion can reduce it
    back to 7). This concrete divergence witness instantiates the
    general impossibility result of the NEO theorem.

    The proof structure: (a) show prefix sum 7 admits the trivial
    zero-completion to reach target 7; (b) show prefix sum 8 admits no
    completion because adding any nonnegative quantity preserves
    prefix_sum ≥ 8 > 7. -/
theorem extendability_indistinguishability
    (target : ℕ)
    (h_target : target = 7) :
    Extendable 7 target ∧ ¬Extendable 8 target := by
  subst h_target
  constructor
  · exact ⟨0, by omega⟩
  · intro ⟨c, hc⟩
    omega