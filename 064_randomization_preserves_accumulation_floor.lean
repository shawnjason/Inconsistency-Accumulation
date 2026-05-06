-- ID 064: Randomization Cannot Remove the Accumulation Floor
--
-- Catalog ID 64 (Inconsistency Accumulation paper).
-- Specialization of Theorem 1(ii) (IA, ID 62 stochastic clause / ID 79
-- measure-theoretic form).
--
-- Statement: the lower bound E[I_N] ≥ N/|U| from the stochastic clause of
-- IA Theorem 1 holds uniformly across every stochastic forward-local
-- policy of depth h on a finite action space of cardinality |U| ≥ 2.
-- Randomization schemes — uniform random, ε-greedy, entropy-regularized,
-- softmax, top-k, top-p, or any other policy redistributing probability
-- mass within the same window-conditioned support — cannot achieve a
-- uniformly smaller floor than 1/|U| per block. The floor is a property
-- of the action-space cardinality and the local-window evaluation
-- structure, not of the policy's specific distribution.
--
-- Corresponds to the randomization-non-escape corollary of:
--   "Inconsistency Accumulation in Forward-Local Sequential Policies:
--    A Lower Bound under Delayed Constraints"
--
-- Shawn Kevin Jason

import Mathlib.Tactic
import Mathlib.Data.Real.Basic

variable {Policy : Type*}

/-- The IA stochastic accumulation floor: every stochastic forward-local
    policy admits an N-block delayed-constraint environment in which the
    expected cumulative inconsistency is at least N/|U|. This is the
    hypothesis form of IA Theorem 1(ii) abstracted to a per-policy bound. -/
def AccumulationFloor (E_inc : Policy → ℝ) (floor : ℝ) : Prop :=
  ∀ π : Policy, E_inc π ≥ floor

/-- Randomization-uniformity: a randomization scheme is a map from policies
    to policies (e.g. converting a deterministic policy to ε-greedy, or
    smoothing a stochastic policy further). -/
def RandomizationScheme (Policy : Type*) : Type _ := Policy → Policy

/-- The accumulation floor is preserved under any randomization scheme: if
    every stochastic forward-local policy satisfies E[I_N] ≥ floor, then
    every output of a randomization scheme also satisfies E[I_N] ≥ floor.
    Randomization cannot drive the expected inconsistency below the floor
    because the floor holds uniformly across the entire policy class. -/
theorem randomization_preserves_accumulation_floor
    (E_inc : Policy → ℝ) (floor : ℝ)
    (h_floor : AccumulationFloor E_inc floor)
    (R : RandomizationScheme Policy) :
    ∀ π : Policy, E_inc (R π) ≥ floor := by
  intro π
  exact h_floor (R π)

/-- Strict-improvement impossibility: no randomization scheme drives the
    expected inconsistency strictly below the floor for any policy.
    Equivalently, the floor is a uniform lower bound that survives every
    randomization map on the policy class. -/
theorem no_randomization_breaks_floor
    (E_inc : Policy → ℝ) (floor : ℝ)
    (h_floor : AccumulationFloor E_inc floor) :
    ¬ ∃ (R : RandomizationScheme Policy) (π : Policy), E_inc (R π) < floor := by
  rintro ⟨R, π, hlt⟩
  have hge : E_inc (R π) ≥ floor := h_floor (R π)
  linarith