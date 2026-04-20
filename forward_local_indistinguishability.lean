import Mathlib.Tactic

-- Forward-Local Indistinguishability at the Choice Point (Lemma 1)
-- Corresponds to Lemma 1 of:
--   "Inconsistency Accumulation in Forward-Local Sequential Policies:
--    A Lower Bound under Delayed Constraints"
--
-- A forward-local policy of depth h selects actions using only a
-- bounded trailing window of h observations. If two decision points
-- present identical windows, the policy cannot return different
-- actions, regardless of any global distinction between them
-- (extendability, silent-phase structure, block identity, etc.).
--
-- Shawn Kevin Jason

section LocalIndistinguishability

variable {X U : Type*}

/-- A forward-local policy of depth `h` is a function of the trailing
    observation window. -/
abbrev ForwardLocalPolicy (X U : Type*) (h : ℕ) := (Fin h → X) → U

variable {h : ℕ}

/-- Lemma 1 (Local indistinguishability at the choice point):
    A forward-local policy returns the same action on any two
    decision points whose trailing windows coincide. -/
theorem forward_local_indistinguishability
    (π : ForwardLocalPolicy X U h)
    {w₁ w₂ : Fin h → X}
    (hw : w₁ = w₂) :
    π w₁ = π w₂ := by
  rw [hw]

/-- Contrapositive form: if a forward-local policy produces different
    actions on two decision points, their trailing windows must
    differ. This is the shape used in the paper's proof of the main
    theorem, where the adversarial construction forces the same window
    at every block's choice point, so the policy's action distribution
    there cannot depend on any out-of-window distinction. -/
theorem forward_local_action_requires_window_distinction
    (π : ForwardLocalPolicy X U h)
    {w₁ w₂ : Fin h → X}
    (h_act : π w₁ ≠ π w₂) :
    w₁ ≠ w₂ := by
  intro hw
  exact h_act (forward_local_indistinguishability π hw)

end LocalIndistinguishability
