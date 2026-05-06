import Mathlib.Tactic

-- ID 060: Forward-Local Indistinguishability at the Choice Point (Lemma 1)
--
-- Catalog ID 60 (Inconsistency Accumulation paper, Lemma 1).
--
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
-- This lemma is the structural primitive underlying both the negative
-- results of IA Theorem 1 (the policy cannot condition on hidden
-- distinctions, so adversarial environments can exploit identical
-- windows to force commitments) and the positive results of
-- Proposition 1 (the policy must therefore rely on summary state if
-- it is to escape the local indistinguishability obstruction).
--
-- Shawn Kevin Jason

section LocalIndistinguishability

variable {X U : Type*}

/-- A forward-local policy of depth `h` is a function of the trailing
    observation window. -/
abbrev ForwardLocalPolicy (X U : Type*) (h : ℕ) := (Fin h → X) → U

variable {h : ℕ}

/-- Forward-local indistinguishability at the choice point (catalog ID 60
    / Lemma 1 of IA).

    A forward-local policy returns the same action on any two decision
    points whose trailing windows coincide. The policy cannot condition
    its action on a distinction that is not present in its bounded local
    information state.

    This is the structural identity that the adversarial construction in
    IA Lemma 2 and Theorem 1 exploits: by ensuring two decision points
    present identical trailing windows, the construction guarantees the
    policy cannot distinguish between branches with differing extendability
    consequences. -/
theorem forward_local_indistinguishability
    (π : ForwardLocalPolicy X U h)
    (w1 w2 : Fin h → X)
    (h_eq : w1 = w2) :
    π w1 = π w2 := by
  rw [h_eq]

end LocalIndistinguishability