import Mathlib.Tactic

-- Extendability Indistinguishability
-- Two prefixes can agree on a bounded projection yet differ in extendability
-- Shawn Kevin Jason

def Extendable (prefix_sum : ℕ) (target : ℕ) : Prop :=
  ∃ completion : ℕ, prefix_sum + completion = target

theorem extendability_indistinguishability
    (target : ℕ)
    (h_target : target = 7) :
    Extendable 7 target ∧ ¬Extendable 8 target := by
  subst h_target
  constructor
  · exact ⟨0, by omega⟩
  · intro ⟨c, hc⟩
    omega