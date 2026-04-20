import Mathlib.Tactic

-- Forced Inconsistency Lemma
-- Shawn Kevin Jason

theorem forced_inconsistency
    (prefix_sum : ℕ)
    (h_prefix : prefix_sum = 8) :
    ∀ completion_sum : ℕ,
    completion_sum ≥ prefix_sum →
    completion_sum ≠ 7 := by
  intro completion_sum h_ge
  omega

theorem admissible_action_preserved
    (prefix_sum : ℕ)
    (h_prefix : prefix_sum = 7) :
    ∃ completion : ℕ, prefix_sum + completion = 7 := by
  exact ⟨0, by omega⟩