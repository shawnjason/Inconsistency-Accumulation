import Mathlib.Tactic

-- Horizon Nonconvergence
-- For every horizon h, a separating pair exists at depth h+1
-- Shawn Kevin Jason

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