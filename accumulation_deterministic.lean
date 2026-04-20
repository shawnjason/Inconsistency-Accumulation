import Mathlib.Tactic

-- Linear Inconsistency Accumulation, Deterministic Case (Theorem 1)
-- Corresponds to the deterministic clause of Theorem 1 of:
--   "Inconsistency Accumulation in Forward-Local Sequential Policies:
--    A Lower Bound under Delayed Constraints"
--
-- For every deterministic forward-local policy π of depth h and every
-- integer N ≥ 0, there exists an N-block delayed-constraint
-- environment in which every block forces a non-extendable
-- commitment, so the cumulative inconsistency counter I_N = N.
--
-- The stochastic clause (E[I_N] ≥ p_π N) uses Mathlib probability
-- infrastructure and is left for a separate file.
--
-- Shawn Kevin Jason

section Accumulation

variable {X U : Type*}

abbrev ForwardLocalPolicy (X U : Type*) (h : ℕ) := (Fin h → X) → U

structure DelayedBlock (X U : Type*) (h : ℕ) where
  window         : Fin h → X
  admissible     : U → Prop
  adm_exists     : ∃ u, admissible u
  nonadm_exists  : ∃ u, ¬ admissible u

def commits_non_extendable {h : ℕ}
    (π : ForwardLocalPolicy X U h)
    (B : DelayedBlock X U h) : Prop :=
  ¬ B.admissible (π B.window)

variable {h : ℕ}

/-- The policy-indexed "bad" block at window `w`: admits all and only
    actions distinct from `π w`, so `π` commits non-extendably. -/
private def bad_block
    (π : ForwardLocalPolicy X U h)
    (w : Fin h → X)
    (g : U) (hg : g ≠ π w) : DelayedBlock X U h :=
  { window := w
    admissible := fun u => u ≠ π w
    adm_exists := ⟨g, hg⟩
    nonadm_exists := ⟨π w, fun h_ne => h_ne rfl⟩ }

private theorem bad_block_window
    (π : ForwardLocalPolicy X U h)
    (w : Fin h → X) (g : U) (hg : g ≠ π w) :
    (bad_block π w g hg).window = w := rfl

private theorem bad_block_commits
    (π : ForwardLocalPolicy X U h)
    (w : Fin h → X) (g : U) (hg : g ≠ π w) :
    commits_non_extendable π (bad_block π w g hg) := by
  show ¬ (π w ≠ π w)
  intro h_ne
  exact h_ne rfl

/-- Theorem 1 (deterministic case):
    For every forward-local policy `π` of depth `h`, every window `w`,
    every alternative action, and every block count `N`, there exists
    an `N`-block environment in which every block forces a
    non-extendable commitment. That is, the cumulative inconsistency
    counter satisfies `I_N = N` exactly. -/
theorem accumulation_deterministic
    (π : ForwardLocalPolicy X U h)
    (w : Fin h → X)
    (hg : ∃ g : U, g ≠ π w)
    (N : ℕ) :
    ∃ blocks : List (DelayedBlock X U h),
      blocks.length = N ∧
      (∀ B ∈ blocks, commits_non_extendable π B) ∧
      (∀ B ∈ blocks, B.window = w) := by
  obtain ⟨g, hg_ne⟩ := hg
  refine ⟨List.replicate N (bad_block π w g hg_ne), ?_, ?_, ?_⟩
  · simp
  · intro B' hB'
    rw [List.eq_of_mem_replicate hB']
    exact bad_block_commits π w g hg_ne
  · intro B' hB'
    rw [List.eq_of_mem_replicate hB']
    rfl

end Accumulation
