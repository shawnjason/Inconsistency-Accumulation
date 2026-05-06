import Mathlib.Tactic

-- ID 062a: Linear Inconsistency Accumulation, Deterministic Clause (Theorem 1)
--
-- Catalog ID 62 (Inconsistency Accumulation paper, Theorem 1 deterministic clause).
-- Companion: ID 062b in accumulation_stochastic.lean (stochastic clause,
-- finite-combinatorial form).
-- Companion: ID 079a/079b in accumulation_stochastic_measure_pathA/pathB
-- (stochastic clause, full measure-theoretic form via two independent proof paths).
--
-- Corresponds to the deterministic clause of Theorem 1 of:
--   "Inconsistency Accumulation in Forward-Local Sequential Policies:
--    A Lower Bound under Delayed Constraints"
--
-- For every deterministic forward-local policy π of depth h and every
-- integer N ≥ 0, there exists an N-block delayed-constraint
-- environment in which every block forces a non-extendable
-- commitment, so the cumulative inconsistency counter I_N = N.
--
-- The construction is policy-adaptive: given π, build a single
-- "bad" block whose admissibility predicate excludes exactly π's
-- chosen action on the window, then concatenate N independent copies
-- of that block. By Lemma 2 (catalog ID 61), each block forces a
-- non-extendable commitment with certainty. Linearity of the counter
-- yields I_N = N exactly.
--
-- The stochastic clause (E[I_N] ≥ N/|U|) uses pigeonhole-on-probabilities
-- and finite-sum linearity in 062b; the full measure-theoretic form is
-- in 079a/079b.
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
    actions distinct from `π w`, so `π` commits non-extendably. The
    `g` parameter witnesses that some admissible action exists; the
    block's non-admissible witness is `π w` itself. -/
private def bad_block
    (π : ForwardLocalPolicy X U h)
    (w : Fin h → X)
    (g : U) (hg : g ≠ π w) : DelayedBlock X U h :=
  { window := w
    admissible := fun u => u ≠ π w
    adm_exists := ⟨g, hg⟩
    nonadm_exists := ⟨π w, fun h_ne => h_ne rfl⟩ }

/-- The bad block's window is `w` by construction. -/
private theorem bad_block_window
    (π : ForwardLocalPolicy X U h)
    (w : Fin h → X) (g : U) (hg : g ≠ π w) :
    (bad_block π w g hg).window = w := rfl

/-- The bad block forces `π` to commit non-extendably: π's chosen
    action on the window is `π w`, which the block's admissibility
    predicate excludes. -/
private theorem bad_block_commits
    (π : ForwardLocalPolicy X U h)
    (w : Fin h → X) (g : U) (hg : g ≠ π w) :
    commits_non_extendable π (bad_block π w g hg) := by
  show ¬ (π w ≠ π w)
  intro h_ne
  exact h_ne rfl

/-- Theorem 1, deterministic clause (catalog ID 62 / IA Theorem 1
    deterministic case).

    For every forward-local policy π of depth h, every window w,
    every alternative action g ≠ π(w), and every block count N, there
    exists an N-block environment in which every block forces a
    non-extendable commitment. The cumulative inconsistency counter
    satisfies I_N = N exactly.

    The construction concatenates N copies of the policy-indexed bad
    block via List.replicate. Each block is identical: same window w,
    same admissibility predicate (excluding π w), same admissibility
    witness g, same non-admissibility witness π w. By Lemma 2
    (catalog ID 61), π commits non-extendably on each, so the counter
    accumulates to exactly N. -/
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