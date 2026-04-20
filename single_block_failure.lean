import Mathlib.Tactic

-- Policy-Adaptive Single-Block Failure (Lemma 2)
-- Corresponds to Lemma 2 of:
--   "Inconsistency Accumulation in Forward-Local Sequential Policies:
--    A Lower Bound under Delayed Constraints"
--
-- For every forward-local policy π, one can construct a
-- delayed-violation block whose choice-point window is any chosen
-- w, whose consistent (admissible) branch requires an action
-- different from π(w), and in which therefore π's deterministic
-- choice is non-admissible by construction.
--
-- This file formalizes the deterministic case. The stochastic case
-- (E[I_N] ≥ p_π N via conditioning on history and the tower
-- property) uses Mathlib probability infrastructure and is left for a
-- separate file.
--
-- Shawn Kevin Jason

section SingleBlockFailure

variable {X U : Type*}

/-- A forward-local policy of depth `h`. -/
abbrev ForwardLocalPolicy (X U : Type*) (h : ℕ) := (Fin h → X) → U

/-- An abstract delayed-violation block. Only the data needed for the
    choice-point argument is recorded: the window presented at the
    choice point, and the admissibility predicate identifying
    extendability-preserving actions. The `adm_exists` /
    `nonadm_exists` conditions encode the paper's requirement that
    at least one action preserves extendability and at least one
    destroys it. -/
structure DelayedBlock (X U : Type*) (h : ℕ) where
  window         : Fin h → X
  admissible     : U → Prop
  adm_exists     : ∃ u, admissible u
  nonadm_exists  : ∃ u, ¬ admissible u

/-- A forward-local policy commits a non-extendable action in a block
    when its choice at the block's window is not admissible. -/
def commits_non_extendable {h : ℕ}
    (π : ForwardLocalPolicy X U h)
    (B : DelayedBlock X U h) : Prop :=
  ¬ B.admissible (π B.window)

variable {h : ℕ}

/-- Lemma 2 (Policy-adaptive single-block failure, deterministic):
    For every forward-local policy `π` of depth `h` and every window
    `w`, provided at least one alternative action to `π w` exists,
    there is a delayed-violation block with window `w` in which `π`
    commits non-extendably. -/
theorem single_block_failure_det
    (π : ForwardLocalPolicy X U h)
    (w : Fin h → X)
    (hg : ∃ g : U, g ≠ π w) :
    ∃ B : DelayedBlock X U h,
      B.window = w ∧ commits_non_extendable π B := by
  obtain ⟨g, hg_ne⟩ := hg
  -- Build the policy-indexed block: admit exactly the actions that
  -- are NOT π(w). Then π's chosen action π(w) is non-admissible by
  -- construction, and g witnesses that some admissible action exists.
  refine ⟨⟨w,
           fun u => u ≠ π w,
           ⟨g, hg_ne⟩,
           ⟨π w, fun h_ne => h_ne rfl⟩⟩,
          rfl, ?_⟩
  -- After unfolding commits_non_extendable and the block projections,
  -- the goal is definitionally ¬ (π w ≠ π w).
  show ¬ (π w ≠ π w)
  intro h_ne
  exact h_ne rfl

end SingleBlockFailure
