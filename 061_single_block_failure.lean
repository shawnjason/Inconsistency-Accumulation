import Mathlib.Tactic

-- ID 061: Policy-Adaptive Single-Block Failure (Lemma 2)
--
-- Catalog ID 61 (Inconsistency Accumulation paper, Lemma 2 deterministic clause).
--
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
-- separate file (062b_accumulation_stochastic.lean and the two
-- measure-theoretic paths in 079a/079b).
--
-- Lemma 2 is the per-block kernel of IA Theorem 1: by concatenating
-- N independent copies of the policy-indexed block, the inconsistency
-- counter accumulates linearly in N (deterministic clause) or with
-- expected value bounded below by N/|U| (stochastic clause). The
-- block construction is policy-adaptive: the adversarial environment
-- is built using knowledge of π's action at the choice-point window.
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

/-- Policy-Adaptive Single-Block Failure (catalog ID 61 / Lemma 2 of IA,
    deterministic case).

    For every deterministic forward-local policy π of depth h and every
    window w, provided at least one alternative action to π(w) exists,
    there is a delayed-violation block with window w in which π commits
    non-extendably.

    The block is constructed adversarially against π: the admissibility
    predicate admits exactly those actions that differ from π(w). The
    policy's chosen action π(w) is therefore non-admissible by
    construction, while the witnessed alternative g ≠ π(w) preserves
    the admissibility-exists requirement of the block. By Lemma 1
    (forward-local indistinguishability, catalog ID 60), the policy
    cannot escape this construction by conditioning on global structure
    outside the window — its window-only action is fixed at π(w). -/
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