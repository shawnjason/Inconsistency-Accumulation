import Mathlib.Tactic

-- ID 067: Summary Sufficiency (Proposition 1)
--
-- Catalog ID 67 (Inconsistency Accumulation paper, Proposition 1, both clauses).
-- Companion: ID 069 in 069_full_prefix_summary_exists.lean (Remark 2,
-- non-vacuity — establishes that some extendability-preserving summary
-- always exists in the finite-horizon, finite-action setting).
-- Companion: ID 070 in 070_representation_computation_separation.lean
-- (Remark 3 — the existence guarantee does not bound representation size).
--
-- Corresponds to Proposition 1 of:
--   "Inconsistency Accumulation in Forward-Local Sequential Policies:
--    A Lower Bound under Delayed Constraints"
--
-- If an environment family admits a sequentially updatable
-- extendability-preserving summary, then a summary-safe policy
-- exists and achieves zero accumulated inconsistency: every
-- commitment along any generated trajectory uses an admissible
-- action, so no step contributes to the inconsistency counter.
--
-- The content splits into two parts:
--   (1) a zero-inconsistency clause: in any summary-safe trajectory,
--       no commitment violates admissibility (Proposition 1a);
--   (2) an existence clause: for every length N and observation
--       sequence, a summary-safe trajectory of length N exists
--       (Proposition 1b). This uses the oracle's extendability-
--       preservation axiom `successor_admits` as the inductive step.
--
-- Together with Theorem 1 (catalog ID 62), this proposition establishes
-- the architectural fault line of the paper: forward-local policies
-- cannot guarantee bounded inconsistency, but summary-equipped policies
-- on environment families with extendability-preserving summaries
-- achieve I_N = 0 uniformly. The specific representational primitive
-- — extendability preservation — is therefore both necessary (by the
-- impossibility) and sufficient (by this proposition) for a uniform
-- inconsistency bound.
--
-- Shawn Kevin Jason

section SummarySufficiency

variable {X U : Type*}

/-- A sequentially-updatable extendability-preserving summary.
    `admits σ u` holds iff committing action `u` at summary state `σ`
    preserves extendability. The two well-foundedness conditions
    capture the paper's definition: at the initial state, some
    admissible action exists (`initial_admits`); from any admitted
    commitment, the successor summary state again admits some action
    (`successor_admits`). The structure abstracts over the underlying
    state space S, making the proposition a representation-theoretic
    sufficiency statement rather than a claim about a specific encoding. -/
structure AdmissibilityOracle (X U : Type*) where
  S                 : Type*
  σ₀                : S
  update            : S → X → U → S
  admits            : S → U → Prop
  initial_admits    : ∃ u, admits σ₀ u
  successor_admits  :
    ∀ (σ : S) (x : X) (u : U), admits σ u → ∃ u', admits (update σ x u) u'

/-- A trajectory of (summary-state, action) pairs is summary-safe if
    every commitment selected an admissible action at its summary
    state. Safety is a per-step property carried uniformly across the
    trajectory. -/
def safe_trajectory {X U : Type*}
    (O : AdmissibilityOracle X U) (traj : List (O.S × U)) : Prop :=
  ∀ p ∈ traj, O.admits p.1 p.2

variable (O : AdmissibilityOracle X U)

/-- Proposition 1a / Summary Sufficiency, zero-inconsistency clause
    (catalog ID 67, first clause).

    Along any summary-safe trajectory, no commitment violates
    admissibility. This is the formal `I_N(τ) = 0` statement: every
    step's selected action lies in the admissible set, so no step
    contributes to the inconsistency counter. The proof is direct:
    safety means every step is admissible; assuming any step is
    non-admissible contradicts safety on that step. -/
theorem summary_safe_zero_inconsistency
    (traj : List (O.S × U))
    (h_safe : safe_trajectory O traj) :
    ¬ ∃ p ∈ traj, ¬ O.admits p.1 p.2 := by
  intro ⟨p, hp_mem, hp_bad⟩
  exact hp_bad (h_safe p hp_mem)

/-- Proposition 1b / Summary Sufficiency, existence clause
    (catalog ID 67, second clause).

    For every length N and every observation sequence xs, a
    summary-safe trajectory of length N exists. The construction
    threads the summary state forward using the oracle's
    extendability-preservation axiom: starting from σ₀ with the
    initial admitted action, each step uses `successor_admits` to
    produce the next admissible action at the updated summary state.
    The induction on N closes by appeal to the strengthened claim
    over arbitrary starting states with an admitted action. -/
theorem summary_safe_trajectory_exists
    (N : ℕ) (xs : Fin N → X) :
    ∃ traj : List (O.S × U),
      traj.length = N ∧ safe_trajectory O traj := by
  -- Strengthen to an arbitrary starting state with an admitted action.
  suffices h : ∀ (n : ℕ) (σ : O.S) (obs : Fin n → X),
      (∃ u, O.admits σ u) →
      ∃ traj : List (O.S × U),
        traj.length = n ∧ safe_trajectory O traj from
    h N O.σ₀ xs O.initial_admits
  intro n
  induction n with
  | zero =>
    intro _ _ _
    refine ⟨[], rfl, ?_⟩
    intro p hp
    simp at hp
  | succ m ih =>
    intro σ obs ⟨u, hu⟩
    -- Commit `u` at `σ`; the successor state still admits some action.
    have h_next : ∃ u', O.admits (O.update σ (obs 0) u) u' :=
      O.successor_admits σ (obs 0) u hu
    obtain ⟨traj_tail, h_len_tail, h_safe_tail⟩ :=
      ih (O.update σ (obs 0) u) (obs ∘ Fin.succ) h_next
    refine ⟨(σ, u) :: traj_tail, ?_, ?_⟩
    · rw [List.length_cons, h_len_tail]
    · intro p hp
      rw [List.mem_cons] at hp
      rcases hp with h_eq | h_mem
      · rw [h_eq]; exact hu
      · exact h_safe_tail p h_mem

end SummarySufficiency