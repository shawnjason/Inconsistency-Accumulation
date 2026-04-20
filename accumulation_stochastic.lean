import Mathlib.Tactic

-- Linear Inconsistency Accumulation, Stochastic Clause (Theorem 1)
-- Corresponds to the stochastic clause of Theorem 1 of:
--   "Inconsistency Accumulation in Forward-Local Sequential Policies:
--    A Lower Bound under Delayed Constraints"
--
-- For every stochastic forward-local policy π of depth h with a finite
-- action space of size at least 2, and every block count N, there
-- exists an N-block adversarial environment in which the expected
-- cumulative inconsistency satisfies
--
--   E[I_N] ≥ N / |U|.
--
-- This is strictly stronger than the paper's `E[I_N] ≥ p_π N` form:
-- the constant 1/|U| is uniform across all stochastic policies and
-- depends only on the action-space cardinality.
--
-- The proof avoids measure-theoretic infrastructure by exploiting the
-- paper's adversarial construction: since every block presents the
-- same window at the choice point, the per-block commitment
-- distribution is identical, and by linearity of expectation E[I_N]
-- is the sum of per-block failure probabilities.
--
-- Shawn Kevin Jason

section StochasticAccumulation

variable {X U : Type*} [Fintype U]

/-- A stochastic forward-local policy of depth `h`: for each trailing
    observation window, it specifies a probability distribution over
    actions. -/
structure StochasticForwardLocalPolicy (X U : Type*) (h : ℕ) [Fintype U] where
  prob        : (Fin h → X) → U → ℝ
  nonneg      : ∀ w u, 0 ≤ prob w u
  sums_to_one : ∀ w, ∑ u, prob w u = 1

/-- A delayed-violation block instantiated for stochastic policies.
    The admissibility predicate is carried with a decidability field
    so that failure probabilities can be computed as finite sums;
    the field is registered as an instance below. -/
structure StochasticDelayedBlock (X U : Type*) (h : ℕ) [Fintype U] where
  window        : Fin h → X
  admissible    : U → Prop
  decAdm        : DecidablePred admissible
  adm_exists    : ∃ u, admissible u
  nonadm_exists : ∃ u, ¬ admissible u

attribute [instance] StochasticDelayedBlock.decAdm

/-- Probability that policy `π` commits a non-admissible action in
    block `B`. -/
def failure_prob {h : ℕ}
    (π : StochasticForwardLocalPolicy X U h)
    (B : StochasticDelayedBlock X U h) : ℝ :=
  ∑ u ∈ Finset.univ.filter (fun u => ¬ B.admissible u), π.prob B.window u

/-- Expected cumulative inconsistency across a list of blocks.
    For a stochastic forward-local policy, the per-block commitment
    distribution depends only on the window, so blocks with identical
    windows produce i.i.d. Bernoulli failure indicators; the
    expectation of their sum is the sum of per-block failure
    probabilities. -/
def expected_inconsistency {h : ℕ}
    (π : StochasticForwardLocalPolicy X U h)
    (blocks : List (StochasticDelayedBlock X U h)) : ℝ :=
  (blocks.map (failure_prob π)).sum

variable {h : ℕ}

/-- Pigeonhole on probabilities: in a finite non-empty action space,
    some action has probability at least `1/|U|`. Proof by
    contradiction: if every action had strictly smaller probability,
    the total would fall short of 1. -/
lemma exists_action_high_prob
    (π : StochasticForwardLocalPolicy X U h)
    (w : Fin h → X)
    [Nonempty U] :
    ∃ u : U, π.prob w u ≥ (1 : ℝ) / Fintype.card U := by
  by_contra h_all
  push Not at h_all
  -- h_all : ∀ u, π.prob w u < 1 / Fintype.card U
  have h_card_pos : (0 : ℝ) < Fintype.card U := by
    exact_mod_cast Fintype.card_pos
  have h_card_ne : (Fintype.card U : ℝ) ≠ 0 := ne_of_gt h_card_pos
  have h_sum_lt : (∑ u, π.prob w u) < 1 := by
    calc (∑ u, π.prob w u)
        < ∑ _u : U, (1 : ℝ) / Fintype.card U := by
            apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
            intro u _
            exact h_all u
      _ = (Fintype.card U : ℝ) * ((1 : ℝ) / Fintype.card U) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = 1 := by
            field_simp
  rw [π.sums_to_one] at h_sum_lt
  linarith

/-- Theorem 1 (stochastic clause):
    For every stochastic forward-local policy `π` of depth `h` with at
    least two available actions, and every block count `N`, there
    exists an `N`-block adversarial environment in which the expected
    cumulative inconsistency satisfies `E[I_N] ≥ N / |U|`. The
    accumulation rate is therefore strictly positive for any finite
    action space. -/
theorem accumulation_stochastic
    [DecidableEq U]
    (π : StochasticForwardLocalPolicy X U h)
    (w : Fin h → X)
    (hU : 2 ≤ Fintype.card U)
    (N : ℕ) :
    ∃ blocks : List (StochasticDelayedBlock X U h),
      blocks.length = N ∧
      expected_inconsistency π blocks ≥ (N : ℝ) / Fintype.card U := by
  -- Two cardinality consequences used throughout.
  have hne : Nonempty U := Fintype.card_pos_iff.mp (by omega)
  have hntri : Nontrivial U :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  -- Step 1: pigeonhole gives an action u_max with high probability.
  obtain ⟨u_max, h_u_max⟩ := exists_action_high_prob π w
  -- Step 2: since |U| ≥ 2, an alternative action g ≠ u_max exists.
  obtain ⟨g, hg⟩ := exists_ne u_max
  -- Step 3: construct the adversarial block (admissible ↔ ≠ u_max),
  -- replicated N times.
  refine ⟨List.replicate N
    { window := w
      admissible := fun v => v ≠ u_max
      decAdm := inferInstance
      adm_exists := ⟨g, hg⟩
      nonadm_exists := ⟨u_max, fun h => h rfl⟩ },
    by simp, ?_⟩
  -- Step 4: compute expected_inconsistency of the replicated list.
  -- After unfolding, it is N * failure_prob of the (identical) block.
  unfold expected_inconsistency failure_prob
  rw [List.map_replicate, List.sum_replicate, nsmul_eq_mul]
  -- Reduce the filter {u : ¬ (u ≠ u_max)} to the singleton {u_max}.
  have h_filter :
      Finset.univ.filter (fun u : U => ¬ (u ≠ u_max)) = {u_max} := by
    ext u; simp
  rw [h_filter, Finset.sum_singleton]
  -- Goal: (N : ℝ) * π.prob w u_max ≥ (N : ℝ) / Fintype.card U.
  have h_N_nonneg : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h_lb : (N : ℝ) * ((1 : ℝ) / Fintype.card U) ≤ (N : ℝ) * π.prob w u_max :=
    mul_le_mul_of_nonneg_left h_u_max h_N_nonneg
  have h_rewrite : (N : ℝ) * ((1 : ℝ) / Fintype.card U) =
                   (N : ℝ) / Fintype.card U := by ring
  linarith

end StochasticAccumulation
