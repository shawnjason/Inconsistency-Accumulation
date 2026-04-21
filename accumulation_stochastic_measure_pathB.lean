/-
# Measure-Theoretic Stochastic Accumulation — Path B (Product-Isomorphism Route)

This file is one of two independent machine-checked proofs of the main
theorem in the paper
"Inconsistency Accumulation in Forward-Local Sequential Policies:
 A Lower Bound under Delayed Constraints."

## The two paths

The paper's load-bearing product-measure independence identity admits
two architecturally distinct proofs, both formalized in this repository:

- **Path A** (`accumulation_stochastic_measure_pathA.lean`): proves the
  identity via fiber-partitioning with an explicit coordinate-update
  bijection, using `Finset.sum_fiberwise`, `Function.update`, and
  `Finset.sum_bij`.

- **Path B** (this file): proves the identity via the canonical product
  isomorphism, using Mathlib's `Fin.insertNthEquiv`,
  `Fintype.sum_prod_type`, `Fin.prod_univ_succAbove`, and the Fubini-
  style factorization on the discrete product space.

Both files verify the same main theorem end-to-end. A reviewer can
compile either file independently; neither depends on the other. The
shared claim — the product-measure independence identity underlying
the tower-property argument of §5 — is therefore certified twice,
through entirely different Mathlib infrastructure.

## What this file builds

- A trajectory probability space (Ω, 𝓕, μ) induced by running a
  stochastic forward-local policy π in the paper's adversarial
  environment
- A filtration F_k representing "information available after k complete
  blocks"
- Per-block failure indicators X_k, with measurability
- A bridge lemma identifying μ[X_k | F_{k-1}] with the policy's
  per-window failure probability
- The main theorem: E_μ[∑ X_k] ≥ N / |U|

## Structure

1. Basic objects (action space, window, policy, block)
2. Trajectory space construction (Ω, kernels, μ, filtration)
3. Failure indicators and measurability
4. Determined-by-prefix characterization of the filtration
5. The product-measure independence identity (Path B, via
   `piSuccAboveEquiv` and `Fin.insertNthEquiv`)
6. Bridge lemma and main theorem

Author: Shawn Kevin Jason
-/

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.ConditionalProbability
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory ENNReal NNReal

namespace InconsistencyAccumulation

/-! ## Section 1: Basic Objects

The action space, window, forward-local policy, and the adversarial block.
These mirror the definitions in `accumulation_stochastic.lean` but are
restated here so this file is self-contained.
-/

/- NOTE on measurable-space assumptions:

   The action space `U` is a finite type. Mathematically, the only
   reasonable measurable-space structure on a finite type is the
   discrete σ-algebra (every subset measurable). However, Lean's
   instance resolution does not automatically synthesize
   `MeasurableSpace` from `Fintype`, so the measurable-space
   hypotheses must be declared explicitly.

   The hypotheses `[MeasurableSpace U]` and `[MeasurableSingletonClass U]`
   are load-bearing for the following reasons:
     - `Measure.dirac u` requires `MeasurableSpace U`
     - `Measure.dirac_apply` simplification requires `MeasurableSingletonClass U`
     - `Measure.pi` requires `MeasurableSpace` on each factor
     - `measurableSet_singleton` (used in `X_measurable`) requires
       `MeasurableSingletonClass`

   For any specific finite `U`, users instantiate both with the
   discrete structure via `measurableSpace_of_top` or by invoking
   `Fintype`-derived instances. Both instances exist and are
   automatic for any finite type the paper considers.
-/
variable {U : Type*} [Fintype U] [DecidableEq U] [Nonempty U]
  [MeasurableSpace U] [MeasurableSingletonClass U]

/-- The window-observation type. For the adversarial construction, the window
    is constant across blocks (always equal to w*), so we can fix it as a
    unit-like type. We use `Unit` to indicate "the adversarial construction
    presents the same window at every choice point". -/
abbrev Window : Type := Unit

/-- A stochastic forward-local policy. Because the adversarial construction
    forces the window to be w* at every choice point, the policy's action
    distribution at the choice point is fully determined by its behavior on
    a single window value. We represent this as a probability mass function
    on U. -/
structure StochPolicy (U : Type*) [Fintype U] where
  prob        : U → ℝ
  nonneg      : ∀ u, 0 ≤ prob u
  sums_to_one : ∑ u, prob u = 1

namespace StochPolicy

variable (π : StochPolicy U)

/-- The policy's action distribution as a discrete probability measure on U. -/
noncomputable def asMeasure : Measure U :=
  Measure.sum (fun u => (ENNReal.ofReal (π.prob u)) • Measure.dirac u)

/-- The `asMeasure` construction is a probability measure. -/
instance asMeasure_isProbability : IsProbabilityMeasure π.asMeasure := by
  have hsum : HasSum π.prob 1 := by
    simpa [π.sums_to_one] using
      (hasSum_sum_of_ne_finset_zero (s := Finset.univ) (f := π.prob) (by
        intro u hu
        exact False.elim (hu (Finset.mem_univ u))))
  simpa [StochPolicy.asMeasure] using
    (HasSum.isProbabilityMeasure_sum_dirac (d := fun u : U => u) π.nonneg hsum)
  /- TO PROVE: the sum-of-Diracs measure has total mass 1.
     Use `π.sums_to_one` together with `Measure.sum_apply`
     and `Measure.dirac_apply`. Standard Mathlib. -/

/-- The mass that the policy's measure assigns to a singleton equals
    the probability of that action. -/
lemma asMeasure_singleton (π : StochPolicy U) (u : U) :
    π.asMeasure {u} = ENNReal.ofReal (π.prob u) := by
  classical
  unfold StochPolicy.asMeasure
  rw [Measure.sum_apply _ (MeasurableSet.singleton u)]
  -- Goal: ∑' v, (ENNReal.ofReal (π.prob v) • Measure.dirac v) {u} = ENNReal.ofReal (π.prob u)
  simp only [Measure.smul_apply, Measure.dirac_apply' _ (MeasurableSet.singleton u),
             Set.indicator_apply, Set.mem_singleton_iff, smul_eq_mul]
  -- Only the term with v = u is nonzero
  rw [tsum_eq_single u (fun v hv => by simp [hv])]
  simp

end StochPolicy

/-- The admissible set for the adversarial block. By construction of the
    policy-indexed adversarial block, the admissible set is any set that
    excludes at least one action with probability ≥ 1/|U|. For the
    pigeonhole argument, we fix it as the complement of a specific
    "bad action" a*, chosen so that π assigns it probability ≥ 1/|U|. -/
structure AdversarialBlock (U : Type*) [Fintype U] (π : StochPolicy U) where
  badAction        : U
  badAction_heavy  : (1 : ℝ) / Fintype.card U ≤ π.prob badAction

/-- Construction: for any stochastic policy π on a finite action space
    with |U| ≥ 2, an adversarial block exists. This is the pigeonhole
    step that `accumulation_stochastic.lean` proves combinatorially. -/
noncomputable def pigeonholeBlock
    (π : StochPolicy U) (hU : 2 ≤ Fintype.card U) :
    AdversarialBlock U π := by
  classical
  have h_exists : ∃ u : U, (1 : ℝ) / Fintype.card U ≤ π.prob u := by
    by_contra h_none
    push_neg at h_none
    have hcard_pos : 0 < Fintype.card U := lt_of_lt_of_le (by decide : 0 < 2) hU
    have hcard_ne : (Fintype.card U : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hcard_pos)
    have hsum_lt : (∑ u, π.prob u) < 1 := by
      calc
        (∑ u, π.prob u) < ∑ u, (1 : ℝ) / Fintype.card U :=
          Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun u _ => h_none u)
        _ = 1 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          field_simp
    linarith [π.sums_to_one]
  exact ⟨h_exists.choose, h_exists.choose_spec⟩

/-! ## Section 2: Trajectory Space

The trajectory space for an N-block episode is the N-fold product of the
action space: one action per block (at the choice point). The reset and
silent phases are deterministic, so they do not contribute randomness.

Ω_N := U^N

This is a standard Mathlib finite product. The measure is the N-fold
product of π.asMeasure, which corresponds to the policy acting
independently at each block's choice point. This independence holds
because, by construction of the adversarial environment, the window at
each choice point is deterministically w* regardless of history.
-/

/-- The trajectory space for an N-block episode. -/
abbrev Ω (U : Type*) (N : ℕ) := Fin N → U

variable {N : ℕ}

/-- The trajectory measure: N-fold product of the policy's action
    distribution. -/
noncomputable def trajectoryMeasure
    (π : StochPolicy U) (N : ℕ) : Measure (Ω U N) :=
  Measure.pi (fun _ => π.asMeasure)

/-- The trajectory measure is a probability measure. -/
instance trajectoryMeasure_isProbability
    (π : StochPolicy U) (N : ℕ) :
    IsProbabilityMeasure (trajectoryMeasure π N) := by
  unfold trajectoryMeasure
  have : ∀ i : Fin N, IsProbabilityMeasure (π.asMeasure : Measure U) :=
    fun _ => inferInstance
  infer_instance

/-- The real-valued mass the trajectory measure assigns to a singleton
    trajectory equals the product of per-coordinate probabilities. -/
lemma trajectoryMeasure_real_singleton
    (π : StochPolicy U) (N : ℕ) (x : Ω U N) :
    (trajectoryMeasure π N).real {x} = ∏ i : Fin N, π.prob (x i) := by
  classical
  -- Rewrite {x} as a cylinder: Set.pi univ (fun i => {x i})
  have h_cyl : ({x} : Set (Ω U N)) = Set.pi Set.univ (fun i => {x i}) := by
    ext y
    constructor
    · rintro rfl
      intro i _
      exact Set.mem_singleton _
    · intro hy
      ext i
      exact hy i (Set.mem_univ i)
  -- Compute μ {x} = ∏ i, π.asMeasure {x i} via pi_pi
  have h_measure : (trajectoryMeasure π N) {x}
      = ∏ i : Fin N, π.asMeasure {x i} := by
    rw [h_cyl]
    exact MeasureTheory.Measure.pi_pi (fun _ => π.asMeasure)
      (fun i => ({x i} : Set U))
  -- Convert each factor via asMeasure_singleton, then take toReal
  rw [Measure.real, h_measure]
  rw [ENNReal.toReal_prod]
  congr 1
  funext i
  rw [StochPolicy.asMeasure_singleton]
  exact ENNReal.toReal_ofReal (π.nonneg _)

/-! ## Section 3: Filtration and Failure Indicators

The filtration F_k represents "information available after the first k
blocks." For the product space Ω = U^N, F_k is the σ-algebra generated
by the projections onto the first k coordinates.

The failure indicator X_k : Ω → ℝ is 1 if the action at block k lies in
the adversarial bad-action set (i.e., equals B.badAction), and 0 otherwise.
-/

variable (π : StochPolicy U)

/-- The filtration on the trajectory space. F_k = σ-algebra generated by
    the first k coordinates.

    INDEXING CHOICE: We use `Fin (N+1)` so that `F 0` is the trivial
    σ-algebra (no information before the first block) and `F N` is the
    full σ-algebra. This avoids the truncated-subtraction issue that
    arises with ℕ-indexed filtrations at k=0. -/
@[reducible]
noncomputable def F (N : ℕ) : Fin (N+1) → MeasurableSpace (Ω U N) :=
  fun k =>
    MeasurableSpace.generateFrom
      { S | ∃ (i : Fin N) (_ : i.val < k.val) (A : Set U),
              MeasurableSet A ∧ S = {ω | ω i ∈ A} }

/-- The filtration is monotone: F_j ≤ F_k for j ≤ k. -/
lemma F_mono (N : ℕ) : Monotone (F (U := U) N) := by
  intro j k hjk
  refine MeasurableSpace.generateFrom_mono ?_
  intro S hS
  rcases hS with ⟨i, hi, A, hA, rfl⟩
  exact ⟨i, lt_of_lt_of_le hi hjk, A, hA, rfl⟩
  /- TO PROVE: the generating sets are nested, so the generated σ-algebras
     are nested. -/

/-- The filtration is bounded above by the full σ-algebra on Ω. -/
lemma F_le_full (N : ℕ) (k : Fin (N+1)) :
    F (U := U) N k ≤ (MeasurableSpace.pi : MeasurableSpace (Ω U N)) := by
  refine MeasurableSpace.generateFrom_le ?_
  intro S hS
  obtain ⟨i, _, A, hA, rfl⟩ := hS
  exact MeasurableSet.preimage hA (measurable_pi_apply i)

/-- The failure indicator for block k: 1 if action at block k equals the
    adversarial bad action, 0 otherwise. -/
noncomputable def X (π : StochPolicy U) (B : AdversarialBlock U π)
    (k : Fin N) : Ω U N → ℝ :=
  fun ω => if ω k = B.badAction then 1 else 0

/-- The failure indicator is measurable with respect to F_{k+1}.
    In particular, X_k is F_{k+1}-measurable but not (in general)
    F_k-measurable. -/
lemma X_measurable
    (π : StochPolicy U) (B : AdversarialBlock U π) (k : Fin N) :
    Measurable (X (N := N) π B k) := by
  simpa [X] using measurable_of_finite (X (N := N) π B k)
  /- TO PROVE: X k is the composition of the k-th projection (measurable
     because F generates the product σ-algebra) with a measurable
     indicator function. Use `Measurable.indicator` or direct
     construction. -/

/-- The failure indicator is integrable under the trajectory measure. -/
lemma X_integrable
    (π : StochPolicy U) (B : AdversarialBlock U π) (k : Fin N) :
    Integrable (X π B k) (trajectoryMeasure π N) := by
  simpa using (MeasureTheory.Integrable.of_finite (μ := trajectoryMeasure π N) (f := X π B k))
  /- TO PROVE: X k is bounded (values in {0, 1}) and measurable on a
     probability space, hence integrable. Use `Integrable.of_bounded`
     or similar Mathlib lemma. -/

/-! ## Section 4: The Bridge Lemma and the Main Theorem

This is the load-bearing section. The bridge lemma identifies the
conditional expectation of X_k given F_k with the policy's per-action
probability on the bad action, almost surely. Because the product measure
is the policy's action distribution in each coordinate independently,
the conditional expectation of X_k given the history F_k is constant a.s.
and equal to π(badAction).

Once the bridge lemma is established, the main theorem follows by
linearity of expectation: each E[X_k] ≥ 1/|U|, so E[∑ X_k] ≥ N/|U|.
-/

/-- **Determined-by-prefix characterization.** A set `s` on the finite
    product `Ω = Fin N → U` is said to be *determined by the first k
    coordinates* if membership in `s` depends only on the values of
    those coordinates. -/
def DeterminedByPrefix (N : ℕ) (k : ℕ) (s : Set (Ω U N)) : Prop :=
  ∀ ω ω' : Ω U N, (∀ i : Fin N, i.val < k → ω i = ω' i) → (ω ∈ s ↔ ω' ∈ s)

/-- Bridge from F_k-measurability to the determined-by-prefix property.
    Every F_k-measurable set is determined by the first k coordinates;
    this is an σ-algebra induction on the generating cylinders. -/
lemma F_measurable_determined
    (N : ℕ) (k : Fin (N+1)) (s : Set (Ω U N))
    (hs : MeasurableSet[F (U := U) N k] s) :
    DeterminedByPrefix N k.val s := by
  induction hs with
  | basic s' hs_gen =>
    rcases hs_gen with ⟨i, hi, A, _, rfl⟩
    intro ω ω' h_eq
    simp only [Set.mem_setOf_eq]
    rw [h_eq i hi]
  | empty =>
    intro ω ω' _
    simp
  | compl s' _ ih =>
    intro ω ω' h_eq
    simp only [Set.mem_compl_iff]
    rw [ih ω ω' h_eq]
  | iUnion f _ ih =>
    intro ω ω' h_eq
    simp only [Set.mem_iUnion]
    exact exists_congr (fun j => ih j ω ω' h_eq)

/-! ## Section 5: The Product-Measure Independence Identity (Path B)

The load-bearing product-measure independence identity, verified via the
product-isomorphism approach. Uses `Fin.insertNthEquiv` from Mathlib to
establish the canonical product isomorphism
`(Fin (n+1) → U) ≃ U × (Fin n → U)` that separates a chosen coordinate
from the rest. This is the canonical measure-theoretic factorization via
Fubini on the discrete product space.

This file verifies the identity via Path B. The sibling file
`accumulation_stochastic_measure_pathA.lean` verifies the same identity
via fiber-partitioning with an explicit coordinate-update bijection. Both
files verify the same main theorem end-to-end, providing independent
machine-checked certificates of the same conclusion. -/

/-- The product equivalence on pi-types specialized to a constant family:
    given position `i : Fin (n+1)`, a function on `Fin (n+1)` is equivalent
    to a pair of its value at `i` and its restriction to the other
    coordinates. Built from Mathlib's `Fin.insertNthEquiv`. -/
def piSuccAboveEquiv (n : ℕ) (i : Fin (n+1)) :
    (Fin (n+1) → U) ≃ U × (Fin n → U) :=
  (Fin.insertNthEquiv (fun _ : Fin (n+1) => U) i).symm

/-- **Product-measure independence identity (product-isomorphism route).**
    For any set `s` determined by the first `k.val` coordinates, the
    integral of the failure indicator `X_k` restricted to `s` equals
    `π.prob B.badAction * μ.real(s)`.

    Uses `piSuccAboveEquiv N k` to separate the coordinate-k factor from
    the rest, `Fintype.sum_prod_type` to split the Cartesian sum into
    nested sums, `Fin.prod_univ_succAbove` to factor the trajectory-
    measure product at position k, and `π.sums_to_one` to close.

    Uses `Fin (N+1)` signature to align with `piSuccAboveEquiv N k` at
    the type level. The `setIntegral_X_eq` wrapper below case-splits on
    `N = 0` vs `N = N' + 1` to provide the standard `Fin N` interface. -/
lemma setIntegral_X_eq_of_determined_via_equiv
    (π : StochPolicy U) (B : AdversarialBlock U π) {N : ℕ} (k : Fin (N+1))
    (s : Set (Ω U (N+1)))
    (hs : DeterminedByPrefix (N+1) k.val s) :
    ∫ ω in s, X π B k ω ∂(trajectoryMeasure π (N+1))
      = (trajectoryMeasure π (N+1)).real s * π.prob B.badAction := by
  classical
  -- Step 1: reduce set integral to finite sum form
  have hs_meas : MeasurableSet s := MeasurableSet.of_discrete
  rw [← MeasureTheory.integral_indicator hs_meas]
  rw [MeasureTheory.integral_fintype]
  swap
  · exact (X_integrable π B k).indicator hs_meas
  simp_rw [Set.indicator_apply]
  simp only [X, smul_eq_mul]
  rw [show (fun x => (trajectoryMeasure π (N+1)).real {x} *
            (if x ∈ s then (if x k = B.badAction then (1:ℝ) else 0) else 0))
          = (fun x => if x ∈ s ∧ x k = B.badAction
                      then (trajectoryMeasure π (N+1)).real {x} else 0) from by
    funext x
    by_cases hxs : x ∈ s
    · by_cases hxk : x k = B.badAction
      · simp [hxs, hxk]
      · simp [hxs, hxk]
    · simp [hxs]]
  -- Goal: ∑ x, if (x ∈ s ∧ x k = bad) then μ.real{x} else 0
  --      = μ.real(s) * π.prob B.badAction
  -- Step 2: reindex the LHS sum via piSuccAboveEquiv
  let e := piSuccAboveEquiv (U := U) N k
  rw [← Equiv.sum_comp e.symm
        (fun x => if x ∈ s ∧ x k = B.badAction
                  then (trajectoryMeasure π (N+1)).real {x} else 0)]
  -- Step 3: convert μ.real(s) to sum form, apply same reindexing
  have h_rhs_sum : (trajectoryMeasure π (N+1)).real s
      = ∑ x : Ω U (N+1), if x ∈ s then (trajectoryMeasure π (N+1)).real {x} else 0 := by
    have hA : MeasurableSet {x : Ω U (N+1) | x ∈ s} := MeasurableSet.of_discrete
    have hs_setOf : s = {x | x ∈ s} := by ext; rfl
    rw [hs_setOf]
    have h1 : (trajectoryMeasure π (N+1)).real {x | x ∈ s}
        = ∫ _ω in {x | x ∈ s}, (1 : ℝ) ∂(trajectoryMeasure π (N+1)) := by
      simp [MeasureTheory.integral_const, Measure.real]
    rw [h1]
    rw [← MeasureTheory.integral_indicator hA]
    rw [MeasureTheory.integral_fintype]
    · congr 1
      funext x
      by_cases hxs : x ∈ s
      · simp [hxs]
      · simp [hxs]
    · exact (integrable_const (1 : ℝ)).indicator hA
  rw [h_rhs_sum]
  rw [Finset.sum_mul]
  rw [← Equiv.sum_comp e.symm
        (fun x => (if x ∈ s then (trajectoryMeasure π (N+1)).real {x} else 0)
                    * π.prob B.badAction)]
  -- Step 4: split Cartesian sums into nested sums
  rw [Fintype.sum_prod_type]
  conv_rhs => rw [Fintype.sum_prod_type]
  -- Step 5: expand singleton measures, split products at position k
  simp_rw [trajectoryMeasure_real_singleton]
  simp_rw [Fin.prod_univ_succAbove _ k]
  -- Step 6: unfold e.symm evaluations at coord k and at k.succAbove j
  -- First substitute the let-bound `e` to expose the Equiv structure
  show _ = _
  simp only [e, piSuccAboveEquiv, Equiv.symm_symm, Fin.insertNthEquiv_apply,
             Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  -- Goal now:
  --   ∑ u, ∑ rest, if (insertNthEquiv _ k (u, rest) ∈ s ∧ u = B.badAction)
  --               then π.prob u * ∏ j, π.prob (rest j) else 0
  -- = ∑ u, ∑ rest, (if insertNthEquiv _ k (u, rest) ∈ s
  --                then π.prob u * ∏ j, π.prob (rest j) else 0) * π.prob B.badAction
  -- Step 7: close using DeterminedByPrefix and π.sums_to_one
  -- Key observation: insertNthEquiv _ k (u, rest) ∈ s depends only on rest,
  -- not on u (since s is determined by coords < k, and u is at coord k).
  -- Claim: for all u rest, (insertNth k u rest ∈ s) ↔ (insertNth k B.badAction rest ∈ s)
  have h_indep : ∀ (u : U) (rest : Fin N → U),
      (Fin.insertNth (α := fun _ => U) k u rest ∈ s)
        ↔ (Fin.insertNth (α := fun _ => U) k B.badAction rest ∈ s) := by
    intro u rest
    apply hs
    intro i hi
    have hik : i ≠ k := by
      intro h
      rw [h] at hi
      exact absurd hi (lt_irrefl _)
    -- Use i.exists_succAbove_eq with hik to get ⟨m, k.succAbove m = i⟩
    obtain ⟨m, hm⟩ := i.exists_succAbove_eq hik
    rw [← hm]
    rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]
  -- Rewrite the indicators using h_indep. Use direct rewrites via Finset.sum_congr
  -- rather than conv blocks to avoid conv-ext issues.
  have h_lhs_subst : (∑ u : U, ∑ rest : Fin N → U,
        if (Fin.insertNthEquiv (fun _ : Fin (N+1) => U) k) (u, rest) ∈ s ∧ u = B.badAction
        then π.prob u * ∏ j, π.prob (rest j) else 0)
      = ∑ u : U, ∑ rest : Fin N → U,
        if (Fin.insertNthEquiv (fun _ : Fin (N+1) => U) k) (B.badAction, rest) ∈ s ∧ u = B.badAction
        then π.prob u * ∏ j, π.prob (rest j) else 0 := by
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro rest _
    congr 1
    simp only [eq_iff_iff]
    exact and_congr_left (fun _ => h_indep u rest)
  have h_rhs_subst : (∑ u : U, ∑ rest : Fin N → U,
        (if (Fin.insertNthEquiv (fun _ : Fin (N+1) => U) k) (u, rest) ∈ s
         then π.prob u * ∏ j, π.prob (rest j) else 0) * π.prob B.badAction)
      = ∑ u : U, ∑ rest : Fin N → U,
        (if (Fin.insertNthEquiv (fun _ : Fin (N+1) => U) k) (B.badAction, rest) ∈ s
         then π.prob u * ∏ j, π.prob (rest j) else 0) * π.prob B.badAction := by
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro rest _
    congr 2
    simp only [eq_iff_iff]
    exact h_indep u rest
  rw [h_lhs_subst, h_rhs_subst]
  -- Now indicators are identical and u-independent; swap sums
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro rest _
  by_cases h_cond : (Fin.insertNthEquiv (fun _ : Fin (N+1) => U) k) (B.badAction, rest) ∈ s
  · -- Indicator = true
    simp only [h_cond, if_true, true_and]
    -- LHS: ∑ u, if u = B.badAction then π.prob u * ∏_rest else 0
    rw [Finset.sum_ite_eq' Finset.univ B.badAction (fun u => π.prob u * ∏ j, π.prob (rest j))]
    simp only [Finset.mem_univ, if_true]
    -- Goal: π.prob B.badAction * ∏ j, π.prob (rest j)
    --     = ∑ x, (π.prob x * ∏ j, π.prob (rest j)) * π.prob B.badAction
    -- Factor π.prob B.badAction out of outer sum, then ∏_rest out of inner sum
    rw [← Finset.sum_mul]
    rw [← Finset.sum_mul]
    rw [π.sums_to_one]
    ring
  · -- Indicator = false, both sides 0
    simp only [h_cond, if_false, false_and]
    simp

/-- Helper: for any F_k-measurable set s, the integral of X_k restricted
    to s equals π.prob B.badAction times μ.real(s). This is obtained by
    composing F_measurable_determined with the Path B product-measure
    identity, case-splitting on `N` to align the indexing signature. -/
lemma setIntegral_X_eq
    (π : StochPolicy U) (B : AdversarialBlock U π) (k : Fin N)
    (s : Set (Ω U N))
    (hs : MeasurableSet[F (U := U) N ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩] s) :
    ∫ ω in s, X π B k ω ∂(trajectoryMeasure π N)
      = (trajectoryMeasure π N).real s * π.prob B.badAction := by
  have hdet : DeterminedByPrefix N k.val s :=
    F_measurable_determined N ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩ s hs
  -- Case-split on N to apply the Path B helper with its Fin (M+1) signature
  match N, k, s, hdet with
  | 0, k, _, _ => exact k.elim0
  | M + 1, k, s, hdet => exact setIntegral_X_eq_of_determined_via_equiv π B k s hdet

/-- **Bridge lemma.** The conditional expectation of the block-k failure
    indicator given the first-k-blocks history is almost surely equal to
    the policy's probability on the bad action, which is at least 1/|U|. -/
lemma condExp_X_ge
    (π : StochPolicy U) (B : AdversarialBlock U π) (k : Fin N) :
    ∀ᵐ ω ∂(trajectoryMeasure π N),
      (1 : ℝ) / Fintype.card U
        ≤ (trajectoryMeasure π N)[X π B k |
                (F (U := U) N ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩)] ω := by
  -- Strategy: show condExp equals the constant π.prob B.badAction a.e.,
  -- then invoke B.badAction_heavy.
  have hm : F (U := U) N ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩
            ≤ MeasurableSpace.pi :=
    F_le_full (U := U) N ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩
  -- The constant function c : Ω → ℝ, c ω = π.prob B.badAction
  set c : ℝ := π.prob B.badAction with hc_def
  -- Step 1: show condExp equals fun _ => c, a.e.
  have h_ae_eq : (fun _ : Ω U N => c)
      =ᵐ[trajectoryMeasure π N]
      (trajectoryMeasure π N)[X π B k |
        F (U := U) N ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩] := by
    apply MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hm
    · exact X_integrable π B k
    · intro s hs _
      exact (integrable_const c).integrableOn
    · intro s hs _hfin
      -- Goal: ∫ ω in s, c ∂μ = ∫ ω in s, X_k ∂μ
      rw [MeasureTheory.integral_const, setIntegral_X_eq π B k s hs]
      simp [Measure.real, hc_def, mul_comm]
    · exact aestronglyMeasurable_const
  -- Step 2: conclude from c ≥ 1/|U| and the a.e. equality
  filter_upwards [h_ae_eq] with ω hω
  rw [← hω]
  exact B.badAction_heavy

/-- **Main theorem.** For every stochastic forward-local policy π with
    |U| ≥ 2, every adversarial block, and every N, the expected cumulative
    inconsistency under the trajectory measure is at least N/|U|. -/
theorem accumulation_stochastic_measure
    (π : StochPolicy U) (hU : 2 ≤ Fintype.card U)
    (B : AdversarialBlock U π) (N : ℕ) :
    (N : ℝ) / Fintype.card U ≤
      ∫ ω, (∑ k : Fin N, X π B k ω) ∂(trajectoryMeasure π N) := by
  have h_each : ∀ k : Fin N,
      (1 : ℝ) / Fintype.card U ≤
        ∫ ω, X π B k ω ∂(trajectoryMeasure π N) := by
    intro k
    have hm : F (U := U) N ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩
              ≤ MeasurableSpace.pi :=
      F_le_full (U := U) N ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩
    have h_cond_integrable :
        Integrable ((trajectoryMeasure π N)[X π B k |
          F (U := U) N ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩])
          (trajectoryMeasure π N) :=
      integrable_condExp
    calc
      (1 : ℝ) / Fintype.card U
          = ∫ _ω, (1 : ℝ) / Fintype.card U ∂(trajectoryMeasure π N) := by
              simp
      _ ≤ ∫ ω, (trajectoryMeasure π N)[X π B k |
          F (U := U) N ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩] ω
          ∂(trajectoryMeasure π N) := by
            apply MeasureTheory.integral_mono_ae
            · exact integrable_const _
            · exact h_cond_integrable
            · exact condExp_X_ge (π := π) (B := B) (k := k)
      _ = ∫ ω, X π B k ω ∂(trajectoryMeasure π N) := by
            exact MeasureTheory.integral_condExp hm
  calc
    (N : ℝ) / Fintype.card U
        = ∑ _k : Fin N, (1 : ℝ) / Fintype.card U := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
    _ ≤ ∑ k : Fin N, ∫ ω, X π B k ω ∂(trajectoryMeasure π N) := by
          exact Finset.sum_le_sum (fun k _ => h_each k)
    _ = ∫ ω, (∑ k : Fin N, X π B k ω) ∂(trajectoryMeasure π N) := by
          rw [MeasureTheory.integral_finset_sum]
          intro k _
          exact X_integrable π B k
  /- TO PROVE (bookkeeping step, follows the pattern in the GPT snippet):

     1. Apply `integral_finset_sum` to pull the sum out:
          ∫ ∑ X_k = ∑ ∫ X_k
        (uses X_integrable for each k)

     2. For each k, apply the tower property via `integral_condExp`:
          ∫ X_k dμ = ∫ μ[X_k | F_k] dμ

     3. Apply `integral_mono_ae` using `condExp_X_ge`:
          ∫ μ[X_k | F_k] dμ ≥ ∫ (1/|U|) dμ = 1/|U|

     4. Sum over k ∈ Fin N:
          ∑ 1/|U| = N/|U|

     Lemma names that may need adjustment (Mathlib drift):
     - `integral_finset_sum` vs `Finset.integral_sum`
     - `integral_condExp` vs `integral_condexp`
     - `integral_mono_ae` vs `integral_mono_of_le`

     If any name fails, grep Mathlib for a matching signature. -/

end InconsistencyAccumulation
