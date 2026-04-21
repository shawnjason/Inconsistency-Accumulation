/-
# Measure-Theoretic Stochastic Accumulation — Architecture File

This file is the target for the measure-theoretic formalization of
Theorem 1's stochastic clause in the paper
"Inconsistency Accumulation in Forward-Local Sequential Policies:
 A Lower Bound under Delayed Constraints."

## Purpose

The previously-verified file `accumulation_stochastic.lean` proves the
stochastic lower bound on `E[I_N]` in finite-combinatorial form:
it works over `Finset` sums and does not invoke Mathlib's measure
theory. That formalization suffices for the combinatorial argument
but leaves the paper's §5 tower-property argument (which proves the
bound for arbitrary trajectory distributions induced by a forward-local
policy) formally un-checked.

This file closes that gap. It constructs:
- a trajectory probability space (Ω, 𝓕, μ) induced by running a
  stochastic forward-local policy π in the paper's adversarial
  environment
- a filtration F_k representing "information available after k complete
  blocks"
- per-block failure indicators X_k, with measurability
- a bridge lemma identifying μ[X_k | F_{k-1}] with the policy's
  per-window failure probability from the combinatorial file
- the main theorem: E_μ[∑ X_k] ≥ N / |U|

## Structure

The file is organized in four sections:
1. Basic objects (action space, window, policy, block)
2. Trajectory space construction (Ω, kernels, μ, filtration)
3. Failure indicators and measurability
4. Bridge lemma and main theorem

Proofs are marked `sorry` and annotated with what each sorry needs to
establish. The order in which to fill them is specified in the
companion markdown file.

## Notes for the implementer

- Mathlib namespaces assumed: `MeasureTheory`, `ProbabilityTheory`,
  `ProbabilityTheory.Kernel`
- Type universes are handled implicitly; add explicit universes if
  elaboration fails
- The bridge lemma (section 4) is the load-bearing step; every other
  sorry is bookkeeping around it
- This file DEPENDS on `accumulation_stochastic.lean` being importable.
  If imports fail, either restate the combinatorial lemma locally
  or arrange the repo so both files live in the same namespace.

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

/-- Helper: for any F_k-measurable set s, the integral of X_k restricted
    to s equals π.prob B.badAction times μ.real(s). This is the
    "independence of X_k from the first-k-coordinates σ-algebra"
    statement, proved via the finite-space route. -/
lemma setIntegral_X_eq
    (π : StochPolicy U) (B : AdversarialBlock U π) (k : Fin N)
    (s : Set (Ω U N))
    (hs : MeasurableSet[F (U := U) N ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩] s) :
    ∫ ω in s, X π B k ω ∂(trajectoryMeasure π N)
      = (trajectoryMeasure π N).real s * π.prob B.badAction := by
  sorry

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
