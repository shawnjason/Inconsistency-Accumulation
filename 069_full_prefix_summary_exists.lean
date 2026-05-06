-- ID 069: Full-Prefix Summary Non-Vacuity
--
-- Catalog ID 69 (Inconsistency Accumulation paper, Remark 2 in Section 6).
-- Companion to Proposition 1 (Summary Sufficiency, ID 67).
--
-- Statement: in the finite-horizon, finite-action setting where extendability
-- is decidable, the full prefix itself is an extendability-preserving
-- summary. Specifically, the identity map S = Prefix together with the
-- direct extendability decoder D(p, u) = ext(p, u) trivially satisfies the
-- extendability-preservation property. The summary is typically large rather
-- than compact, but its existence establishes that Proposition 1 is a
-- genuine positive existence claim rather than a vacuous one. The point of
-- Summary Sufficiency is the architectural separation, not that compact
-- summaries always exist.
--
-- Corresponds to Remark 2 of:
--   "Inconsistency Accumulation in Forward-Local Sequential Policies:
--    A Lower Bound under Delayed Constraints"
--
-- Shawn Kevin Jason

import Mathlib.Tactic

/-- An extendability-preserving summary: a state space S, an initial state,
    a transition map (`step`), and a decoder that determines whether a
    candidate next action preserves extendability from the current summary
    state. -/
structure ExtendabilityPreservingSummary
    (Prefix Action : Type)
    (ext : Prefix → Action → Prop) where
  S          : Type
  s0         : S
  step       : S → Action → S
  decode     : S → Action → Prop
  σ          : Prefix → S
  decode_ok  : ∀ (p : Prefix) (u : Action), decode (σ p) u ↔ ext p u

/-- Full-prefix summary non-vacuity: for any prefix space and any extendability
    predicate, the identity-map summary (S := Prefix, σ := id, decode := ext)
    is an extendability-preserving summary. The full prefix itself is a valid
    summary, establishing that Proposition 1 is non-vacuous. -/
theorem full_prefix_summary_exists
    (Prefix Action : Type)
    (ext : Prefix → Action → Prop)
    (p0 : Prefix)
    (step : Prefix → Action → Prefix) :
    ∃ _ : ExtendabilityPreservingSummary Prefix Action ext, True := by
  refine ⟨{
    S         := Prefix
    s0        := p0
    step      := step
    decode    := ext
    σ         := id
    decode_ok := fun _ _ => Iff.rfl
  }, trivial⟩