import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableMeromorphicContinuation
import Mathlib
open MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_meromorphic_continuation : ∀ {X : Type} [MeasurableSpace X] (Eis : ℂ → X → ℂ) (c : ℝ),
    (∀ s₀ : ℂ, ∃ (k : ℕ) (U : Set ℂ) (Hol : ℂ → X → ℂ), U ∈ 𝓝 s₀ ∧
      (∀ s ∈ U, s ≠ s₀ → ∀ g, Hol s g = (s - s₀) ^ k * Eis s g) ∧ ∀ g, DifferentiableOn ℂ (Hol · g) U) →
    (∀ s : ℂ, c < s.re → Measurable (Eis s)) → ∀ s₀ : ℂ, ∀ᶠ s in 𝓝[≠] s₀, Measurable (Eis s) := by
  first | exact @GlobalTheory.measurable_eventually_of_meromorphic_family | exact GlobalTheory.measurable_eventually_of_meromorphic_family | (intros; apply GlobalTheory.measurable_eventually_of_meromorphic_family <;> assumption)
