import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeromorphicIdentityContinuation
import Mathlib
open MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.meromorphic_identity_continuation : ∀ (f₁ f₂ : ℂ → ℂ) (c : ℝ),
    (∀ s₀ : ℂ, ∃ (k : ℕ) (U : Set ℂ) (Hol : ℂ → ℂ), U ∈ 𝓝 s₀ ∧ (∀ s ∈ U, s ≠ s₀ → Hol s = (s - s₀) ^ k * f₁ s) ∧
      DifferentiableOn ℂ Hol U) →
    (∀ s₀ : ℂ, ∃ (k : ℕ) (U : Set ℂ) (Hol : ℂ → ℂ), U ∈ 𝓝 s₀ ∧ (∀ s ∈ U, s ≠ s₀ → Hol s = (s - s₀) ^ k * f₂ s) ∧
      DifferentiableOn ℂ Hol U) →
    (∀ s : ℂ, c < s.re → f₁ s = f₂ s) → ∀ s₀ : ℂ, ∀ᶠ s in 𝓝[≠] s₀, f₁ s = f₂ s := by
  first | exact @GlobalTheory.identity_of_localForm_halfPlane | exact GlobalTheory.identity_of_localForm_halfPlane | (intros; apply GlobalTheory.identity_of_localForm_halfPlane <;> assumption)
