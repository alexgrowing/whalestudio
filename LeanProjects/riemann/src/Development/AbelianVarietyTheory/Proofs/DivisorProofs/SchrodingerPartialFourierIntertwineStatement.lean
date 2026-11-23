import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPartialFourierIntertwine
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodinger_partial_fourier_intertwine : ∀ {V U : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U]
    (P : V → V → ℝ), GlobalTheory.ArchUniq.IsPairing P → ∀ (Λ₁ Λ₂ : U →L[ℝ] V) (φ : SchwartzMap U ℂ) (f₀ : SchwartzMap V ℂ),
    ∃ f : SchwartzMap V ℂ, ∀ (ℓ : SchwartzMap V ℂ →L[ℂ] ℂ) (ξ : U),
      (∀ (s : U) (g : SchwartzMap V ℂ), ⇑g = GlobalTheory.ArchUniq.schrF P (Λ₁ s, Λ₂ s) ⇑f₀ →
        ℓ g = Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ s ξ : ℝ) : ℂ)) * ℓ f₀) →
      ℓ f = φ ξ * ℓ f₀ := by
  first | exact @GlobalTheory.SchrPairing.exists_multiplier | exact GlobalTheory.SchrPairing.exists_multiplier | (intros; apply GlobalTheory.SchrPairing.exists_multiplier <;> assumption)
