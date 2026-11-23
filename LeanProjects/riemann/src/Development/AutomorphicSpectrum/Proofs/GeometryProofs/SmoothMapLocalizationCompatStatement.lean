import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothMapLocalizationCompat
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_map_localization_compat : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω₀] [CharZero Ω] [Algebra Ω₀ Ω] (A₀ : Subalgebra ℤ Ω₀)
    (A₁ : Subalgebra ℤ Ω) (φ : A₀ →+* A₁), (∀ a, ((φ a : A₁) : Ω) = algebraMap Ω₀ Ω a) → φ.Smooth →
    ∀ h : Ω₀, h ∈ Algebra.adjoin ℚ (A₀ : Set Ω₀) → h ≠ 0 → ∀ (S : Subalgebra ℚ Ω₀) (T : Subalgebra ℚ Ω),
      S = Algebra.adjoin ℚ (insert h⁻¹ (A₀ : Set Ω₀)) →
      T = Algebra.adjoin ℚ (insert (algebraMap Ω₀ Ω h)⁻¹ (A₁ : Set Ω)) →
      ∃ ψ : S →+* T, (∀ s, ((ψ s : T) : Ω) = algebraMap Ω₀ Ω s) ∧ ψ.Smooth := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocalisedSmooth.smooth_localised | exact GlobalTheory.CompanionTheory.Ar.LocalisedSmooth.smooth_localised | (intros; apply GlobalTheory.CompanionTheory.Ar.LocalisedSmooth.smooth_localised <;> assumption)
