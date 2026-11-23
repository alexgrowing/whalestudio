import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValuationCoordsComplexPoint
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
open ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_coords_complex_point : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (w : (Σ k, ι k) → ℂ), w ∈ Small.ptsOver ℂ (mCoordIdeal y) → ∃ (W : Subring Ω) (φ : W →+* ℂ), (∀ a : W, φ a ≠ 0 → IsUnit a) ∧ (∀ (k : K) (c e : ι k), w ⟨k, c⟩ ≠ 0 → ∃ h : y ⟨k, e⟩ / y ⟨k, c⟩ ∈ W, φ ⟨_, h⟩ * w ⟨k, c⟩ = w ⟨k, e⟩) ∧ ∀ (a : K → ℤ) (s : Ω) (v : ℂ) (C : ∀ k, ι k), Small.HasVal y a s w v → (∀ k, w ⟨k, C k⟩ ≠ 0) → ∃ h : s * ∏ k, y ⟨k, C k⟩ ^ (-a k) ∈ W, φ ⟨_, h⟩ * ∏ k, w ⟨k, C k⟩ ^ a k = v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocVal.exists_locRing_val | exact GlobalTheory.CompanionTheory.Ar.LocVal.exists_locRing_val | (intros; apply GlobalTheory.CompanionTheory.Ar.LocVal.exists_locRing_val <;> assumption)
