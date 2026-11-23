import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HeightLowerBoundChartNorm
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_lower_bound_chart_norm : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (d : ℕ), IsArithVar (mCoordIdeal y) d → Birational y → ∀ (a : K → ℤ) (u : Ω) (q m : ℕ), 0 < q → 0 < m → (m : Ω) * u ^ q ∈ chartLatNm y a q → ∀ (φ : ((Σ k, ι k) → ℂ) → ℝ) (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L (mCoordIdeal y), ∀ val : L, val ≠ 0 → HasVal y a u w val → (Module.finrank ℚ L : ℝ)⁻¹ * (∑ σ : L →+* ℂ, (φ (fun p => σ (w p)) - Real.log ‖σ val‖)) - Real.log m / q ≤ ptHt (fun k => (a k : ℝ)) φ L w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ht.SecLow.height_ge_of_section | exact GlobalTheory.CompanionTheory.Ar.Ht.SecLow.height_ge_of_section | (intros; apply GlobalTheory.CompanionTheory.Ar.Ht.SecLow.height_ge_of_section <;> assumption)
