import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArchimedeanValueBound
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_value_bound : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (d : ℕ), IsArithVar (mCoordIdeal y) d → Birational y → ∀ (A : HermLine ι) (q m : ℕ) (u : Ω), IsSmoothHerm A → 0 < q → 0 < m → (m : Ω) * u ^ q ∈ chartLatNm y A.a q → ∃ C : ℝ, ∀ z ∈ ptsOver ℂ (mCoordIdeal y), ∀ val : ℂ, HasVal y A.a u z val → ‖val‖ ≤ Real.exp C * A.h z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ArchBd.section_bound | exact GlobalTheory.CompanionTheory.Ar.ArchBd.section_bound | (intros; apply GlobalTheory.CompanionTheory.Ar.ArchBd.section_bound <;> assumption)
