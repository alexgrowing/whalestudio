import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterExtLocal
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem ptsIntegral_congr_and_homog :
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι ℤ)) (e : ℕ) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ), (∀ g g' : ((Σ k, ι k) → ℂ) → ℝ, (∀ z ∈ mcPts P, g z = g' z) → ptsIntegral P φ g = ptsIntegral P φ g') ∧ ∀ (c : ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ), ptsIntegral P φ (fun z => c * g z) = c * ptsIntegral P φ g := by
  classical
  intro K _ _ ι _ P e φ
  refine ⟨fun g g' hg => ?_, fun c g => ?_⟩
  · exact (ReciprocityTheory.ChartRestriction.G.Geo.ptsLocal K ι P e 0 φ φ g g' (fun _ _ _ => rfl) hg).2
  · unfold ptsIntegral
    split_ifs with h
    · unfold ReciprocityTheory.ChartRestriction.G.Geo.ptsIntegralAt
      rw [← MeasureTheory.integral_const_mul]
      congr 1
      funext y
      have : ∀ w, ReciprocityTheory.ChartRestriction.G.Geo.sheetDensity P h.choose φ (fun z => c * g z) y w =
          c * ReciprocityTheory.ChartRestriction.G.Geo.sheetDensity P h.choose φ g y w := by
        intro w
        unfold ReciprocityTheory.ChartRestriction.G.Geo.sheetDensity
        split_ifs <;> ring
      simp only [this]
      rw [← mul_finsum_mem]
    · simp

end GlobalTheory.CompanionTheory.Ar.Num
