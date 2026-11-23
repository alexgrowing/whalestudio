import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LogIntegralCongrSmul
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_integral_congr_smul : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι ℤ)) (e : ℕ) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ), (∀ g g' : ((Σ k, ι k) → ℂ) → ℝ, (∀ z ∈ mcPts P, g z = g' z) → ptsIntegral P φ g = ptsIntegral P φ g') ∧ ∀ (c : ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ), ptsIntegral P φ (fun z => c * g z) = c * ptsIntegral P φ g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.ptsIntegral_congr_and_homog | exact GlobalTheory.CompanionTheory.Ar.Num.ptsIntegral_congr_and_homog | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.ptsIntegral_congr_and_homog <;> assumption)
