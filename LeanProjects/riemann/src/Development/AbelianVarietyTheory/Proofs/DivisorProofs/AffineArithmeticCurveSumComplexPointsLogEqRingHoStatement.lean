import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineArithmeticCurveSumComplexPointsLogEqRingHo
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineArithmeticCurve_sum_complexPoints_log_eq_ringHoms : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsAffine Y] (q : Y ⟶ Sp k), IsArithVar q 0 → ∀ b : Γ(Y, ⊤), ∑ᶠ σ : k →+* ℂ, ∑ᶠ y : CxPts q σ, Real.log ‖ratVal (algebraMap Γ(Y, ⊤) Y.functionField b) y‖ = ∑ᶠ τ : Γ(Y, ⊤) →+* ℂ, Real.log ‖τ b‖ := by
  first | exact @GlobalTheory.AffCurveSum.main | exact GlobalTheory.AffCurveSum.main | (intros; apply GlobalTheory.AffCurveSum.main <;> assumption)
