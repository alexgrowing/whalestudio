import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAngleFormReEq
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dbar_angleForm_re_eq : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] (n : ℕ) (a a' : E → ℝ) (q : E → ℂ) (ξ z : E), ContDiffAt ℝ 2 a z → ContDiffAt ℝ 2 a' z → ContDiffAt ℝ 2 q z → 0 < a z → 0 < a' z → (dbar (angleForm n a a' q ξ) z ξ).re = (n + 1) * (‖q z‖ ^ 2 / (a z * a' z)) ^ n * ((‖del q z ξ - q z * del (fun x => (Real.log (a' x) : ℂ)) z ξ‖ ^ 2 - ‖dbar q z ξ - q z * dbar (fun x => (Real.log (a x) : ℂ)) z ξ‖ ^ 2) / (a z * a' z)) + (‖q z‖ ^ 2 / (a z * a' z)) ^ (n + 1) * ((leviForm (fun x => Real.log (a x)) z ξ ξ).re - (leviForm (fun x => Real.log (a' x)) z ξ ξ).re) := by
  first | exact @GlobalTheory.CurveDens.re_dbar_angleForm | exact GlobalTheory.CurveDens.re_dbar_angleForm | (intros; apply GlobalTheory.CurveDens.re_dbar_angleForm <;> assumption)
