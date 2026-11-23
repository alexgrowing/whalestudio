import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionMetricSegmentPolynomial
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.self_intersection_metric_segment_polynomial : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L : HermLB p) (u : SmFn p) (a a' : ℝ), L.IsSelfInter a → (up L u).IsSelfInter a' → ∃ s : Polynomial ℝ, s.eval 0 = a ∧ s.eval 1 = a' ∧ ∀ t : ℚ, ((D : ℝ) + 1) / 2 * chInt (up L (u.smul t)) D u.u = s.derivative.eval (t : ℝ) := by
  first | exact @GlobalTheory.HSAmp.SelfPoly.selfInter_poly | exact GlobalTheory.HSAmp.SelfPoly.selfInter_poly | (intros; apply GlobalTheory.HSAmp.SelfPoly.selfInter_poly <;> assumption)
