import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AngleFormDbarHermitian
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.angle_form_dbar_hermitian : ∀ (D n : ℕ) (a a' : V D → ℝ) (q : V D → ℂ) (z ξ : V D), ContDiffAt ℝ 2 a z → ContDiffAt ℝ 2 a' z → ContDiffAt ℝ 2 q z → 0 < a z → 0 < a' z → ∑ j, ∑ l, ξ j * dbar (CurveDens.angleForm n a a' q (EuclideanSpace.single j 1)) z (EuclideanSpace.single l 1) * starRingEnd ℂ (ξ l) = dbar (CurveDens.angleForm n a a' q ξ) z ξ := by
  first | exact @GlobalTheory.CurveDens.sum_dbar_angleForm_single | exact GlobalTheory.CurveDens.sum_dbar_angleForm_single | (intros; apply GlobalTheory.CurveDens.sum_dbar_angleForm_single <;> assumption)
