import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexHessianAdjugateDivergenceFree
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
theorem _root_.GlobalTheory.T.complex_hessian_adjugate_divergence_free : ∀ (D : ℕ) (u : V D → ℂ) (z : V D), ContDiffAt ℝ 3 u z → (∀ l j : Fin D, ContDiffAt ℝ 1 (fun x => (cHess D u x).adjugate l j) z) ∧ ∀ j : Fin D, ∑ l, dbar (fun x => (cHess D u x).adjugate l j) z (EuclideanSpace.single l 1) = 0 := by
  first | exact @GlobalTheory.HessPiola.cHess_adjugate_piola | exact GlobalTheory.HessPiola.cHess_adjugate_piola | (intros; apply GlobalTheory.HessPiola.cHess_adjugate_piola <;> assumption)
