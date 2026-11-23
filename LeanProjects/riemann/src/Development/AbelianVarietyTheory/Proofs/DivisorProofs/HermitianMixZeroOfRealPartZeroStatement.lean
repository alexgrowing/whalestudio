import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMixZeroOfRealPartZero
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
theorem _root_.GlobalTheory.T.hermitian_mix_zero_of_real_part_zero : ∀ (d : ℕ) (A M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ), A.IsHermitian → (∀ ξ : V (d + 1), (∑ j, ∑ l, ξ j * M j l * starRingEnd ℂ (ξ l)).re = 0) → mix d A M = 0 := by
  first | exact @GlobalTheory.MixDens.mix_eq_zero_of_re_form_eq_zero | exact GlobalTheory.MixDens.mix_eq_zero_of_re_form_eq_zero | (intros; apply GlobalTheory.MixDens.mix_eq_zero_of_re_form_eq_zero <;> assumption)
