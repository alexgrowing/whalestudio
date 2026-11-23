import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetTriangularConjugateEqDiagonalRatio
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernOneEqNegDdcLogDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernDensDetWeightEqNegLeviLog
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetBlockChangeOfBasisViaTwoFamiliesImplicit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.LminorMapConj
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_triangular_conjugate_eq_diagonal_ratio : ∀ {m : ℕ} (n : Low m → ℂ) (T : Matrix (Fin m) (Fin m) ℂ), (∀ a c : Fin m, c < a → T a c = 0) → IsUnit T.det → (Matrix.of fun s t : Low m => (T⁻¹ * (uni n)⁻¹) s.1.1 t.1.1 * T t.1.2 s.1.2).det = ∏ s : Low m, T s.1.2 s.1.2 / T s.1.1 s.1.1 := by
  first | exact @GlobalTheory.FlagFibre.det_lowConj | exact GlobalTheory.FlagFibre.det_lowConj | (intros; apply GlobalTheory.FlagFibre.det_lowConj <;> assumption)
