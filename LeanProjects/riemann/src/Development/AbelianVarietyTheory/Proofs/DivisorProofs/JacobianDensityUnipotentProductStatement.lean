import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacobianDensityUnipotentProduct
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
theorem _root_.GlobalTheory.T.jacobian_density_unipotent_product : ∀ {m : ℕ} (G : Matrix (Fin m) (Fin m) ℂ), G.PosDef → ∀ (n : Low m → ℂ) (T : Matrix (Fin m) (Fin m) ℂ), (∀ a c : Fin m, c < a → T a c = 0) → chg T (chg (uni n) G) = 1 → ∏ s : Low m, ‖T s.1.2 s.1.2 / T s.1.1 s.1.1‖ ^ 2 = jacDens G n := by
  first | exact @GlobalTheory.TriJacDens.prod_diag_eq_jacDens | exact GlobalTheory.TriJacDens.prod_diag_eq_jacDens | (intros; apply GlobalTheory.TriJacDens.prod_diag_eq_jacDens <;> assumption)
