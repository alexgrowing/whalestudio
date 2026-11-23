import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdbarLogDetSubmatrixCurvature
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
theorem _root_.GlobalTheory.T.ddbar_log_det_submatrix_curvature : ∀ {N : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] (H : E → Matrix (Fin N) (Fin N) ℂ) (p : E) (i : Fin N), MContDiffAt 2 H p → (∀ᶠ v in 𝓝 p, (H v).PosDef) → H p = 1 → ∀ ξ η : E, ddbar (fun v => ((-Real.log (quotGram ((H v).submatrix (emb i) (emb i))).det.re : ℝ) : ℂ)) p ξ η = curv H p ξ η i i + ∑ a ∈ Finset.Iio i, conn H p ξ i a * starRingEnd ℂ (conn H p η i a) - ∑ c ∈ Finset.Ioi i, conn H p ξ c i * starRingEnd ℂ (conn H p η c i) := by
  first | exact @GlobalTheory.GradedLine.ddbar_neg_log_quotGram_emb | exact GlobalTheory.GradedLine.ddbar_neg_log_quotGram_emb | (intros; apply GlobalTheory.GradedLine.ddbar_neg_log_quotGram_emb <;> assumption)
