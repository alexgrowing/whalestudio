import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionTraceSubmatrixConnection
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
theorem _root_.GlobalTheory.T.extension_trace_submatrix_connection : ∀ {N : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] (H : E → Matrix (Fin N) (Fin N) ℂ) (p : E) (i : Fin N), MContDiffAt 2 H p → (∀ᶠ v in 𝓝 p, (H v).PosDef) → H p = 1 → ∀ ξ η : E, extTrace (fun v => (H v).submatrix (emb i) (emb i)) p ξ η = kappa * ∑ a ∈ Finset.Iio i, conn H p ξ i a * starRingEnd ℂ (conn H p η i a) := by
  first | exact @GlobalTheory.StepTrace.extTrace_step_eq_sum | exact GlobalTheory.StepTrace.extTrace_step_eq_sum | (intros; apply GlobalTheory.StepTrace.extTrace_step_eq_sum <;> assumption)
