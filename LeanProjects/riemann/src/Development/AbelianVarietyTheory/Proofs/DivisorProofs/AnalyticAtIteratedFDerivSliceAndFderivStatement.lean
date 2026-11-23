import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticAtIteratedFDerivSliceAndFderiv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConstantCoeffDpolyOfAdditiveTaylorPts
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analyticAt_iteratedFDeriv_slice_and_fderiv_eq : ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] (H : E × F → ℂ) (w₀ : F) (k : ℕ) (v : Fin k → E), AnalyticAt ℂ H (0, w₀) → AnalyticAt ℂ (fun w ↦ iteratedFDeriv ℂ k (fun z ↦ H (z, w)) 0 v) w₀ ∧ ∀ e : F, fderiv ℂ (fun w ↦ iteratedFDeriv ℂ k (fun z ↦ H (z, w)) 0 v) w₀ e = iteratedFDeriv ℂ k (fun z ↦ fderiv ℂ H (z, w₀) (0, e)) 0 v := by
  first | exact @GlobalTheory.analyticAt_iteratedFDeriv_slice_and_fderiv | exact GlobalTheory.analyticAt_iteratedFDeriv_slice_and_fderiv | (intros; apply GlobalTheory.analyticAt_iteratedFDeriv_slice_and_fderiv <;> assumption)
