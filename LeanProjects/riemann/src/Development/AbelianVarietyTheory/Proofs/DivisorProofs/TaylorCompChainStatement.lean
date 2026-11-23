import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorCompChain
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConstantCoeffDpolyOfAdditiveTaylorPts
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.taylor_comp_eq_taylor_taylor_of_analyticAt : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ {K : Type} [Fintype K] [DecidableEq K] (Φ : (I → ℂ) → K → ℂ) (h : (K → ℂ) → ℂ), AnalyticAt ℂ Φ 0 → Φ 0 = 0 → AnalyticAt ℂ h 0 → GlobalTheory.PeriodFamily.taylor N t (fun z ↦ h (Φ z)) = GlobalTheory.PeriodFamily.taylor N (fun k ↦ GlobalTheory.PeriodFamily.taylor N t fun z ↦ Φ z k) h := by
  first | exact @GlobalTheory.PeriodFamily.taylor_comp_chain | exact GlobalTheory.PeriodFamily.taylor_comp_chain | (intros; apply GlobalTheory.PeriodFamily.taylor_comp_chain <;> assumption)
