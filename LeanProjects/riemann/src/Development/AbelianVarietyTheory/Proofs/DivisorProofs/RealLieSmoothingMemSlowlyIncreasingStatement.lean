import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLieSmoothingMemSlowlyIncreasing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realLieSmoothing_mem_slowlyIncreasing : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (α : Lie E a → ℂ), IsTest (invSet E a) α → ∀ f ∈ growth E a, smoothing ν α f ∈ growth E a := by
  first | exact @GlobalTheory.AutGrowth.smoothing_mem_growth | exact GlobalTheory.AutGrowth.smoothing_mem_growth | (intros; apply GlobalTheory.AutGrowth.smoothing_mem_growth <;> assumption)
