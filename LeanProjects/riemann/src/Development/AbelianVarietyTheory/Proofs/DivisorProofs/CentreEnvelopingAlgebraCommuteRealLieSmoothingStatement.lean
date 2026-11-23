import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreEnvelopingAlgebraCommuteRealLieSmoothing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centreEnvelopingAlgebra_commute_realLieSmoothing : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (α : Lie E a → ℂ), IsTest (invSet E a) α → ∀ (ψ : Sm E a) (h : smoothing ν α ψ.1 ∈ Sm E a), ∀ z ∈ Zalg E a, (z ⟨smoothing ν α ψ.1, h⟩).1 = smoothing ν α (z ψ).1 := by
  first | exact @GlobalTheory.CentreSmooth.zalg_smoothing | exact GlobalTheory.CentreSmooth.zalg_smoothing | (intros; apply GlobalTheory.CentreSmooth.zalg_smoothing <;> assumption)
