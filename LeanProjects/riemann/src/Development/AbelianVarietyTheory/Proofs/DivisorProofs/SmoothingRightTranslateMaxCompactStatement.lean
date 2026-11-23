import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothingRightTranslateMaxCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothing_right_translate_maxCompact : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (α : Lie E a → ℂ), KInv α → ∀ (ψ : GA E a → ℂ) (k : Kinf E a) (g : GA E a), smoothing ν α (fun x => ψ (x * infGL E a (Unitary.toUnits k))) g = smoothing ν α ψ (g * infGL E a (Unitary.toUnits k)) := by
  first | exact @GlobalTheory.AutGrowth.smoothing_rt_Kinf | exact GlobalTheory.AutGrowth.smoothing_rt_Kinf | (intros; apply GlobalTheory.AutGrowth.smoothing_rt_Kinf <;> assumption)
