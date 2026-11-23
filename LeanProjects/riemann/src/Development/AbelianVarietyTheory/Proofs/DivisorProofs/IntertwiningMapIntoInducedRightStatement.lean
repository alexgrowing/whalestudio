import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntertwiningMapIntoInducedRight
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intertwining_map_into_induced_right : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a a' : ℕ) (α β : kˣ →* ℂˣ) (l : (Matrix (Fin a') (Fin a') k → ℂ) → ℂ), IsSmU α →
    IsEqv (α / β) (((a + a' : ℕ) : ℂ) / 2) l → ∀ Ψ ∈ SB (Matrix (Fin a') (Fin (a + a')) k), mapB a l (α / β) α Ψ ∈ indSp a a' α β := by
  first | exact @GlobalTheory.KSplit.mapB_mem_indSp | exact GlobalTheory.KSplit.mapB_mem_indSp | (intros; apply GlobalTheory.KSplit.mapB_mem_indSp <;> assumption)
