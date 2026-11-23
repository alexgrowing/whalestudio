import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralUnimodularCompletion
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRightMemSB
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit GlobalTheory.GJReg
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_unimodular_completion : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (A S C D : Matrix (Fin n) (Fin n) k), A ∈ intM k (Fin n) (Fin n) → S ∈ intM k (Fin n) (Fin n) →
    C ∈ intM k (Fin n) (Fin n) → D ∈ intM k (Fin n) (Fin n) → C * A + D * S = 1 →
    ∃ T ∈ intM k (Fin n) (Fin n), ∃ u ∈ KO k (Fin n), u.val = A + T * S := by
  first | exact @GlobalTheory.StableRange.exists_mem_KO | exact GlobalTheory.StableRange.exists_mem_KO | (intros; apply GlobalTheory.StableRange.exists_mem_KO <;> assumption)
