import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzAveragingLeftInvariant
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRightMemSB
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit GlobalTheory.GJReg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_averaging_left_invariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (φ : Matrix (Fin n) (Fin n) k → ℂ), φ ∈ SB (Matrix (Fin n) (Fin n) k) →
    ∃ (m : ℕ) (w : Fin m → ℂ) (u : Fin m → GL (Fin n) k), (∀ i, u i ∈ KO k (Fin n)) ∧ ∑ i, w i = 1 ∧
      ∀ g ∈ KO k (Fin n), ∀ X, ∑ i, w i * φ ((u i).val * (g.val * X)) = ∑ i, w i * φ ((u i).val * X) := by
  first | exact @GlobalTheory.AvgKO.avg_fin | exact GlobalTheory.AvgKO.avg_fin | (intros; apply GlobalTheory.AvgKO.avg_fin <;> assumption)
