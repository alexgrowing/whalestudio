import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepFunctionIndicatorSpan
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRightMemSB
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit GlobalTheory.GJReg
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.step_function_indicator_span : ∀ (β : Type) (le : β → β → Prop), (∀ x y z, le x y → le y z → le x z) →
    ∀ (B : Set β) (R : Finset β) (F : β → ℂ), (↑R ⊆ B) → (∀ x ∈ B, ∃ y ∈ R, le x y ∧ le y x) →
    (∀ x ∈ B, ∀ y ∈ B, le x y → le y x → F x = F y) →
    ∃ (m : ℕ) (c : Fin m → ℂ) (a : Fin m → β), (∀ i, a i ∈ B) ∧
      ∀ x ∈ B, F x = ∑ i, c i * (if le x (a i) then 1 else 0) := by
  first | exact @GlobalTheory.classFun_eq_sum_indicator_le | exact GlobalTheory.classFun_eq_sum_indicator_le | (intros; apply GlobalTheory.classFun_eq_sum_indicator_le <;> assumption)
