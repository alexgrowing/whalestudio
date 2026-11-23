import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMatrixLeftFactor
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRightMemSB
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit GlobalTheory.GJReg
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_matrix_left_factor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (s : k),
    s ≠ 0 → ∀ X : Matrix (Fin n) (Fin n) k, ∃ (h : GL (Fin n) k) (A B C D : Matrix (Fin n) (Fin n) k),
      A ∈ intM k (Fin n) (Fin n) ∧ B ∈ intM k (Fin n) (Fin n) ∧ C ∈ intM k (Fin n) (Fin n) ∧ D ∈ intM k (Fin n) (Fin n) ∧
      h.val = A * X + s • B ∧ X = C * h.val ∧ s • (1 : Matrix (Fin n) (Fin n) k) = D * h.val := by
  first | exact @GlobalTheory.GJReg.exists_gl_rowSpan_int | exact GlobalTheory.GJReg.exists_gl_rowSpan_int | (intros; apply GlobalTheory.GJReg.exists_gl_rowSpan_int <;> assumption)
