import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteNetIntegralMatrices
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRightMemSB
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit GlobalTheory.GJReg
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_net_integral_matrices : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (t : k),
    t ≠ 0 → valuation k t < 1 → ∀ N M : ℕ, ∃ R : Finset (Matrix (Fin n) (Fin n) k),
      (∀ Y ∈ R, t ^ N • Y ∈ intM k (Fin n) (Fin n)) ∧
      ∀ X, t ^ N • X ∈ intM k (Fin n) (Fin n) → ∃ Y ∈ R, ∃ E ∈ intM k (Fin n) (Fin n), X = Y + t ^ M • E := by
  first | exact @GlobalTheory.GJReg.FinReps.finite_reps_intM | exact GlobalTheory.GJReg.FinReps.finite_reps_intM | (intros; apply GlobalTheory.GJReg.FinReps.finite_reps_intM <;> assumption)
