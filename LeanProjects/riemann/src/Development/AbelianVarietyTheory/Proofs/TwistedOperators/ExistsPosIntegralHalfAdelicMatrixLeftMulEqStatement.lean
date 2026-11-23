import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPosIntegralHalfAdelicMatrixLeftMulEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pos_integral_halfAdelicMatrix_leftMul_eq : ∀ (D : D7) (a : AE D) (m n : ℕ) (M M' : Matrix (Fin m) (Fin m) (AE D)), M * M' = 1 → M' * M = 1 → ∃ κ : ℝ, 0 < κ ∧ ∀ φ : halfMx a m n → ℂ, ∫ t, φ (leftMul a M t) ∂haarHalf a m n = κ * ∫ t, φ t ∂haarHalf a m n := by
  first | exact @GlobalTheory.HalfAverage.integral_leftMul_eq_smul | exact GlobalTheory.HalfAverage.integral_leftMul_eq_smul | (intros; apply GlobalTheory.HalfAverage.integral_leftMul_eq_smul <;> assumption)
