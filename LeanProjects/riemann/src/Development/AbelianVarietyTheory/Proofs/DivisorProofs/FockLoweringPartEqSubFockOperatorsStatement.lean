import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockLoweringPartEqSubFockOperators
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockLoweringPart_eq_sub_fockOperators : ∀ (p q r s : ℕ) (Z : Mat p q), IsPC Z → ∀ P : Pol p q r s, omAct p q r s (Matrix.kroneckerMap (· * ·) Z (1 : Mat r s)) P - omAct p q r s (Matrix.kroneckerMap (· * ·) (Jm p q * Z) (Jm r s)) P = (2 : ℂ) • minusPart (fockAct1 p q r s Z) P := by
  first | exact @GlobalTheory.FockLowDiff.lowering_eq_diff | exact GlobalTheory.FockLowDiff.lowering_eq_diff | (intros; apply GlobalTheory.FockLowDiff.lowering_eq_diff <;> assumption)
