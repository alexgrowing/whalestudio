import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalDegreeOmActKronBlockDiagonalLe
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.totalDegree_omAct_kron_blockDiagonal_le : ∀ (p q r s : ℕ) (E : Mat p q), IsKC E → ∀ (d : ℕ) (P : Pol p q r s), P.totalDegree ≤ d → (omAct p q r s (Matrix.kroneckerMap (· * ·) E (Jm r s)) P).totalDegree ≤ d := by
  first | exact @GlobalTheory.FockBlockDeg.totalDegree_omAct_kron_le | exact GlobalTheory.FockBlockDeg.totalDegree_omAct_kron_le | (intros; apply GlobalTheory.FockBlockDeg.totalDegree_omAct_kron_le <;> assumption)
