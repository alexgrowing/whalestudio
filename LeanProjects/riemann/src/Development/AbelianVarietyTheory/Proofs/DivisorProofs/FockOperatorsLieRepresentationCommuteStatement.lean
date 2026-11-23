import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockOperatorsLieRepresentationCommute
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockOperators_lie_representation_commute : ∀ (p q r s : ℕ), (∀ Y Z, omAct p q r s (Y * Z - Z * Y) = omAct p q r s Y * omAct p q r s Z - omAct p q r s Z * omAct p q r s Y) ∧ IsLieAct (fockAct1 p q r s) ∧ IsLieAct (fockAct2 p q r s) ∧ ∀ Y Z, fockAct1 p q r s Y * fockAct2 p q r s Z = fockAct2 p q r s Z * fockAct1 p q r s Y := by
  first | exact @GlobalTheory.FockAlg.fock_lie_and_commute | exact GlobalTheory.FockAlg.fock_lie_and_commute | (intros; apply GlobalTheory.FockAlg.fock_lie_and_commute <;> assumption)
