import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirFockAct1SubCasimirFockAct2
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casimir_fockAct1_sub_casimir_fockAct2_eq_smul_one : ∀ (p q r s : ℕ), casimir (fockAct1 p q r s) - casimir (fockAct2 p q r s) = ((((p + q : ℕ) : ℂ) * ((r + s : ℕ) : ℂ) * (((r + s : ℕ) : ℂ) - ((p + q : ℕ) : ℂ))) / 4) • (1 : Module.End ℂ (Pol p q r s)) := by
  first | exact @GlobalTheory.FockCasimir.casimir_fockAct1_sub_casimir_fockAct2 | exact GlobalTheory.FockCasimir.casimir_fockAct1_sub_casimir_fockAct2 | (intros; apply GlobalTheory.FockCasimir.casimir_fockAct1_sub_casimir_fockAct2 <;> assumption)
