import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJointHarmonicsHighestWeightEqBotOfNotShape
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockJointHarmonics_highestWeight_eq_bot_of_not_shape : ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ), ¬ JointShape p q r s μ μ' → hwSub (fockAct1 p q r s) μ ⊓ hwSub (fockAct2 p q r s) μ' ⊓ Submodule.span ℂ (jointHarm p q r s) = ⊥ := by
  first | exact @GlobalTheory.FockAlg.jointHarm_hw_eq_bot | exact GlobalTheory.FockAlg.jointHarm_hw_eq_bot | (intros; apply GlobalTheory.FockAlg.jointHarm_hw_eq_bot <;> assumption)
