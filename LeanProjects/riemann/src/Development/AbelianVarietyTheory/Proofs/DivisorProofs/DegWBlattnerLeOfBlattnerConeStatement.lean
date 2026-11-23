import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegWBlattnerLeOfBlattnerCone
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degW_blattner_le_of_blattnerCone : ∀ (p q : ℕ) (M : GKMod p q) (lam : Ix p q → ℚ) (c θ : ℚ), ConeTypes M lam → (∀ a, (θ < lam a → 0 ≤ shiftNu c (blattner lam) a) ∧ (lam a ≤ θ → shiftNu c (blattner lam) a ≤ 0)) → ∀ μ v, IsHW M.act μ v → degW c (blattner lam) ≤ degW c μ := by
  first | exact @GlobalTheory.FlowLemma.degW_blattner_le | exact GlobalTheory.FlowLemma.degW_blattner_le | (intros; apply GlobalTheory.FlowLemma.degW_blattner_le <;> assumption)
