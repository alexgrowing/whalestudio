import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OneSubTwoDivLeSquarefreeLabelMass
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_sub_two_div_le_squarefreeLabelMass : ∀ (g : ℕ) [Fact g.Prime], ∀ N : ℕ, 1 - 2 / (g : ℝ) ≤ mass g N fun _ => True := by
  first | exact @GlobalTheory.BadShare.one_sub_two_div_le_mass_true | exact GlobalTheory.BadShare.one_sub_two_div_le_mass_true | (intros; apply GlobalTheory.BadShare.one_sub_two_div_le_mass_true <;> assumption)
