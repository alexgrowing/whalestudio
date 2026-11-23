import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusMassRootsNotDistinctLe
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squarefreeLabelTorusMass_rootsNotDistinct_le : ∀ (g : ℕ) [Fact g.Prime], ∀ N : ℕ, 2 ^ 12 ≤ g → (mass g N fun f => ¬ RootsApart g N f) ≤ 23 * Real.log g / Real.sqrt g := by
  first | exact @GlobalTheory.BadShare.mass_not_rootsApart_le | exact GlobalTheory.BadShare.mass_not_rootsApart_le | (intros; apply GlobalTheory.BadShare.mass_not_rootsApart_le <;> assumption)
