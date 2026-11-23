import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusMassNoLargePrimeFactorLe
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squarefreeLabelTorusMass_no_large_prime_factor_le : ∀ (g : ℕ) [Fact g.Prime], ∀ N : ℕ, 100000 ≤ N → (mass g N fun f => ¬ HasPrimeFactor g N f) ≤ 1 - 1 / (10 * Real.log N) := by
  first | exact @GlobalTheory.BadShare.mass_not_hasPrimeFactor_le | exact GlobalTheory.BadShare.mass_not_hasPrimeFactor_le | (intros; apply GlobalTheory.BadShare.mass_not_hasPrimeFactor_le <;> assumption)
