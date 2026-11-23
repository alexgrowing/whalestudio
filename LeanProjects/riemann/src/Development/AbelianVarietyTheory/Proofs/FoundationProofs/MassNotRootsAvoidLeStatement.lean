import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MassNotRootsAvoidLe
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mass_not_rootsAvoid_le' : ∀ (g : ℕ) [Fact g.Prime], ∀ (N q d : ℕ) (c : (ZMod g)ˣ), (q.Prime ∧ d.Prime ∧ q ≠ 2 ∧ d ≠ 2 ∧ q ≠ d ∧ 16 ≤ max q d ∧ 16 * q * d ∣ g - 1) → (mass g N fun f => ¬ RootsAvoid g c f) ≤ 1 / (4 * ((min q d : ℕ) : ℝ)) + (1 + Real.log N) / ((g : ℝ) - 1) := by
  first | exact @GlobalTheory.BadShare.mass_not_rootsAvoid_le | exact GlobalTheory.BadShare.mass_not_rootsAvoid_le | (intros; apply GlobalTheory.BadShare.mass_not_rootsAvoid_le <;> assumption)
