import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MassDegTypeLeCycleType
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mass_degType_le_card_cycleType_div : ∀ (g : ℕ) [Fact g.Prime], ∀ (N : ℕ) (A : Multiset ℕ → Prop), (mass g N fun f => A (degType g f)) ≤ ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) => A σ.partition.parts).card : ℝ) / (N.factorial : ℝ) := by
  first | exact @GlobalTheory.BadShare.mass_degType_le_cycleType | exact GlobalTheory.BadShare.mass_degType_le_cycleType | (intros; apply GlobalTheory.BadShare.mass_degType_le_cycleType <;> assumption)
