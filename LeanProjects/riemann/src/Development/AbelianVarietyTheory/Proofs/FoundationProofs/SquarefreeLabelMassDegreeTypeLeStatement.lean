import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelMassDegreeTypeLe
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squarefreeLabelMass_degreeType_le : ∀ (g : ℕ) [Fact g.Prime], ∀ (N : ℕ) (μ : Multiset ℕ), (mass g N fun f => degType g f = μ) ≤ (∏ d ∈ μ.toFinset, ((d : ℝ) ^ μ.count d * (μ.count d).factorial))⁻¹ := by
  first | exact @GlobalTheory.BadShare.mass_degType_le | exact GlobalTheory.BadShare.mass_degType_le | (intros; apply GlobalTheory.BadShare.mass_degType_le <;> assumption)
