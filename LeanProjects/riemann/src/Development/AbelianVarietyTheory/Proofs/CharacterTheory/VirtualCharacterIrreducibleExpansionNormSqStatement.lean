import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharacterIrreducibleExpansionNormSq
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.virtualCharacter_irreducible_expansion_normSq : ∀ (G : Type) [Group G] [Finite G] (φ : G → ℂ), φ ∈ Virt ℂ ℂ G → ∃ c : (G → ℂ) →₀ ℤ, (∀ χ ∈ c.support, IsIrrChar ℂ ℂ χ) ∧ φ = c.sum (fun χ m => m • χ) ∧ ∑ᶠ g, φ g * star (φ g) = (c.sum fun _ m => (m : ℂ) ^ 2) * (Nat.card G : ℂ) := by
  first | exact @GlobalTheory.BI.virt_expand | exact GlobalTheory.BI.virt_expand | (intros; apply GlobalTheory.BI.virt_expand <;> assumption)
