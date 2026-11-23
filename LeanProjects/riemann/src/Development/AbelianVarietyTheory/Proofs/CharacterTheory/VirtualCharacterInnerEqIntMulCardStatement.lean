import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharacterInnerEqIntMulCard
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.virtualCharacter_inner_eq_int_mul_card : ∀ (G : Type) [Group G] [Finite G] (a b : G → ℂ), a ∈ Virt ℂ ℂ G → b ∈ Virt ℂ ℂ G → ∃ m : ℤ, ∑ᶠ g, a g * star (b g) = m * (Nat.card G : ℂ) := by
  first | exact @GlobalTheory.BI.finsum_mul_star_virt_int | exact GlobalTheory.BI.finsum_mul_star_virt_int | (intros; apply GlobalTheory.BI.finsum_mul_star_virt_int <;> assumption)
