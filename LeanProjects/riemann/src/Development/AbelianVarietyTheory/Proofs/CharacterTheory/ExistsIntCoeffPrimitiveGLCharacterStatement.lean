import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsIntCoeffPrimitiveGLCharacter
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_int_coeff_primitive_GL_character : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ (d : ℕ) (χ : GL (Fin d) F → ℂ), 0 < d → IsChar ℂ ℂ χ → IsPrimitive (extZero χ) → ∃ a : ℕ → ℤ, (∀ k : ℕ, ipGL (extZero χ) (fun g : Module.End F (Fin d → F) => rootSum θ k (LinearMap.charpoly g)) = a k * glCard F d) ∧ (d : ℂ) * χ 1 = (∑ k ∈ Finset.range (Nat.card F ^ d - 1), (a k : ℂ)) * ∏ i ∈ Finset.Ico 1 d, (1 - (Nat.card F : ℂ) ^ i) := by
  first | exact @GlobalTheory.CuspGL.exists_int_coeff_of_isPrimitive | exact GlobalTheory.CuspGL.exists_int_coeff_of_isPrimitive | (intros; apply GlobalTheory.CuspGL.exists_int_coeff_of_isPrimitive <;> assumption)
