import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.EqOfIsPrimitiveOfEqOnEllipticFiniteGL
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_isPrimitive_of_eq_on_elliptic_finiteGL : ∀ (F : Type) [Field F] [Finite F] (d : ℕ) (χ χ' : GL (Fin d) F → ℂ), 0 < d → IsIrrChar ℂ ℂ χ → IsIrrChar ℂ ℂ χ' → IsPrimitive (extZero χ) → IsPrimitive (extZero χ') → (∀ x : GL (Fin d) F, Irreducible (Matrix.charpoly (x : Matrix (Fin d) (Fin d) F)) → χ x = χ' x) → χ = χ' := by
  first | exact @GlobalTheory.CuspGL.eq_of_isPrimitive_of_eq_on_elliptic | exact GlobalTheory.CuspGL.eq_of_isPrimitive_of_eq_on_elliptic | (intros; apply GlobalTheory.CuspGL.eq_of_isPrimitive_of_eq_on_elliptic <;> assumption)
