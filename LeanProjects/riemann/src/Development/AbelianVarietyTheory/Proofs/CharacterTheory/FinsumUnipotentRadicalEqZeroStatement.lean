import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FinsumUnipotentRadicalEqZero
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_unipotent_radical_eq_zero_of_isPrimitive : ∀ (F : Type) [Field F] [Finite F] (d : ℕ) (φ : Module.End F (Fin d → F) → ℂ), IsPrimitive φ → ∀ a : ℕ, 0 < a → a < d → ∑ᶠ u ∈ {u : GL (Fin d) F | ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) F) i j = (if i = j then 1 else 0) ∨ (i.val < a ∧ a ≤ j.val)}, φ (Matrix.toLin' (u : Matrix (Fin d) (Fin d) F)) = 0 := by
  first | exact @GlobalTheory.CuspGL.IsPrimitive.finsum_unipotentRadical_eq_zero | exact GlobalTheory.CuspGL.IsPrimitive.finsum_unipotentRadical_eq_zero | (intros; apply GlobalTheory.CuspGL.IsPrimitive.finsum_unipotentRadical_eq_zero <;> assumption)
