import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CardSubspacesMulGeneralLinearGroupCard
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_subspaces_mul_generalLinearGroupCard : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (a : ℕ), a ≤ Module.finrank F V → (Nat.card {W : Submodule F V // Module.finrank F W = a} : ℂ) * (Nat.card F : ℂ) ^ (a * (Module.finrank F V - a)) * glCard F a * glCard F (Module.finrank F V - a) = glCard F (Module.finrank F V) := by
  first | exact @GlobalTheory.CuspGL.card_subspaces_mul_glCard | exact GlobalTheory.CuspGL.card_subspaces_mul_glCard | (intros; apply GlobalTheory.CuspGL.card_subspaces_mul_glCard <;> assumption)
