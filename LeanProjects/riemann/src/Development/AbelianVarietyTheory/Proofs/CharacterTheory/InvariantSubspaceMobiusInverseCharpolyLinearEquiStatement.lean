import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseCharpolyLinearEqui
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj : ∀ (F : Type) [Field F] (s : F[X] → ℂ) (V V' : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] [AddCommGroup V'] [Module F V'] [FiniteDimensional F V'] (e : V ≃ₗ[F] V') (g : Module.End F V), psi s V' (e.conj g) = psi s V g := by
  first | exact @GlobalTheory.CuspGL.psi_conj | exact GlobalTheory.CuspGL.psi_conj | (intros; apply GlobalTheory.CuspGL.psi_conj <;> assumption)
