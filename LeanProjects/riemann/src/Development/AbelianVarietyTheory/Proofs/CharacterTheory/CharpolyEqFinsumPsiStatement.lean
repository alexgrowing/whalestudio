import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharpolyEqFinsumPsi
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.apply_charpoly_eq_finsum_psi_invariant_submodules : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ) (g : Module.End F V), s (LinearMap.charpoly g) = ∑ᶠ W : {W : Submodule F V // ∀ x ∈ W, g x ∈ W}, psi s W.1 (g.restrict W.2) := by
  first | exact @GlobalTheory.CuspGL.charpoly_eq_finsum_psi | exact GlobalTheory.CuspGL.charpoly_eq_finsum_psi | (intros; apply GlobalTheory.CuspGL.charpoly_eq_finsum_psi <;> assumption)
