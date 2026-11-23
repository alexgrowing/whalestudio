import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FinsumCardCyclicVectorsInvariantSubspaces
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_card_cyclic_vectors_invariant_subspaces : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (g : Module.End F V), ∑ᶠ W : {W : Submodule F V // ∀ x ∈ W, g x ∈ W}, (Nat.card {v : W.1 // ∀ U : Submodule F (W.1), (∀ x ∈ U, (g.restrict W.2) x ∈ U) → v ∈ U → U = ⊤} : ℂ) = (Nat.card F : ℂ) ^ Module.finrank F V := by
  first | exact @GlobalTheory.CuspGL.finsum_card_cyclic_eq | exact GlobalTheory.CuspGL.finsum_card_cyclic_eq | (intros; apply GlobalTheory.CuspGL.finsum_card_cyclic_eq <;> assumption)
