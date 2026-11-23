import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.EqZeroOfNotPrimary
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classFn_eq_zero_of_charpoly_not_irreducible_pow : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (φ : Module.End F V → ℂ), IsClassFn φ → IsPrimitive φ → 0 < Module.finrank F V → ∀ g : Module.End F V, (¬ ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧ LinearMap.charpoly g = f ^ m) → φ g = 0 := by
  first | exact @GlobalTheory.CuspGL.eq_zero_of_not_primary | exact GlobalTheory.CuspGL.eq_zero_of_not_primary | (intros; apply GlobalTheory.CuspGL.eq_zero_of_not_primary <;> assumption)
