import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.PrimitiveEndClassFunctionZeroOfCharpolyMassZero
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitiveEndClassFunction_zero_of_charpoly_mass_zero : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (φ : Module.End F V → ℂ), IsClassFn φ → IsPrimitive φ → ∀ g : Module.End F V, mass φ (LinearMap.charpoly g) = 0 → φ g = 0 := by
  first | exact @GlobalTheory.CuspGL.eq_zero_of_mass_charpoly_eq_zero | exact GlobalTheory.CuspGL.eq_zero_of_mass_charpoly_eq_zero | (intros; apply GlobalTheory.CuspGL.eq_zero_of_mass_charpoly_eq_zero <;> assumption)
