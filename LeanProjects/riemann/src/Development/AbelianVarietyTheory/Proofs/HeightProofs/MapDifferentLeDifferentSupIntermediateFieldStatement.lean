import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MapDifferentLeDifferentSupIntermediateField
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_different_le_different_sup_intermediateField : ∀ (F F' : IntermediateField ℚ ℂ) [NumberField F] [NumberField F'] [NumberField ↥(F ⊔ F')], letI : Algebra F ↥(F ⊔ F') := (IntermediateField.inclusion le_sup_left).toRingHom.toAlgebra; (differentIdeal ℤ (𝓞 F')).map (RingOfIntegers.mapRingHom (IntermediateField.inclusion (le_sup_right : F' ≤ F ⊔ F')).toRingHom) ≤ differentIdeal (𝓞 F) (𝓞 ↥(F ⊔ F')) := by
  first | exact @GlobalTheory.DiffBaseChange.map_different_le_sup | exact GlobalTheory.DiffBaseChange.map_different_le_sup | (intros; apply GlobalTheory.DiffBaseChange.map_different_le_sup <;> assumption)
