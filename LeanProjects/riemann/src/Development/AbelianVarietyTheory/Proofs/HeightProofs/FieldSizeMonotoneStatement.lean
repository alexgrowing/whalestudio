import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeMonotone
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.field_size_monotone : (∀ (F : IntermediateField ℚ ℂ) (a b a' b' : ℝ), Sz F a b → a ≤ a' → b ≤ b' → Sz F a' b') ∧ ∀ (F F' : IntermediateField ℚ ℂ) (a b : ℝ), F ≤ F' → Sz F' a b → Sz F a b := by
  first | exact @GlobalTheory.FieldSize.sz_mono_and_of_le | exact GlobalTheory.FieldSize.sz_mono_and_of_le | (intros; apply GlobalTheory.FieldSize.sz_mono_and_of_le <;> assumption)
