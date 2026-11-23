import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFieldIdealsPrincipal
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_field_ideals_principal : ∀ (E : Type) [Field E] [NumberField E] (φ : E →+* ℂ) (F : IntermediateField ℚ ℂ) (a b : ℝ), Sz F a b → (∀ x, φ x ∈ F) → ∃ F' : IntermediateField ℚ ℂ, F ≤ F' ∧ Sz F' (a + Real.log (classNumber E)) (b + Real.log (classNumber E)) ∧ ∀ (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K], F' ≤ K → ∀ 𝔞 : Ideal (𝓞 E), ∃ β : K, Submodule.span (𝓞 K) {β} = Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : ℂ) = φ (a : E)} := by
  first | exact @GlobalTheory.FieldSize.exists_sz_capitulation | exact GlobalTheory.FieldSize.exists_sz_capitulation | (intros; apply GlobalTheory.FieldSize.exists_sz_capitulation <;> assumption)
