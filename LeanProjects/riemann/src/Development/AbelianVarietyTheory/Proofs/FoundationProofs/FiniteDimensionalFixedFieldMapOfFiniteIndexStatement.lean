import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteDimensionalFixedFieldMapOfFiniteIndex
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_fixedField_map_of_finiteIndex' : ∀ {F E : Type} [Field F] [Field E] [Algebra F E] (G : Type) [Group G] (act : G →* (E ≃ₐ[F] E)) (N : Subgroup G), N.FiniteIndex → (∀ x : E, (∀ g, act g x = x) → x ∈ (⊥ : IntermediateField F E)) → FiniteDimensional F (IntermediateField.fixedField (N.map act)) := by
  first | exact @GlobalTheory.finiteDimensional_fixedField_map_of_finiteIndex | exact GlobalTheory.finiteDimensional_fixedField_map_of_finiteIndex | (intros; apply GlobalTheory.finiteDimensional_fixedField_map_of_finiteIndex <;> assumption)
