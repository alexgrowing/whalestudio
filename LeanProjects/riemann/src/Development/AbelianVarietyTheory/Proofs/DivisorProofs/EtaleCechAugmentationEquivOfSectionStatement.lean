import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCechAugmentationEquivOfSection
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCechAugmentation_equiv_of_section : ∀ (R : Type) [CommRing R] (F : Shv R) (Y X : Scheme.{0}) (f : Y ⟶ X) (s : X ⟶ Y), s ≫ f = 𝟙 X → Eqv R (cechAug f) F := by
  first | exact @GlobalTheory.cechAug_eqv_of_section | exact GlobalTheory.cechAug_eqv_of_section | (intros; apply GlobalTheory.cechAug_eqv_of_section <;> assumption)
