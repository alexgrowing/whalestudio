import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexFunctorDegreeTermAugmentedExactResolution
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexFunctorDegreeTerm_augmented_exact_resolution : ∀ (R : Type) [CommRing R] (F : Shv R) (T : Type 1) [Category.{0} T] (Φ : T ⥤ Spcᵒᵖ) (U : T) (X : CosimplicialObject T) (a : (CosimplicialObject.const T).obj U ⟶ X), Hyp R Φ a → ∀ n, WExact (term (Φ ⋙ HC R F) n) a := by
  first | exact @GlobalTheory.EtC.wExact_term_HC | exact GlobalTheory.EtC.wExact_term_HC | (intros; apply GlobalTheory.EtC.wExact_term_HC <;> assumption)
