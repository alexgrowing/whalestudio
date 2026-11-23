import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFieldMonicRootsTensorFractionRingStrictlyHense
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isField_monicRoots_tensor_fractionRing_strictlyHenselian : ∀ (A O : Type) [CommRing A] [IsDomain A] [CommRing O] [Algebra A O], AIC A → SH O → IndEt A O → IsField (O ⊗[A] FractionRing A) ∧ AIC (O ⊗[A] FractionRing A) := by
  first | (exact @GlobalTheory.isField_aic_tensor_fractionRing_of_strictlyHenselian) | (exact GlobalTheory.isField_aic_tensor_fractionRing_of_strictlyHenselian) | (intros; apply GlobalTheory.isField_aic_tensor_fractionRing_of_strictlyHenselian  <;> assumption)
