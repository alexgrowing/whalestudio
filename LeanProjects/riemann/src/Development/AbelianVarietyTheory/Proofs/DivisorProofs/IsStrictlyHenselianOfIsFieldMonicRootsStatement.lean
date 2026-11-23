import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStrictlyHenselianOfIsFieldMonicRoots
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isStrictlyHenselian_of_isField_monicRoots : ∀ (T : Type) [CommRing T], IsField T → AIC T → SH T := by
  first | (exact @GlobalTheory.EtC.isField_aic_sh) | (exact GlobalTheory.EtC.isField_aic_sh) | (intros; apply GlobalTheory.EtC.isField_aic_sh  <;> assumption)
