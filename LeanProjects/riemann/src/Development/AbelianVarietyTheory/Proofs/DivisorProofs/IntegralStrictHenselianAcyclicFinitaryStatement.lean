import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralStrictHenselianAcyclicFinitary
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_strictHenselian_acyclic_finitary : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B], SH A → AcycF R (sp B) F := by
  first | (exact @GlobalTheory.EtC.IntAcyc.acycF_of_isIntegral) | (exact GlobalTheory.EtC.IntAcyc.acycF_of_isIntegral) | (intros; apply GlobalTheory.EtC.IntAcyc.acycF_of_isIntegral  <;> assumption)
