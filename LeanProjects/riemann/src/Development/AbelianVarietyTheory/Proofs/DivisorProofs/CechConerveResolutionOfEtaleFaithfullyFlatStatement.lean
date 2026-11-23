import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechConerveResolutionOfEtaleFaithfullyFlat
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechConerve_resolution_of_etaleFaithfullyFlat : ∀ (R : Type) [CommRing R] (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → Hyp R (Scheme.Spec.rightOp ⋙ sch.op) (coAug g) := by
  first | (exact @GlobalTheory.EtC.hyp_spec_coAug_of_etFF) | (exact GlobalTheory.EtC.hyp_spec_coAug_of_etFF) | (intros; apply GlobalTheory.EtC.hyp_spec_coAug_of_etFF <;> assumption)
