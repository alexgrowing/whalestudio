import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIndEtaleAlgebraOfStrictlyHenselianEtaleStalkAf
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIndEtaleAlgebra_of_strictlyHenselianEtaleStalk_affine : ∀ (A : Type) [CommRing A] (O : Type) [CommRing O] (s : Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of A)), IsStalk O s → ∃ _ : Algebra A O, SH O ∧ IndEt A O ∧ s = Spec.map (CommRingCat.ofHom (algebraMap A O)) := by
  first | (exact @GlobalTheory.EtC.isStalk_affine) | (exact GlobalTheory.EtC.isStalk_affine) | (intros; apply GlobalTheory.EtC.isStalk_affine  <;> assumption)
