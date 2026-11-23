import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSurjectiveSectionOfSH
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_of_etale_surjective_of_SH : ∀ (A : Type) [CommRing A], SH A → ∀ (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of A)), Etale f → Surjective f → ∃ s : Spec (CommRingCat.of A) ⟶ Y, s ≫ f = 𝟙 _ := by
  first | exact @GlobalTheory.EtC.etale_surjective_section_of_SH | exact GlobalTheory.EtC.etale_surjective_section_of_SH | (intros; apply GlobalTheory.EtC.etale_surjective_section_of_SH <;> assumption)
