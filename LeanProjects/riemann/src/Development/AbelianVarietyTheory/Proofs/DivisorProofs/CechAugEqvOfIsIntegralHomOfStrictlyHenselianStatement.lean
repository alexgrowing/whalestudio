import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechAugEqvOfIsIntegralHomOfStrictlyHenselian
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eqv_cechAug_of_isIntegralHom_of_surjective_of_sh : ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ (Y : Scheme.{0}) (g : Y ⟶ Spec (CommRingCat.of A)), IsIntegralHom g → Surjective g → Eqv _ (cechAug g) (tw q i) := by
  first
  | exact @GlobalTheory.EtC.cechAug_eqv_of_isIntegralHom_of_strictlyHenselian
  | exact GlobalTheory.EtC.cechAug_eqv_of_isIntegralHom_of_strictlyHenselian
  | (intros; apply GlobalTheory.EtC.cechAug_eqv_of_isIntegralHom_of_strictlyHenselian <;> assumption)
