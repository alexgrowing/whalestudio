import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceOfStrictlyHenselianSta
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_cohomology_equivalence_of_strictly_henselian_stalks : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (E E' : Spc) (α : E ⟶ E') (p : E' ⟶ sch.obj S), Finitary F → QcqsOver (α ≫ p) → QcqsOver p → (∀ (O : Type) [CommRing O] (s : Spec (CommRingCat.of O) ⟶ S), IsStalk O s → Eqv R ((bcMap α p).app (Over.mk s)) F) → ∀ (U : Over S), Etale U.hom → ∀ n : ℤ, (∀ x : H R ((bc (α ≫ p)).obj U) F n, ∃ (V : Over S) (h : V ⟶ U) (y : H R ((bc p).obj V) F n), Etale V.hom ∧ Surjective h.left ∧ pull R ((bcMap α p).app V) F n y = pull R ((bc (α ≫ p)).map h) F n x) ∧ ∀ y : H R ((bc p).obj U) F n, pull R ((bcMap α p).app U) F n y = 0 → ∃ (V : Over S) (h : V ⟶ U), Etale V.hom ∧ Surjective h.left ∧ pull R ((bc p).map h) F n y = 0 := by
  first
  | exact @GlobalTheory.EtC.loc_glob_classes
  | exact GlobalTheory.EtC.loc_glob_classes
  | (intros; apply GlobalTheory.EtC.loc_glob_classes <;> assumption)
