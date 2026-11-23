import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFaithfullyFlatDescendsOfIsColimit
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleFaithfullyFlat_descends_of_isColimit : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ (B : CommRingCat.{0}) (g : c.pt ⟶ B), EtFF g → ∃ (j : J) (B' : CommRingCat.{0}) (g' : D.obj j ⟶ B') (h : B' ⟶ B), EtFF g' ∧ IsPushout g' (c.ι.app j) h g := by
  first | (exact @GlobalTheory.EtC.etFF_descends_of_isColimit) | (exact GlobalTheory.EtC.etFF_descends_of_isColimit) | (intros; apply GlobalTheory.EtC.etFF_descends_of_isColimit  <;> assumption)
