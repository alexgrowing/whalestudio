import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in

theorem exists_filtered_colimit_etale_of_indEt : ∀ (A O : Type) [CommRing A] [CommRing O] [Algebra A O], IndEt A O → ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ Under (CommRingCat.of A)) (ι : D ⟶ (Functor.const J).obj (Under.mk (CommRingCat.ofHom (algebraMap A O)))), Nonempty (IsColimit (Cocone.mk _ ι)) ∧ ∀ j, (D.obj j).hom.hom.Etale := by
  intro A O _ _ _ h
  obtain ⟨J, _, _, D, t, s, hs, hst⟩ := h
  have : Nonempty J := IsFiltered.nonempty
  refine ⟨J, inferInstance, inferInstance, Under.lift D t,
    { app j := Under.homMk (s.app j) (by simp [hst]) },
    ⟨Under.isColimitLiftCocone _ _ _ _ (by simp [hst]) hs⟩, fun j => (hst j).1⟩

end GlobalTheory.EtC
