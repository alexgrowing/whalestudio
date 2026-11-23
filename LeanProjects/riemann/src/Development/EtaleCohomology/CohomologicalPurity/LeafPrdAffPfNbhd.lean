import Development.EtaleCohomology.CohomologicalPurity.LeafPrdAffPfQuot

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem indNbhd_of_nbhd {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A) (h : Nbhd φ I) :
    IndNbhd φ I :=
  ⟨Discrete PUnit, inferInstance, inferInstance, (Functor.const _).obj (CommRingCat.of B),
    (Functor.const _).map (CommRingCat.ofHom φ), 𝟙 _, ⟨isColimitConstCocone (Discrete PUnit) (CommRingCat.of B)⟩,
    fun _ => ⟨h, Category.comp_id _⟩⟩

end LateralTheory.CohomologicalPurity.TubeCut
