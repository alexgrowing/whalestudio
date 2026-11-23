import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFilteredColimitEtaleOfIndEtStatement

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces
open scoped TensorProduct

namespace UpperTheory.Gal.TranscendenceTraces

private noncomputable def pushIso (A B O : Type) [CommRing A] [CommRing B] [CommRing O] [Algebra A B] [Algebra A O] :
    (Under.pushout (CommRingCat.ofHom (algebraMap A B))).obj (Under.mk (CommRingCat.ofHom (algebraMap A O))) ≅
      Under.mk (CommRingCat.ofHom (algebraMap B (B ⊗[A] O))) :=
  Under.isoMk (CommRingCat.isPushout_tensorProduct A B O).flip.isoPushout.symm
    ((CommRingCat.isPushout_tensorProduct A B O).flip.inr_isoPushout_inv)

private def algOf {B C T : Type} [CommRing B] [CommRing C] [CommRing T] [Algebra B C] [Algebra B T]
    (f : Under.mk (CommRingCat.ofHom (algebraMap B C)) ⟶ Under.mk (CommRingCat.ofHom (algebraMap B T))) : C →ₐ[B] T :=
  { f.right.hom with
    commutes' := fun b => by
      have := congr($(Under.w f).hom b)
      simpa using this }

private def underOf {B C T : Type} [CommRing B] [CommRing C] [CommRing T] [Algebra B C] [Algebra B T]
    (f : C →ₐ[B] T) : Under.mk (CommRingCat.ofHom (algebraMap B C)) ⟶ Under.mk (CommRingCat.ofHom (algebraMap B T)) :=
  Under.homMk (CommRingCat.ofHom f.toRingHom) (by ext b; exact f.commutes b)

end UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.indDesc_of :
    IndDesc := by
  intro A O B C _ _ _ _ _ _ _ _ hO ⟨g⟩
  obtain ⟨J, _, _, D, ι, ⟨hc⟩, hD⟩ := GlobalTheory.T.exists_filtered_colimit_of_etale_of_indEt A O hO
  let F := Under.pushout (CommRingCat.ofHom (algebraMap A B))
  have hFc := isColimitOfPreserves F hc
  have : IsFinitelyPresentable.{0} (Under.mk (CommRingCat.ofHom (algebraMap B C))) :=
    CommRingCat.isFinitelyPresentable_under _ _
      (show (algebraMap B C).FinitePresentation from
        (RingHom.finitePresentation_algebraMap (A := B) (B := C)).mpr inferInstance)
  obtain ⟨j, q, -⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hFc
    (underOf g ≫ (pushIso A B O).inv)
  let E : Type := (D.obj j).right
  letI : Algebra A E := (D.obj j).hom.hom.toAlgebra
  refine ⟨E, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · exact RingHom.etale_algebraMap.mp (hD j)
  · refine ⟨{ (ι.app j).right.hom with commutes' := fun a => ?_ }⟩
    have := congr($(Under.w (ι.app j)).hom a)
    exact this
  · exact ⟨algOf (q ≫ (pushIso A B E).hom)⟩
