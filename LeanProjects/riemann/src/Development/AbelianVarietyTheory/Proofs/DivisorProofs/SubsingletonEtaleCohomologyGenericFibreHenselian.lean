import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIndEtaleTensorProductLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgClosedFractionRingOfMonicPolynomialsHaveRoo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyTwistedFilteredColimitContinuityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologySubsingletonEtaleOverPolynomiStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.GenFibreLine

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap]
  rw [← Functor.map_comp, ← Spec.map_comp]
  rfl

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  simp only [spMap]
  rw [show CommRingCat.ofHom (RingHom.id A) = 𝟙 (CommRingCat.of A) from rfl, Spec.map_id,
    CategoryTheory.Functor.map_id]

theorem pull_bijective_of_ringEquiv {R : Type} [CommRing R] {A B : Type} [CommRing A] [CommRing B]
    (e : A ≃+* B) (F : Shv R) (n : ℤ) : Function.Bijective (pull R (spMap (e : A →+* B)) F n) := by
  have h1 : spMap (e.symm : B →+* A) ≫ spMap (e : A →+* B) = 𝟙 _ := by
    rw [← spMap_comp', ← spMap_id']
    congr 1
    ext x
    simp
  have h2 : spMap (e : A →+* B) ≫ spMap (e.symm : B →+* A) = 𝟙 _ := by
    rw [← spMap_comp', ← spMap_id']
    congr 1
    ext x
    simp
  refine Function.bijective_iff_has_inverse.2 ⟨pull R (spMap (e.symm : B →+* A)) F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, h1, pull_id]
  · rw [← pull_comp, h2, pull_id]

theorem genericFibre_subsingleton : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ (A : Type) [CommRing A] [Algebra (Polynomial T) A] [Algebra T A] [IsScalarTower T (Polynomial T) A], SH A → GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap (Polynomial T) A) → ∀ n i : ℤ, 2 ≤ n → Subsingleton (Ht q (sp (TensorProduct T (FractionRing T) A)) n i) := by
  intro q _ T _ _ _ hA hq A _ _ _ _ _ hind n i hn
  haveI : IsAlgClosed (FractionRing T) := GlobalTheory.isAlgClosed_fractionRing_of_AIC T hA
  have hqK : IsUnit (q : FractionRing T) := by simpa using hq.map (algebraMap T (FractionRing T))
  have h2 := GlobalTheory.isIndEtale_tensorProduct_left (Polynomial T) A
    (TensorProduct T (Polynomial T) (FractionRing T)) hind
  let eX : TensorProduct (Polynomial T) (TensorProduct T (Polynomial T) (FractionRing T)) A ≃+*
      TensorProduct T (FractionRing T) A :=
    (Algebra.TensorProduct.comm (Polynomial T) _ A).toRingEquiv.trans
      ((Algebra.TensorProduct.cancelBaseChange T (Polynomial T) (Polynomial T) A (FractionRing T)).toRingEquiv.trans
        (Algebra.TensorProduct.comm T A (FractionRing T)).toRingEquiv)
  let eK : Polynomial (FractionRing T) ≃+* TensorProduct T (Polynomial T) (FractionRing T) :=
    (polyEquivTensor T (FractionRing T)).toRingEquiv.trans
      (Algebra.TensorProduct.comm T (FractionRing T) (Polynomial T)).toRingEquiv
  obtain ⟨J, _, _, D, t, s, hs, hst⟩ := h2
  let c : Cocone D := ⟨CommRingCat.of (TensorProduct T (FractionRing T) A),
    s ≫ (Functor.const J).map (CommRingCat.ofHom (eX : _ →+* _))⟩
  have hc : IsColimit c := hs.ofIsoColimit (Cocones.ext eX.toCommRingCatIso (fun j => rfl))
  have hqA : IsUnit (q : c.pt) := by
    simpa using hq.map (algebraMap T (TensorProduct T (FractionRing T) A))
  suffices h0 : ∀ x : Ht q (sp (TensorProduct T (FractionRing T) A)) n i, x = 0 from
    ⟨fun x y => by rw [h0 x, h0 y]⟩
  intro x
  obtain ⟨j, z, hz⟩ := (GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity q D c hc n i).1 x hqA
  let g : TensorProduct T (Polynomial T) (FractionRing T) →+* D.obj j := (t.app j).hom
  letI : Algebra (Polynomial (FractionRing T)) (D.obj j) := (g.comp eK.toRingHom).toAlgebra
  haveI : Algebra.Etale (Polynomial (FractionRing T)) (D.obj j) := by
    rw [← RingHom.etale_algebraMap]
    exact RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective eK.bijective) (hst j).1
  haveI := GlobalTheory.T.tateTwistCohomology_subsingleton_etale_over_polynomial_algClosed q (FractionRing T) (D.obj j) hqK n i hn
  rw [← hz, Subsingleton.elim z 0, map_zero]

end GlobalTheory.EtC.GenFibreLine
