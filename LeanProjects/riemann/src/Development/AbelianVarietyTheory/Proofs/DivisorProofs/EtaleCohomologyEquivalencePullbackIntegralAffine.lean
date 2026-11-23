import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceBasicPropertiesStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem eqv_pullback_integral_affine : ∀ (R : Type) [CommRing R] (F : Shv R) (A C : Type) [CommRing A] [CommRing C] [Algebra A C],
    (∀ (B : Type) [CommRing B] [Algebra A B] [Algebra.IsIntegral A B],
      Eqv R (spMap (Algebra.TensorProduct.includeRight : B →ₐ[A] C ⊗[A] B).toRingHom) F) →
    ∀ (Z Z' : Scheme.{0}) (h : Z ⟶ Spec (CommRingCat.of A)) (h' : Z' ⟶ Spec (CommRingCat.of C)) (φ : Z' ⟶ Z),
    IsIntegralHom h → IsPullback φ h' h (Spec.map (CommRingCat.ofHom (algebraMap A C))) → Eqv R (sch.map φ) F := by
  intro R _ F A C _ _ _ hB Z Z' h h' φ hh hP
  have E := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties R F
  haveI : IsAffine Z := isAffine_of_isAffineHom h

  set f : CommRingCat.of A ⟶ Γ(Z, ⊤) := Spec.preimage (Z.isoSpec.inv ≫ h) with hf
  have hfh : Z.isoSpec.hom ≫ Spec.map f = h := by
    rw [hf, Spec.map_preimage, Iso.hom_inv_id_assoc]
  have hint : IsIntegralHom (Spec.map f) := by
    have : Spec.map f = Z.isoSpec.inv ≫ h := by rw [hf, Spec.map_preimage]
    rw [this]; infer_instance
  letI : Algebra A Γ(Z, ⊤) := f.hom.toAlgebra
  haveI : Algebra.IsIntegral A Γ(Z, ⊤) := ⟨IsIntegralHom.SpecMap_iff.mp hint⟩
  have hsq := (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct A C Γ(Z, ⊤))).flip
  have hsq' : IsPullback
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : Γ(Z, ⊤) →ₐ[A] C ⊗[A] Γ(Z, ⊤)).toRingHom) ≫ Z.isoSpec.inv)
      (Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)) h
      (Spec.map (CommRingCat.ofHom (algebraMap A C))) := by
    have hr : IsPullback Z.isoSpec.inv (Spec.map f) h (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [← hfh, Iso.inv_hom_id_assoc, Category.comp_id]⟩
    simpa using IsPullback.paste_horiz hsq hr
  let e := IsPullback.isoIsPullback _ _ hP hsq'
  have he : φ = e.hom ≫ (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : Γ(Z, ⊤) →ₐ[A] C ⊗[A] Γ(Z, ⊤)).toRingHom) ≫ Z.isoSpec.inv) :=
    (IsPullback.isoIsPullback_hom_fst _ _ hP hsq').symm
  rw [he, Functor.map_comp, Functor.map_comp]
  refine (E.2.1 _ _ _ _ _).1 (E.1 _ _ _ inferInstance) ((E.2.1 _ _ _ _ _).1 (hB Γ(Z, ⊤)) (E.1 _ _ _ inferInstance))

end GlobalTheory.EtC
