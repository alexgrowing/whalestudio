import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleEquivalenceSchemeOfStrictlyHenselianStalksStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIndEtaleAlgebraOfStrictlyHenselianEtaleStalkAfStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.LocGlobRing

noncomputable def pbIso (A X O : Type) [CommRing A] [CommRing X] [CommRing O] [Algebra A X] [Algebra A O]
    (g : Spec (CommRingCat.of X) ⟶ Spec (CommRingCat.of A)) (hg : g = Spec.map (CommRingCat.ofHom (algebraMap A X))) :
    pullback g (Spec.map (CommRingCat.ofHom (algebraMap A O))) ≅ Spec (CommRingCat.of (O ⊗[A] X)) :=
  pullback.congrHom hg rfl ≪≫ pullbackSymmetry _ _ ≪≫ pullbackSpecIso A O X

theorem pbIso_inv_fst (A X O : Type) [CommRing A] [CommRing X] [CommRing O] [Algebra A X] [Algebra A O]
    (g : Spec (CommRingCat.of X) ⟶ Spec (CommRingCat.of A)) (hg : g = Spec.map (CommRingCat.ofHom (algebraMap A X))) :
    (pbIso A X O g hg).inv ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : X →ₐ[A] O ⊗[A] X).toRingHom) := by
  subst hg
  simp [pbIso, pullback.congrHom_inv, pullbackSpecIso_inv_snd]

theorem pbIso_inv_snd (A X O : Type) [CommRing A] [CommRing X] [CommRing O] [Algebra A X] [Algebra A O]
    (g : Spec (CommRingCat.of X) ⟶ Spec (CommRingCat.of A)) (hg : g = Spec.map (CommRingCat.ofHom (algebraMap A X))) :
    (pbIso A X O g hg).inv ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : O →+* O ⊗[A] X)) := by
  subst hg
  simp [pbIso, pullback.congrHom_inv, pullbackSpecIso_inv_fst]

end GlobalTheory.LocGlobRing

namespace GlobalTheory.LocGlobRing

theorem square (A B C O : Type) [CommRing A] [CommRing B] [CommRing C] [CommRing O] [Algebra A B] [Algebra A C] [Algebra A O]
    (φ : B →ₐ[A] C)
    (hC : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) = Spec.map (CommRingCat.ofHom (algebraMap A C)))
    (h₁ h₂) :
    (pbIso A C O _ hC).inv ≫ pullback.map (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom (algebraMap A O))) (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom (algebraMap A O))) (Spec.map (CommRingCat.ofHom φ.toRingHom)) (𝟙 _) (𝟙 _) h₁ h₂ =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A O) φ).toRingHom) ≫ (pbIso A B O _ rfl).inv := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pbIso_inv_fst, Category.assoc, pbIso_inv_fst,
      ← Spec.map_comp, ← Spec.map_comp]
    congr 1
  · rw [Category.assoc, pullback.lift_snd, Category.comp_id, pbIso_inv_snd, Category.assoc, pbIso_inv_snd,
      ← Spec.map_comp]
    congr 1
    ext x
    simp

end GlobalTheory.LocGlobRing

theorem GlobalTheory.LocGlobRing.main : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (A B C : Type) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C] (φ : B →ₐ[A] C), (∀ (O : Type) [CommRing O] [Algebra A O], SH O → IndEt A O → Eqv R (spMap (Algebra.TensorProduct.map (AlgHom.id A O) φ).toRingHom) F) → Eqv R (spMap φ.toRingHom) F := by
  intro R _ F hF A B C _ _ _ _ _ φ hyp
  have hC : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) =
      Spec.map (CommRingCat.ofHom (algebraMap A C)) := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    simp
  refine GlobalTheory.T.etaleEquivalence_scheme_of_strictlyHenselian_stalks R F hF (Spec (CommRingCat.of C)) (Spec (CommRingCat.of B)) (Spec (CommRingCat.of A))
    (Spec.map (CommRingCat.ofHom φ.toRingHom)) (Spec.map (CommRingCat.ofHom (algebraMap A B))) ?_
  intro O _ s hs
  obtain ⟨inst, hSH, hInd, rfl⟩ := GlobalTheory.T.isIndEtaleAlgebra_of_strictlyHenselianEtaleStalk_affine A O s hs
  have h := @hyp O _ inst hSH hInd
  have eb := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties R F
  rw [← Iso.hom_inv_id_assoc (GlobalTheory.LocGlobRing.pbIso A C O _ hC) (pullback.map _ _ _ _ _ _ _ _ _),
    GlobalTheory.LocGlobRing.square A B C O φ hC, Functor.map_comp, Functor.map_comp]
  exact (eb.2.1 _ _ _ _ _).1 (eb.1 _ _ _ inferInstance) ((eb.2.1 _ _ _ _ _).1 h (eb.1 _ _ _ inferInstance))
