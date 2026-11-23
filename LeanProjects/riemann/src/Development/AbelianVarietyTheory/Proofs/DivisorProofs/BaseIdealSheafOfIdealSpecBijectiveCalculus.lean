import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdealSheafAwayFromP
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FormalAlg

theorem baseIdeal_sup {R : Type} [CommRing R] {W : Scheme.{0}} (f : W ⟶ Spec (CommRingCat.of R))
    (a b : Ideal R) : baseIdeal f (a ⊔ b) = baseIdeal f a ⊔ baseIdeal f b := by
  refine Scheme.IdealSheafData.ext (funext fun U => ?_)
  rw [Scheme.IdealSheafData.ideal_sup, Pi.sup_apply, baseIdeal_ideal, baseIdeal_ideal, baseIdeal_ideal,
    Ideal.map_sup]

theorem idealSheaf_ext_top {X : Scheme.{0}} [IsAffine X] {I J : X.IdealSheafData}
    (h : I.ideal ⟨⊤, isAffineOpen_top X⟩ = J.ideal ⟨⊤, isAffineOpen_top X⟩) : I = J :=
  Scheme.IdealSheafData.ext_of_iSup_eq_top (ι := Unit) (fun _ => ⟨⊤, isAffineOpen_top X⟩) iSup_const fun _ => h

theorem appLE_specMap_fromSpec {W : Scheme.{0}} (U : W.Opens) (hU : IsAffineOpen U) (C : Type) [CommRing C]
    (φ : Γ(W, U) →+* C) (h : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤
      (Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec) ⁻¹ᵁ U) :
    ((Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec).appLE U ⊤ h).hom =
      (cst (𝟙 (Spec (CommRingCat.of C))) ⊤).comp φ := by
  have hfs : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := by rw [hU.fromSpec_preimage_self]
  have m1 : (Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec).appLE U ⊤ h =
      hU.fromSpec.appLE U ⊤ hfs ≫ (Spec.map (CommRingCat.ofHom φ)).appTop := by
    rw [Scheme.Hom.comp_appLE]
    rfl
  have m2 : hU.fromSpec.appLE U ⊤ hfs = (Scheme.ΓSpecIso Γ(W, U)).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    convert Category.comp_id _
    exact (Spec Γ(W, U)).presheaf.map_id _
  have m3 : (Scheme.ΓSpecIso Γ(W, U)).inv ≫ (Spec.map (CommRingCat.ofHom φ)).appTop =
      CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).inv :=
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)).symm
  rw [m1, m2, m3]
  ext x
  simp only [cst, RingHom.comp_apply, rs_self]
  rfl

theorem specIdeal :
    (∀ (C : Type) [CommRing C], Function.Bijective (fun a : Ideal C => baseIdeal (𝟙 (Spec (CommRingCat.of C))) a) ∧ (∀ a b : Ideal C, baseIdeal (𝟙 (Spec (CommRingCat.of C))) (a ⊔ b) = baseIdeal (𝟙 _) a ⊔ baseIdeal (𝟙 _) b)) ∧ (∀ (W : Scheme.{0}) (V : W.affineOpens) (C : Type) [CommRing C] (φ : Γ(W, V.1) →+* C) (J : W.IdealSheafData), J.comap (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) = baseIdeal (𝟙 (Spec (CommRingCat.of C))) ((J.ideal V).map φ)) := by
  refine ⟨fun C _ => ⟨⟨fun a b hab => ?_, fun J => ?_⟩, fun a b => baseIdeal_sup _ a b⟩, fun W V C _ φ J => ?_⟩
  · have hb := cst_bijective (𝟙 (Spec (CommRingCat.of C))) (W := ⊤) rfl
    have e := congrArg (fun I : (Spec (CommRingCat.of C)).IdealSheafData => I.ideal ⟨⊤, isAffineOpen_top _⟩) hab
    simp only [baseIdeal_ideal] at e
    rw [← Ideal.comap_map_of_bijective _ hb (I := a), e, Ideal.comap_map_of_bijective _ hb]
  · have hb := cst_bijective (𝟙 (Spec (CommRingCat.of C))) (W := ⊤) rfl
    refine ⟨(J.ideal ⟨⊤, isAffineOpen_top _⟩).comap (cst (𝟙 (Spec (CommRingCat.of C))) ⊤), idealSheaf_ext_top ?_⟩
    simp only [baseIdeal_ideal]
    exact Ideal.map_comap_of_surjective _ hb.2 _
  · have h : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) ⁻¹ᵁ V.1 :=
      fun x _ => V.2.range_fromSpec.subset ⟨_, rfl⟩
    refine idealSheaf_ext_top ?_
    rw [GlobalTheory.Principalise.comapIdealAffine J _ V ⟨⊤, isAffineOpen_top _⟩ h, baseIdeal_ideal, Ideal.map_map,
      appLE_specMap_fromSpec V.1 V.2 C φ h]

end GlobalTheory.FormalAlg
