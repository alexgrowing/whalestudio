import Development.EtaleCohomology.EtaleSheaves.GlobalPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.GlobalPf

namespace LateralTheory.E.AffinePf

theorem eqv_of_sq (R : Type) [CommRing R] (F : Shv R) {E₁ E₂ E₁' E₂' : Spc} (f : E₁ ⟶ E₂) (f' : E₁' ⟶ E₂')
    (a : E₁ ≅ E₁') (b : E₂ ≅ E₂') (h : f ≫ b.hom = a.hom ≫ f') (hf : Eqv R f' F) : Eqv R f F := fun n => by
  have hiso : ∀ {X Y : Spc} (e : X ≅ Y), Function.Bijective (pull R e.hom F n) := fun e => by
    refine ⟨Function.LeftInverse.injective (g := pull R e.inv F n) fun x => ?_,
      Function.RightInverse.surjective (g := pull R e.inv F n) fun x => ?_⟩
    · rw [← pull_comp, e.inv_hom_id, pull_id]
    · rw [← pull_comp, e.hom_inv_id, pull_id]
  have hf2 : f = a.hom ≫ f' ≫ b.inv := by rw [← Category.assoc, ← h]; simp
  have : ⇑(pull R f F n) = pull R a.hom F n ∘ pull R f' F n ∘ pull R b.inv F n := by
    funext x; rw [hf2]; simp only [Function.comp_apply]; rw [pull_comp, pull_comp]
  rw [this]
  exact (hiso a).comp ((hf n).comp (hiso b.symm))

theorem ι_comp_eq {T : CommRingCat.{0}} {X : Scheme.{0}} (p : X ⟶ Spec T) (V : X.Opens) (hV : IsAffineOpen V) :
    V.ι ≫ p = hV.isoSpec.hom ≫ Spec.map (gam p V) := by
  have h1 : Spec.map (gam p V) = hV.fromSpec ≫ p := by
    have := IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top (Spec T)) hV (by simp)
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at this
    rw [gam, Spec.map_comp]
    exact this
  rw [h1, ← Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec]

theorem Affine_of : Affine := by
  intro q i T K k X p V hV hb
  have hpo := IsPushout.of_hasPushout k (gam p V)
  have hre := hb _ _ _ hpo
  have hS := isPullback_SpecMap_of_isPushout _ _ _ _ hpo.flip
  have h1 := (isPullback_morphismRestrict (pullback.fst p (Spec.map k)) V).paste_vert
    (IsPullback.of_hasPullback p (Spec.map k))
  have h2 : IsPullback hV.isoSpec.hom (V.ι ≫ p) (Spec.map (gam p V)) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [ι_comp_eq p V hV, Category.comp_id]⟩
  have h3 := h1.paste_horiz h2
  rw [Category.comp_id] at h3
  refine eqv_of_sq _ _ _ (sch.map (Spec.map (pushout.inr k (gam p V))))
    (sch.mapIso (h3.isoIsPullback _ _ hS)) (sch.mapIso hV.isoSpec) ?_ hre
  simp only [Functor.mapIso_hom, ← Functor.map_comp, IsPullback.isoIsPullback_hom_fst]

end LateralTheory.E.AffinePf

end
