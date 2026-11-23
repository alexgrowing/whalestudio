import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mum.ThickChart

theorem isPushout_quotMap (R C : Type) [CommRing R] [CommRing C] [Algebra R C] (K : Ideal R) :
    IsPushout (CommRingCat.ofHom (algebraMap R C)) (CommRingCat.ofHom (Ideal.Quotient.mk K))
      (CommRingCat.ofHom (Ideal.Quotient.mk (K.map (algebraMap R C))))
      (CommRingCat.ofHom (Ideal.quotientMap (K.map (algebraMap R C)) (algebraMap R C) Ideal.le_comap_map)) := by
  refine ⟨⟨by ext x; rfl⟩, ⟨PushoutCocone.IsColimit.mk _ (fun s => CommRingCat.ofHom
    (Ideal.Quotient.lift (K.map (algebraMap R C)) s.inl.hom ?_)) ?_ ?_ ?_⟩⟩
  · intro a ha
    have : K.map (algebraMap R C) ≤ RingHom.ker s.inl.hom := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      have h := congrArg (fun f => f.hom x) s.condition
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at h
      rw [Ideal.mem_comap, RingHom.mem_ker, h, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]
    exact this ha
  · intro s
    ext x
    rfl
  · intro s
    ext x
    exact congrArg (fun f => f.hom x) s.condition
  · intro s m h1 _
    ext x
    exact congrArg (fun f => f.hom x) h1

theorem isPullback_quotMap (R C : Type) [CommRing R] [CommRing C] [Algebra R C] (K : Ideal R) :
    IsPullback (spMap (Ideal.Quotient.mk (K.map (algebraMap R C))))
      (spMap (Ideal.quotientMap (K.map (algebraMap R C)) (algebraMap R C) Ideal.le_comap_map))
      (spMap (algebraMap R C)) (spMap (Ideal.Quotient.mk K)) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_quotMap R C K)

theorem thick_chart : ∀ (R' : Type) [CommRing R'] (I : Ideal R') (G' : Over (Sp R')) (C' : Type) [CommRing C'] [Algebra R' C'] (j : Sp C' ⟶ G'.left) [IsOpenImmersion j], j ≫ G'.hom = spMap (algebraMap R' C') → ∀ (e : ℕ), ∃ (je : Sp (C' ⧸ (I ^ (e + 1)).map (algebraMap R' C')) ⟶ (thickObj R' I e G').left) (_ : IsOpenImmersion je), je.opensRange = (pullback.fst G'.hom (thick R' I e)) ⁻¹ᵁ j.opensRange ∧ IsPullback je (spMap (Ideal.Quotient.mk ((I ^ (e + 1)).map (algebraMap R' C')))) (pullback.fst G'.hom (thick R' I e)) j ∧ je ≫ (thickObj R' I e G').hom = spMap (Ideal.quotientMap ((I ^ (e + 1)).map (algebraMap R' C')) (algebraMap R' C') Ideal.le_comap_map) := by
  intro R' _ I G' C' _ _ j _ hj e
  have outer := isPullback_quotMap R' C' (I ^ (e + 1))
  have right : IsPullback (pullback.snd G'.hom (thick R' I e)) (pullback.fst G'.hom (thick R' I e))
      (thick R' I e) G'.hom := (IsPullback.of_hasPullback G'.hom (thick R' I e)).flip
  have hw : (spMap (Ideal.Quotient.mk ((I ^ (e + 1)).map (algebraMap R' C'))) ≫ j) ≫ G'.hom =
      spMap (Ideal.quotientMap ((I ^ (e + 1)).map (algebraMap R' C')) (algebraMap R' C') Ideal.le_comap_map) ≫
        thick R' I e := by
    rw [Category.assoc, hj]
    exact outer.w
  let je := pullback.lift _ _ hw
  have hje1 : je ≫ pullback.fst G'.hom (thick R' I e) = spMap (Ideal.Quotient.mk ((I ^ (e + 1)).map (algebraMap R' C'))) ≫ j :=
    pullback.lift_fst _ _ _
  have hje2 : je ≫ pullback.snd G'.hom (thick R' I e) =
      spMap (Ideal.quotientMap ((I ^ (e + 1)).map (algebraMap R' C')) (algebraMap R' C') Ideal.le_comap_map) :=
    pullback.lift_snd _ _ _
  have big : IsPullback (je ≫ pullback.snd G'.hom (thick R' I e))
      (spMap (Ideal.Quotient.mk ((I ^ (e + 1)).map (algebraMap R' C')))) (thick R' I e) (j ≫ G'.hom) := by
    rw [hje2, hj]
    exact outer.flip
  have sq : IsPullback je (spMap (Ideal.Quotient.mk ((I ^ (e + 1)).map (algebraMap R' C'))))
      (pullback.fst G'.hom (thick R' I e)) j := IsPullback.of_right big hje1 right
  haveI hoi : IsOpenImmersion je := MorphismProperty.of_isPullback (P := @IsOpenImmersion) sq.flip inferInstance
  refine ⟨je, hoi, ?_, sq, hje2⟩
  have h1 : sq.isoPullback.hom ≫ pullback.fst (pullback.fst G'.hom (thick R' I e)) j = je := sq.isoPullback_hom_fst
  have h2 : Set.range je = Set.range (pullback.fst (pullback.fst G'.hom (thick R' I e)) j) := by
    rw [← h1, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr sq.isoPullback.hom.surjective, Set.image_univ]
  apply TopologicalSpace.Opens.ext
  rw [Scheme.Hom.coe_opensRange, h2, IsOpenImmersion.range_pullbackFst]

end GlobalTheory.Mum.ThickChart
