import Development.EtaleCohomology.CohomologicalPurity.LeafHsSumPfR

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut.PbSumPf

theorem types_univ {A : Type} {F : Discrete A ⥤ Type} (c : Cocone F) (hc : IsColimit c) :
    IsUniversalColimit c := by
  intro F' c' α f e _ H
  let i' : Discrete.functor (fun a => F'.obj ⟨a⟩) ≅ F' := Discrete.natIso (fun _ => Iso.refl _)
  let i : Discrete.functor (fun a => F.obj ⟨a⟩) ≅ F := Discrete.natIso (fun _ => Iso.refl _)
  let d : Cofan (fun a => F'.obj ⟨a⟩) := (Cocone.precompose i'.hom).obj c'
  let b : Cofan (fun a => F.obj ⟨a⟩) := (Cocone.precompose i.hom).obj c
  have hb : IsColimit b := (IsColimit.precomposeHomEquiv i c).symm hc
  have hd : ∀ a z, d.inj a z = c'.ι.app ⟨a⟩ z := fun _ _ => rfl
  have hbi : ∀ a z, b.inj a z = c.ι.app ⟨a⟩ z := fun _ _ => rfl
  have e1 : ∀ j x, c.ι.app j (α.app j x) = f (c'.ι.app j x) := fun j x => by
    have := ConcreteCategory.congr_hom (NatTrans.congr_app e j) x
    simpa using this
  refine ⟨(IsColimit.precomposeHomEquiv i' c') ((Cofan.nonempty_isColimit_iff_bijective_fromSigma d).2 ⟨?_, ?_⟩).some⟩
  · rintro ⟨a, z⟩ ⟨a', w⟩ h
    change d.inj a z = d.inj a' w at h
    rw [hd, hd] at h
    have h2 : b.inj a (α.app ⟨a⟩ z) = b.inj a' (α.app ⟨a'⟩ w) := by
      rw [hbi, hbi, e1, e1, h]
    obtain rfl := Cofan.eq_of_inj_apply_eq_of_isColimit hb _ _ h2
    have h3 := Cofan.inj_injective_of_isColimit hb a h2
    have := Types.ext_of_isPullback (H ⟨a⟩) h h3
    subst this
    rfl
  · intro y
    obtain ⟨a, x, hx⟩ := Cofan.inj_jointly_surjective_of_isColimit hb (f y)
    rw [hbi] at hx
    obtain ⟨z, hz1, _⟩ := Types.exists_of_isPullback (H ⟨a⟩) y x hx.symm
    exact ⟨⟨a, z⟩, hz1⟩

theorem univ_of_eval {J C D : Type*} [Category J] [Category C] [Category D] [HasPullbacks D]
    (F : J ⥤ C ⥤ D) (c : Cocone F)
    (hc : ∀ x : C, IsUniversalColimit (((evaluation C D).obj x).mapCocone c)) : IsUniversalColimit c := by
  intro F' c' α f e hα H
  exact ⟨evaluationJointlyReflectsColimits _ fun x =>
    (hc x (((evaluation C D).obj x).mapCocone c') (Functor.whiskerRight α _) (((evaluation C D).obj x).map f)
      (by ext y; dsimp; exact NatTrans.congr_app (NatTrans.congr_app e y) x)
      (hα.whiskerRight _) fun j => (H j).map ((evaluation C D).obj x)).some⟩

theorem spc_univ {A : Type} (F : Discrete A ⥤ Spc) (c : Cocone F) (hc : IsColimit c) : IsUniversalColimit c :=
  univ_of_eval (C := SimplexCategoryᵒᵖ) (D := PSh) F c fun n =>
    univ_of_eval (C := Scheme.{0}ᵒᵖ) (D := Type) _ _ fun Y =>
      types_univ _ (isColimitOfPreserves _ (isColimitOfPreserves ((evaluation _ _).obj n) hc))

theorem pb_of_eq {C : Type*} [Category C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f f' : X ⟶ Z} {g : Y ⟶ Z}
    (e : f = f') (hp : IsPullback fst snd f' g) : IsPullback fst snd f g := by subst e; exact hp

theorem pb_of_eq_snd {C : Type*} [Category C] {P X Y Z : C} {fst : P ⟶ X} {snd snd' : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (e : snd = snd') (hp : IsPullback fst snd' f g) : IsPullback fst snd f g := by subst e; exact hp

end LateralTheory.CohomologicalPurity.TubeCut.PbSumPf

namespace LateralTheory.CohomologicalPurity.TubeCut
open PbSumPf

theorem LeafPbSum_of : LeafPbSum := by
  intro X U A E c hc π π' h
  have hS := (leafDiscSumH A E c hc).some
  have Uv := spc_univ _ _ hS
  let g := sch.map U.ι
  refine Uv (Cofan.mk (abv U (E := disc.obj c.pt) (disc.map π)).left
      fun a => (abvRel U (disc.map (c.inj a)) (disc.map (π' a)) (disc.map π) (h a)).left)
    (Discrete.natTrans fun a => pullback.fst (disc.map (π' a.as)) g)
    (pullback.fst (disc.map π) g) ?_ (.of_discrete _) ?_
  · apply NatTrans.ext; funext ⟨a⟩
    exact (pullback.lift_fst (f := disc.map π) (g := g) _ _ _).symm
  · rintro ⟨a⟩
    have outer : IsPullback (pullback.fst (disc.map (π' a)) g)
        ((abvRel U (disc.map (c.inj a)) (disc.map (π' a)) (disc.map π) (h a)).left ≫ pullback.snd (disc.map π) g)
        (disc.map (c.inj a) ≫ disc.map π) g := by
      have e2 : (abvRel U (disc.map (c.inj a)) (disc.map (π' a)) (disc.map π) (h a)).left ≫ pullback.snd (disc.map π) g
          = pullback.snd (disc.map (π' a)) g := (pullback.lift_snd _ _ _).trans (Category.comp_id _)
      exact pb_of_eq_snd e2 (pb_of_eq (h a) (IsPullback.of_hasPullback _ _))
    have sq := IsPullback.of_bot outer (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback (disc.map π) g)
    exact sq.flip

end LateralTheory.CohomologicalPurity.TubeCut
