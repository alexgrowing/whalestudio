import Development.EtaleCohomology.CohomologicalPurity.LeafFstHocPf

noncomputable section
open CategoryTheory Limits GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem ev_pb {P Q R : PSh} (f : P ⟶ R) (g : Q ⟶ R) (U : AlgebraicGeometry.Scheme.{0}ᵒᵖ) :
    IsPullback ((pullback.fst f g).app U) ((pullback.snd f g).app U) (f.app U) (g.app U) :=
  (IsPullback.of_hasPullback f g).map ((evaluation _ _).obj U)

theorem ev_cofan {A : Type} {X : A → PSh} (c : Cofan X) (hc : IsColimit c) (U : AlgebraicGeometry.Scheme.{0}ᵒᵖ) :
    Nonempty (IsColimit (Cofan.mk (c.pt.obj U) fun a => (c.inj a).app U)) :=
  ⟨(isColimitMapCoconeCofanMkEquiv ((evaluation _ _).obj U) X c.inj).1
    (isColimitOfPreserves ((evaluation _ _).obj U) hc)⟩

theorem leafUnivSum : LeafUnivSum := by
  intro A X c ⟨hc⟩ Y G f g
  let ι : ∀ a, pullback (c.inj a ≫ f) g ⟶ pullback f g := fun a =>
    pullback.map (c.inj a ≫ f) g f g (c.inj a) (𝟙 G) (𝟙 Y) (by simp) (by simp)
  have h1 : ∀ a, ι a ≫ pullback.fst f g = pullback.fst _ _ ≫ c.inj a := fun a => by simp only [ι, pullback.map, pullback.lift_fst]
  have h2 : ∀ a, ι a ≫ pullback.snd f g = pullback.snd _ _ := fun a => by simp only [ι, pullback.map, pullback.lift_snd, Category.comp_id]
  change Nonempty (IsColimit (Cofan.mk (pullback f g) ι))
  refine ⟨evaluationJointlyReflectsColimits _ fun U => ?_⟩
  refine (isColimitMapCoconeCofanMkEquiv ((evaluation _ _).obj U) _ ι).2 ?_
  dsimp only [evaluation_obj_obj, evaluation_obj_map]
  have hcU := ev_cofan c hc U
  have f1 : ∀ a z, (pullback.fst f g).app U ((ι a).app U z) =
      (c.inj a).app U ((pullback.fst (c.inj a ≫ f) g).app U z) := fun a z =>
    show ((ι a ≫ pullback.fst f g).app U) z = ((pullback.fst _ _ ≫ c.inj a).app U) z by rw [h1 a]
  have f2 : ∀ a z, (pullback.snd f g).app U ((ι a).app U z) =
      (pullback.snd (c.inj a ≫ f) g).app U z := fun a z =>
    show ((ι a ≫ pullback.snd f g).app U) z = ((pullback.snd (c.inj a ≫ f) g).app U) z by rw [h2 a]
  refine Classical.choice ((Cofan.nonempty_isColimit_iff_bijective_fromSigma
    (Cofan.mk ((pullback f g).obj U) fun j => (ι j).app U)).2 ⟨?_, ?_⟩)
  · rintro ⟨a, z⟩ ⟨b, w⟩ e
    change (ι a).app U z = (ι b).app U w at e
    have e1 := congr_arg ((pullback.fst f g).app U) e
    rw [f1, f1] at e1
    obtain ⟨rfl, hw⟩ := (Cofan.inj_apply_eq_iff_of_isColimit hcU.some _ _).1 e1
    rw [cast_eq] at hw
    have e2 := congr_arg ((pullback.snd f g).app U) e
    rw [f2, f2] at e2
    rw [Types.ext_of_isPullback (ev_pb (c.inj a ≫ f) g U) hw.symm e2]
  · intro p
    obtain ⟨a, y, hy⟩ := Cofan.inj_jointly_surjective_of_isColimit hcU.some ((pullback.fst f g).app U p)
    change (c.inj a).app U y = _ at hy
    obtain ⟨z, hz1, hz2⟩ := Types.exists_of_isPullback (ev_pb (c.inj a ≫ f) g U) y
      ((pullback.snd f g).app U p) (by
        have : ((pullback.fst f g ≫ f).app U) p = ((pullback.snd f g ≫ g).app U) p := by rw [pullback.condition]
        change f.app U ((c.inj a).app U y) = _
        rw [hy]; exact this)
    refine ⟨⟨a, z⟩, ?_⟩
    change (ι a).app U z = p
    refine Types.ext_of_isPullback (ev_pb f g U) ?_ ?_
    · rw [f1, hz1, hy]
    · rw [f2, hz2]

end LateralTheory.CohomologicalPurity.TubeCut
