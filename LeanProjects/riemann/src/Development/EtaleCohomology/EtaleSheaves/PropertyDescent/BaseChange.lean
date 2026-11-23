import Development.EtaleCohomology.EtaleSheaves.PropertyDescent

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafPropsDescendPf

namespace LateralTheory.E.LeafPropsDescendPf.BaseChange

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

theorem toR_incl {R R' : Subalgebra k Ω} (hR : R ≤ R') : toR R' ≫ incl hR = toR R := by
  rw [← Spec.map_comp]
  rfl

theorem cond {R R' : Subalgebra k Ω} (hR : R ≤ R') {C D : Scheme.{0}} {g : D ⟶ Sp R} {v : C ⟶ D}
    {c : C ⟶ Sp Ω} (h : IsPullback v c g (toR R)) : v ≫ g = (c ≫ toR R') ≫ incl hR := by
  rw [Category.assoc, toR_incl]; exact h.w

theorem sq {R R' : Subalgebra k Ω} (hR : R ≤ R') {C D : Scheme.{0}} {g : D ⟶ Sp R} {v : C ⟶ D}
    {c : C ⟶ Sp Ω} (h : IsPullback v c g (toR R)) :
    IsPullback (pullback.lift v (c ≫ toR R') (cond hR h)) c (pullback.snd g (incl hR)) (toR R') := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback g (incl hR))
  rw [pullback.lift_fst, toR_incl]; exact h

theorem leafBaseChangePre : LeafBaseChangePre := by
  intro k _ Ω _ _ R R' hR C0 C1 C2 c0 γ1 γ2 D0 D1 D2 q d1 d2 v0 v1 v2 hpre
  obtain ⟨-, -, -, p0, p1, p2, h1, h2⟩ := hpre
  let e1 : pullback (d1 ≫ q) (incl hR) ⟶ pullback q (incl hR) :=
    pullback.map _ _ _ _ d1 (𝟙 _) (𝟙 _) (by simp) (by simp)
  let e2 : pullback (d2 ≫ d1 ≫ q) (incl hR) ⟶ pullback (d1 ≫ q) (incl hR) :=
    pullback.map _ _ _ _ d2 (𝟙 _) (𝟙 _) (by simp) (by simp)
  have E1 : e1 ≫ pullback.snd q (incl hR) = pullback.snd (d1 ≫ q) (incl hR) := by
    simp only [e1, pullback.map, pullback.lift_snd, Category.comp_id]
  have E2 : e2 ≫ e1 ≫ pullback.snd q (incl hR) = pullback.snd (d2 ≫ d1 ≫ q) (incl hR) := by
    rw [E1]; simp only [e2, pullback.map, pullback.lift_snd, Category.comp_id]
  refine ⟨_, _, _, pullback.snd q (incl hR), e1, e2, pullback.lift v0 (c0 ≫ toR R') (cond hR p0),
    pullback.lift v1 ((γ1 ≫ c0) ≫ toR R') (cond hR p1), pullback.lift v2 ((γ2 ≫ γ1 ≫ c0) ≫ toR R') (cond hR p2),
    pullback.fst _ _, pullback.fst _ _, pullback.fst _ _, ⟨sq hR p0, ?_, ?_, ?_, ?_⟩,
    IsPullback.of_hasPullback _ _, ?_, ?_⟩
  · rw [E1]; exact sq hR p1
  · rw [E2]; exact sq hR p2
  · apply pullback.hom_ext
    · simp only [e1, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]; exact h1
    · simp only [e1, pullback.map, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
        Category.comp_id]
  · apply pullback.hom_ext
    · simp only [e2, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]; exact h2
    · simp only [e2, pullback.map, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
        Category.comp_id]
  · rw [E1]; exact IsPullback.of_hasPullback _ _
  · rw [E2]; exact IsPullback.of_hasPullback _ _

theorem LeafPropsDescend_of (hS : LeafSpreadOne) : LeafPropsDescend :=
  LateralTheory.E.LeafPropsDescendPf.LeafPropsDescend_of hS leafBaseChangePre

end LateralTheory.E.LeafPropsDescendPf.BaseChange

end
