import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.DualCon

theorem Rep.baseChange (S : Scheme.{0}) (A B S' S'' B'' : Over S) [GrpObj A] (b : B ⟶ S')
    (P : LB (A ⊗ B).left) (h : S'' ⟶ S') (k : B'' ⟶ B) (b'' : B'' ⟶ S'') (hR : Rep A b P)
    (hpb : IsPullback k b'' b h) : Rep A b'' (ev P (fst A B'') (snd A B'' ≫ k)) := by
  have hP : P.IsLB := hR.fam.isLB
  have hP' : (ev P (fst A B'') (snd A B'' ≫ k)).IsLB := pull_isLB hP _
  have key : ∀ (Y : Over S) (a : Y ⟶ A) (y : Y ⟶ B''), evc hP' a y = evc hP a (y ≫ k) := by
    intro Y a y
    rw [evc_ev hP, lift_fst, lift_snd_assoc]
  have iso : ∀ (T : Over S) (N : LB (A ⊗ T).left) (hN : N.IsLB) (y : T ⟶ B''),
      LBIso N (ev (ev P (fst A B'') (snd A B'' ≫ k)) (fst A T) (snd A T ≫ y)) ↔
        LBIso N (ev P (fst A T) (snd A T ≫ y ≫ k)) := by
    intro T N hN y
    rw [← cls_eq_iff hN (pull_isLB hP' _), ← cls_eq_iff hN (pull_isLB hP _), cls_ev hP', cls_ev hP, key,
      Category.assoc]
  refine ⟨⟨hP', (isAdditive_iff hP').2 fun Y a a' t ↦ ?_⟩, fun T t N hN ↦ ?_⟩
  · rw [key, key, key]
    exact (isAdditive_iff hP).1 hR.fam.add Y a a' (t ≫ k)
  · obtain ⟨x, ⟨hx1, hx2⟩, hu⟩ := hR.univ T (t ≫ h) N hN
    refine ⟨hpb.lift x t hx1, ⟨hpb.lift_snd _ _ _, (iso T N hN.isLB _).2 ?_⟩, fun y ⟨hy1, hy2⟩ ↦ ?_⟩
    · rw [hpb.lift_fst]
      exact hx2
    · have e : y ≫ k = x := hu (y ≫ k) ⟨by rw [Category.assoc, hpb.w, ← Category.assoc, hy1],
        (iso T N hN.isLB y).1 hy2⟩
      exact hpb.hom_ext (by rw [e, hpb.lift_fst]) (by rw [hy1, hpb.lift_snd])

end GlobalTheory.DualCon
