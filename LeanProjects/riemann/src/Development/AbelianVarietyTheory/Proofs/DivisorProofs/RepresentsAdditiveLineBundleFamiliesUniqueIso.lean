import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

theorem cls_eq_evc_id {S : Scheme.{0}} {A T : Over S} {M : LB (A ⊗ T).left} (hM : M.IsLB) :
    cls M hM = evc hM (fst A T) (snd A T ≫ 𝟙 T) := by
  rw [Category.comp_id, evc, lift_fst_snd, Over.id_left, pull_id]

theorem cls_trans {S : Scheme.{0}} {A B B' B'' : Over S} {P : LB (A ⊗ B).left} {P' : LB (A ⊗ B').left}
    {Q : LB (A ⊗ B'').left} (hP : P.IsLB) (hP' : P'.IsLB) (hQ : Q.IsLB) (x : B ⟶ B') (y : B' ⟶ B'')
    (hx : LBIso P (ev P' (fst A B) (snd A B ≫ x))) (hy : LBIso P' (ev Q (fst A B') (snd A B' ≫ y))) :
    LBIso P (ev Q (fst A B) (snd A B ≫ x ≫ y)) := by
  refine (cls_eq_iff hP (pull_isLB hQ _)).1 ?_
  rw [(cls_eq_iff hP (pull_isLB hP' _)).2 hx, cls_ev hP', cls_ev hQ, evc,
    (cls_eq_iff hP' (pull_isLB hQ _)).2 hy, cls_ev hQ, pull_evc, lift_fst, lift_snd_assoc, Category.assoc]

theorem rep_unique (S : Scheme.{0}) (A B B' S' : Over S) [GrpObj A] (b : B ⟶ S') (P : LB (A ⊗ B).left)
    (b' : B' ⟶ S') (P' : LB (A ⊗ B').left) (h : Rep A b P) (h' : Rep A b' P') :
    ∃ e : B ≅ B', e.hom ≫ b' = b ∧ Same A P P' (𝟙 B) e.hom := by
  have hP := h.fam.isLB
  have hP' := h'.fam.isLB
  obtain ⟨x, ⟨hxb, hxP⟩, -⟩ := h'.univ B b P h.fam
  obtain ⟨y, ⟨hyb, hyP⟩, -⟩ := h.univ B' b' P' h'.fam
  have idB : LBIso P (ev P (fst A B) (snd A B ≫ 𝟙 B)) :=
    (cls_eq_iff hP (pull_isLB hP _)).1 (cls_eq_evc_id hP)
  have idB' : LBIso P' (ev P' (fst A B') (snd A B' ≫ 𝟙 B')) :=
    (cls_eq_iff hP' (pull_isLB hP' _)).1 (cls_eq_evc_id hP')
  have hxy : x ≫ y = 𝟙 B :=
    (h.univ B b P h.fam).unique ⟨by rw [Category.assoc, hyb, hxb], cls_trans hP hP' hP x y hxP hyP⟩
      ⟨Category.id_comp _, idB⟩
  have hyx : y ≫ x = 𝟙 B' :=
    (h'.univ B' b' P' h'.fam).unique ⟨by rw [Category.assoc, hxb, hyb], cls_trans hP' hP hP' y x hyP hxP⟩
      ⟨Category.id_comp _, idB'⟩
  exact ⟨⟨x, y, hxy, hyx⟩, hxb, (same_id_iff hP hP' x).2 hxP⟩

end GlobalTheory.DualCon
