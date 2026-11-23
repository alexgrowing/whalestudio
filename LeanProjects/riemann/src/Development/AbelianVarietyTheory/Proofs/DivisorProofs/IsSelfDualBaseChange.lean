import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobPullHomExtAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.CurveRootGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbDatum

theorem evc_pull_eq_pull_evc {T T' : Scheme.{0}} {A B Y : Over T} {A' B' Y' : Over T'}
    {f : A'.left ⟶ A.left} {g : B'.left ⟶ B.left} {m : (A' ⊗ B').left ⟶ (A ⊗ B).left}
    (h₁ : m ≫ (fst A B).left = (fst A' B').left ≫ f) (h₂ : m ≫ (snd A B).left = (snd A' B').left ≫ g)
    {P : LB (A ⊗ B).left} (hP : P.IsLB) (hP' : (P.pull m).IsLB) (u : Y'.left ⟶ Y.left)
    (a : Y' ⟶ A') (t : Y' ⟶ B') (a₀ : Y ⟶ A) (t₀ : Y ⟶ B)
    (ha : a.left ≫ f = u ≫ a₀.left) (ht : t.left ≫ g = u ≫ t₀.left) :
    evc hP' a t = CechPic.pull u (evc hP a₀ t₀) := by
  have e : (lift a t).left ≫ m = u ≫ (lift a₀ t₀).left := by
    apply left_ext
    · rw [Category.assoc, h₁, lift_left_fst_assoc, ha, Category.assoc, lift_left_fst]
    · rw [Category.assoc, h₂, lift_left_snd_assoc, ht, Category.assoc, lift_left_snd]
  rw [evc, evc, cls_pull hP, ← pull_comp, ← pull_comp, e]

theorem isSelfDual_baseChange (O : Type) [CommRing O] (c : O →+* O) (T T' : Scheme.{0}) (b : T' ⟶ T)
    (A : Over T) [GrpObj A] (A' : Over T') [GrpObj A'] (j : OAct O A) (j' : OAct O A') (φ : A'.left ⟶ A.left)
    (hφ : IsGrpPullback A' A b φ) (hj : IsActPull j' j b φ) (P : LB (A ⊗ A).left)
    (m : (A' ⊗ A').left ⟶ (A ⊗ A).left) (h₁ : m ≫ (fst A A).left = (fst A' A').left ≫ φ)
    (h₂ : m ≫ (snd A A).left = (snd A' A').left ≫ φ) (h : IsSelfDual c j P) : IsSelfDual c j' (P.pull m) := by
  obtain ⟨hd, hs, ha⟩ := h
  have hP := hd.isLB
  have hP' : (P.pull m).IsLB := pull_isLB hP m
  refine ⟨hd.baseChange hφ hφ h₁ h₂ hP' ((cls_eq_iff hP' hP').1 rfl), ?_, fun x ↦ ?_⟩
  · have e : evc hP (snd A A) (fst A A) = cls P hP := (cls_eq_iff (pull_isLB hP _) hP).2 hs
    refine (cls_eq_iff (pull_isLB hP' _) hP').1 ?_
    rw [cls_ev hP', evc_pull_eq_pull_evc h₁ h₂ hP hP' m _ _ (snd A A) (fst A A) h₂.symm h₁.symm, e, cls_pull hP]
  · have e : evc hP (fst A A ≫ j.act x) (snd A A) = evc hP (fst A A) (snd A A ≫ j.act (c x)) :=
      (cls_eq_iff (pull_isLB hP _) (pull_isLB hP _)).2 (ha x)
    refine (cls_eq_iff (pull_isLB hP' _) (pull_isLB hP' _)).1 ?_
    rw [cls_ev hP', cls_ev hP',
      evc_pull_eq_pull_evc h₁ h₂ hP hP' m _ _ (fst A A ≫ j.act x) (snd A A) ?_ h₂.symm,
      evc_pull_eq_pull_evc h₁ h₂ hP hP' m _ _ (fst A A) (snd A A ≫ j.act (c x)) h₁.symm ?_, e]
    · rw [Over.comp_left, Over.comp_left, Category.assoc, hj.2, ← Category.assoc, ← h₂, Category.assoc]
    · rw [Over.comp_left, Over.comp_left, Category.assoc, hj.2, ← Category.assoc, ← h₁, Category.assoc]

end GlobalTheory.AbDatum
