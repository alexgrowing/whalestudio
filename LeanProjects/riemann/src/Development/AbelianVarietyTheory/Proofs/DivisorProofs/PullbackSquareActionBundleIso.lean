import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullback

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RealMult.PullPol

theorem swap_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {φ : G'.left ⟶ G.left}
    {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} (hs : IsSquare φ φ₂) :
    (lift (snd G' G') (fst G' G')).left ≫ φ₂ = φ₂ ≫ (lift (snd G G) (fst G G)).left := by
  apply pullback.hom_ext
  · change _ ≫ φ₂ ≫ (fst G G).left = φ₂ ≫ (lift (snd G G) (fst G G)).left ≫ (fst G G).left
    rw [hs.1, ← Over.comp_left, lift_fst, hs.2, ← Category.assoc, ← Over.comp_left, lift_fst]
  · change _ ≫ φ₂ ≫ (snd G G).left = φ₂ ≫ (lift (snd G G) (fst G G)).left ≫ (snd G G).left
    rw [hs.2, ← Over.comp_left, lift_snd, hs.1, ← Category.assoc, ← Over.comp_left, lift_snd]

theorem act_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {φ : G'.left ⟶ G.left}
    {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} (hs : IsSquare φ φ₂) (u' : G' ⟶ G') (u : G ⟶ G)
    (hu : u'.left ≫ φ = φ ≫ u.left) :
    (lift (fst G' G') (snd G' G' ≫ u')).left ≫ φ₂ = φ₂ ≫ (lift (fst G G) (snd G G ≫ u)).left := by
  apply pullback.hom_ext
  · change _ ≫ φ₂ ≫ (fst G G).left = φ₂ ≫ (lift (fst G G) (snd G G ≫ u)).left ≫ (fst G G).left
    rw [hs.1, ← Category.assoc, ← Over.comp_left, lift_fst, ← Over.comp_left, lift_fst, hs.1]
  · change _ ≫ φ₂ ≫ (snd G G).left = φ₂ ≫ (lift (fst G G) (snd G G ≫ u)).left ≫ (snd G G).left
    rw [hs.2, ← Category.assoc, ← Over.comp_left, lift_snd, ← Over.comp_left, lift_snd, Over.comp_left,
      Over.comp_left, Category.assoc, hu, ← Category.assoc, ← hs.2, Category.assoc]

end GlobalTheory.RealMult.PullPol

namespace GlobalTheory.RealMult.PullPol

open GlobalTheory.CechPic in

theorem pol_pull : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S' : Scheme.{0}} (X : Obj F 𝔠 S) (b : S' ⟶ S) (A' : Over S') [GrpObj A'] [IsCommMonObj A']
    (φ : A'.left ⟶ X.A.left), IsGrpPullback A' X.A b φ → ∀ (rm' : OAct (𝓞 F) A'),
    (∀ a, (rm'.act a).left ≫ φ = φ ≫ (X.rm.act a).left) → ∀ (φ₂ : (G2 A').left ⟶ (G2 X.A).left), IsSquare φ φ₂ →
    ∀ (c c' : 𝔠.elt) (a : 𝓞 F),
      LBIso ((X.P c).pull φ₂) (((X.P c).pull φ₂).pull (lift (snd A' A') (fst A' A')).left) ∧
      LBIso ((X.P c').pull φ₂) (LB.div ((X.P (c + c')).pull φ₂) ((X.P c).pull φ₂)) ∧
      LBIso ((X.P (a • c)).pull φ₂) (((X.P c).pull φ₂).pull (lift (fst A' A') (snd A' A' ≫ rm'.act a)).left) := by
  intro F _ _ 𝔠 S S' X b A' _ _ φ _ rm' hact φ₂ hs c c' a
  have hP := X.isLB
  refine ⟨(cls_eq_iff (pull_isLB (hP c) φ₂) (pull_isLB (pull_isLB (hP c) φ₂) _)).1 ?_,
    (cls_eq_iff (pull_isLB (hP c') φ₂) (LB.isLB_div (pull_isLB (hP _) φ₂) (pull_isLB (hP c) φ₂))).1 ?_,
    (cls_eq_iff (pull_isLB (hP _) φ₂) (pull_isLB (pull_isLB (hP c) φ₂) _)).1 ?_⟩
  · have h := (cls_eq_iff (hP c) (pull_isLB (hP c) _)).2 (X.symm c)
    rw [cls_pull (hP c)] at h
    rw [cls_pull (pull_isLB (hP c) φ₂), cls_pull (hP c), ← GlobalTheory.CechPic.pull_comp, swap_comp hs,
      GlobalTheory.CechPic.pull_comp, ← h]
  · have h := (cls_eq_iff (hP c') (LB.isLB_div (hP _) (hP c))).2 (X.add c c')
    rw [cls_div (pull_isLB (hP _) φ₂) (pull_isLB (hP c) φ₂), cls_pull (hP c'), cls_pull (hP _), cls_pull (hP c), h,
      cls_div (hP _) (hP c), map_sub]
  · have h := (cls_eq_iff (hP _) (pull_isLB (hP c) _)).2 (X.smul a c)
    rw [cls_pull (hP c)] at h
    rw [cls_pull (pull_isLB (hP c) φ₂), cls_pull (hP c), ← GlobalTheory.CechPic.pull_comp, act_comp hs _ _ (hact a),
      GlobalTheory.CechPic.pull_comp, ← h, cls_pull (hP _)]

end GlobalTheory.RealMult.PullPol
