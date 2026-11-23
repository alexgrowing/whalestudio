import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobPullHomExtAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOnAff

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.DeRham GlobalTheory.DeRhamSheaf GlobalTheory.AbDual GlobalTheory.Cris GlobalTheory.AbDatum GlobalTheory.CechPic
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbDatum.Adjoint

theorem evc_swap_adj {S : Scheme.{0}} {A : Over S} {P : LB (A ⊗ A).left} (hP : P.IsLB) (hs : LBIso (swap P) P)
    {f g : A ⟶ A} (h : LBIso (ev P (fst A A ≫ f) (snd A A)) (ev P (fst A A) (snd A A ≫ g))) {Y : Over S}
    (y z : Y ⟶ A) : evc hP y (z ≫ f) = evc hP (y ≫ g) z := by
  have hs' : (swap P).IsLB := pull_isLB hP _
  have sym (a b : Y ⟶ A) : evc hP a b = evc hP b a := by
    rw [← evc_swap hP hs' a b, evc, evc, (cls_eq_iff hs' hP).2 hs]
  have e := congrArg (CechPic.pull (lift z y).left) ((cls_eq_iff (pull_isLB hP _) (pull_isLB hP _)).2 h)
  rw [cls_ev hP, cls_ev hP, pull_evc, pull_evc, lift_fst_assoc, lift_snd, lift_fst, lift_snd_assoc] at e
  rw [sym, e, sym]

theorem adj_pull {S S' : Scheme.{0}} {A : Over S} (b : S' ⟶ S) {P : LB (A ⊗ A).left} (hP : P.IsLB)
    {f g : A ⟶ A} (h : ∀ (Y : Over S) (y z : Y ⟶ A), evc hP y (z ≫ f) = evc hP (y ≫ g) z)
    {m : ((Over.pullback b).obj A ⊗ (Over.pullback b).obj A).left ⟶ (A ⊗ A).left}
    (m₁ : m ≫ (fst A A).left = (fst _ _ : _ ⟶ (Over.pullback b).obj A).left ≫ pullback.fst A.hom b)
    (m₂ : m ≫ (snd A A).left = (snd _ _ : _ ⟶ (Over.pullback b).obj A).left ≫ pullback.fst A.hom b) :
    LBIso (ev (P.pull m) (fst _ _) (snd ((Over.pullback b).obj A) _ ≫ (Over.pullback b).map f))
      (ev (P.pull m) (fst _ ((Over.pullback b).obj A) ≫ (Over.pullback b).map g) (snd _ _)) := by
  have hP' : (P.pull m).IsLB := pull_isLB hP _
  refine (cls_eq_iff (pull_isLB hP' _) (pull_isLB hP' _)).1 ?_
  let Y : Over S := Over.mk (m ≫ (A ⊗ A).hom)
  let y : Y ⟶ A := Over.homMk (m ≫ (fst A A).left) (by rw [Category.assoc, Over.w]; rfl)
  let z : Y ⟶ A := Over.homMk (m ≫ (snd A A).left) (by rw [Category.assoc, Over.w]; rfl)
  have k (u : A ⟶ A) : ((Over.pullback b).map u).left ≫ pullback.fst A.hom b = pullback.fst A.hom b ≫ u.left :=
    pullback.lift_fst _ _ _
  have e := h Y y z
  rw [cls_ev hP', cls_ev hP', evc, evc, cls_pull hP, ← pull_comp, ← pull_comp]
  rw [evc, evc] at e
  refine Eq.trans ?_ (e.trans ?_)
  · congr 2
    apply left_ext
    · rw [Category.assoc, m₁, lift_left_fst_assoc, lift_left_fst, ← m₁]
      rfl
    · rw [Category.assoc, m₂, lift_left_snd_assoc, lift_left_snd, Over.comp_left, Category.assoc, k,
        ← Category.assoc, ← m₂]
      rfl
  · congr 2
    apply left_ext
    · rw [Category.assoc, m₁, lift_left_fst_assoc, lift_left_fst, Over.comp_left, Over.comp_left,
        Category.assoc, k, ← Category.assoc, ← m₁]
      rfl
    · rw [Category.assoc, m₂, lift_left_snd_assoc, lift_left_snd, ← m₂]
      rfl

theorem main : GlobalTheory.CovTop.Hypotheses2 → ∀ (O : Type) [CommRing O] (c : O →+* O) (T : Scheme.{0}) (A : Over T) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (i : OAct O A) (P : LB (A ⊗ A).left), IsSelfDual c i P →
    ∀ (H : T.Modules)
    (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV))
    (ρ : O →+* End H) (β : H ⟶ dual H), IsDRAct e i ρ → IsPolPairing e P β →
    ∀ x : O, VB.act ρ x ≫ β = β ≫ dualMap (VB.act ρ (c x)) := by
  intro hP O _ c T A _ g hA hg i P hS H e ρ β hρ hβ x
  refine hom_dual_ext_affine fun V hV s t ↦ ?_
  obtain ⟨m, φ, m₁, m₂, hφ, pφ, k⟩ := hβ V hV
  have hL := hS.1.isLB
  have hAV := DeRhamSheaf.VB.isAbelianScheme_onAff A hA hV
  have hgV := DeRhamSheaf.VB.smooth_onAff A hg hV
  haveI := i.hom x
  haveI := i.hom (c x)
  let X (s : Γ(H, V)) : HdR (onAff A hV) := dualApp (β.app V s) le_rfl ∘ₗ (e V hV).symm.toLinearMap
  have hX (s t : Γ(H, V)) : X s (e V hV t) = dualApp (β.app V s) le_rfl t :=
    congrArg (dualApp (β.app V s) le_rfl) ((e V hV).symm_apply_apply t)
  have adj := hφ.adjoint (cupSquare_of_free hP.p5.1 (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hAV hAV) (smooth_prod hgV hgV))
    (pull_isLB hL m) (pull_isLB hL m) hφ ((Over.pullback hV.fromSpec).map (i.act (c x)))
    ((Over.pullback hV.fromSpec).map (i.act x))
    (adj_pull hV.fromSpec hL (fun _ y z ↦ evc_swap_adj hL hS.2.1 (hS.2.2 x) y z) m₁ m₂) (X s)
  have key := pφ.bijective_left.1 (LinearMap.ext fun y ↦
    ((k _ (X ((VB.act ρ x).app V s)) y (hX _)).trans (congrArg y (hρ x V hV s))).trans
      ((k s (X s) _ (hX s)).symm.trans (adj y)))
  refine (hX _ t).symm.trans ((LinearMap.congr_fun key (e V hV t)).trans ?_)
  refine Eq.trans ?_ (dualApp_dualMap (VB.act ρ (c x)) (β.app V s) le_rfl t).symm
  rw [← hX, hρ]
  rfl

end GlobalTheory.AbDatum.Adjoint
