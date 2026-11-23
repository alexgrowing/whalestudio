import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon.BaseChange

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} [GrpObj A] {A' : Over S'} [GrpObj A'] {φ : A'.left ⟶ A.left}

theorem ext' (hφ : IsGrpPullback A' A f φ) {X Z : Scheme.{0}} {s : X ⟶ S'} {u v : Z ⟶ (A' ⊗ Over.mk s).left}
    (h₁ : u ≫ (fst A' (Over.mk s)).left ≫ φ = v ≫ (fst A' (Over.mk s)).left ≫ φ)
    (h₂ : u ≫ (snd A' (Over.mk s)).left = v ≫ (snd A' (Over.mk s)).left) : u = v := by
  refine left_ext (hφ.1.hom_ext (by simpa only [Category.assoc] using h₁) ?_) h₂
  rw [Category.assoc, Category.assoc, Over.w (fst A' _), ← Over.w (snd A' (Over.mk s)), ← Category.assoc, h₂,
    Category.assoc]

theorem toBase_w {X : Scheme.{0}} {s : X ⟶ S'} {s₀ : X ⟶ S} (hs : s ≫ f = s₀) :
    (snd A' (Over.mk s)).left ≫ s₀ = (A' ⊗ Over.mk s).hom ≫ f := by
  rw [← hs, ← Category.assoc]
  exact congrArg (· ≫ f) (Over.w (snd A' (Over.mk s)))

def toBase (hφ : IsGrpPullback A' A f φ) {X : Scheme.{0}} {s : X ⟶ S'} {s₀ : X ⟶ S} (hs : s ≫ f = s₀) :
    (A' ⊗ Over.mk s).left ⟶ (A ⊗ Over.mk s₀).left :=
  (lift (pushP hφ (s := (A' ⊗ Over.mk s).hom) rfl (fst A' (Over.mk s)))
    (Over.homMk (snd A' (Over.mk s)).left (toBase_w hs) : Over.mk ((A' ⊗ Over.mk s).hom ≫ f) ⟶ Over.mk s₀)).left

@[reassoc]
theorem toBase_fst (hφ : IsGrpPullback A' A f φ) {X : Scheme.{0}} {s : X ⟶ S'} {s₀ : X ⟶ S} (hs : s ≫ f = s₀) :
    toBase hφ hs ≫ (fst A (Over.mk s₀)).left = (fst A' (Over.mk s)).left ≫ φ :=
  lift_left_fst _ _

@[reassoc]
theorem toBase_snd (hφ : IsGrpPullback A' A f φ) {X : Scheme.{0}} {s : X ⟶ S'} {s₀ : X ⟶ S} (hs : s ≫ f = s₀) :
    toBase hφ hs ≫ (snd A (Over.mk s₀)).left = (snd A' (Over.mk s)).left :=
  lift_left_snd _ _

theorem ofBase_w {X : Scheme.{0}} {s : X ⟶ S'} {s₀ : X ⟶ S} (hs : s ≫ f = s₀) :
    (fst A (Over.mk s₀)).left ≫ A.hom = ((snd A (Over.mk s₀)).left ≫ s) ≫ f := by
  rw [Over.w (fst A _), Category.assoc, hs]
  exact (Over.w (snd A (Over.mk s₀))).symm

def ofBase (hφ : IsGrpPullback A' A f φ) {X : Scheme.{0}} {s : X ⟶ S'} {s₀ : X ⟶ S} (hs : s ≫ f = s₀) :
    (A ⊗ Over.mk s₀).left ⟶ (A' ⊗ Over.mk s).left :=
  (lift (liftPt hφ _ (fst A (Over.mk s₀)).left (ofBase_w hs))
    (Over.homMk (snd A (Over.mk s₀)).left rfl : Over.mk ((snd A (Over.mk s₀)).left ≫ s) ⟶ Over.mk s)).left

@[reassoc]
theorem ofBase_fst (hφ : IsGrpPullback A' A f φ) {X : Scheme.{0}} {s : X ⟶ S'} {s₀ : X ⟶ S} (hs : s ≫ f = s₀) :
    ofBase hφ hs ≫ (fst A' (Over.mk s)).left ≫ φ = (fst A (Over.mk s₀)).left := by
  rw [← Category.assoc]
  exact (congrArg (· ≫ φ) (lift_left_fst _ _)).trans (liftPt_left _ _ _ _)

@[reassoc]
theorem ofBase_snd (hφ : IsGrpPullback A' A f φ) {X : Scheme.{0}} {s : X ⟶ S'} {s₀ : X ⟶ S} (hs : s ≫ f = s₀) :
    ofBase hφ hs ≫ (snd A' (Over.mk s)).left = (snd A (Over.mk s₀)).left :=
  lift_left_snd _ _

theorem ofBase_toBase (hφ : IsGrpPullback A' A f φ) {X : Scheme.{0}} {s : X ⟶ S'} {s₀ : X ⟶ S}
    (hs : s ≫ f = s₀) : ofBase hφ hs ≫ toBase hφ hs = 𝟙 _ := by
  apply left_ext
  · rw [Category.assoc, toBase_fst, ofBase_fst, Category.id_comp]
  · rw [Category.assoc, toBase_snd, ofBase_snd, Category.id_comp]

theorem toBase_ofBase (hφ : IsGrpPullback A' A f φ) {X : Scheme.{0}} {s : X ⟶ S'} {s₀ : X ⟶ S}
    (hs : s ≫ f = s₀) : toBase hφ hs ≫ ofBase hφ hs = 𝟙 _ := by
  apply ext' hφ
  · rw [Category.assoc, ofBase_fst, toBase_fst, Category.id_comp]
  · rw [Category.assoc, ofBase_snd, toBase_snd, Category.id_comp]

end GlobalTheory.DualCon.BaseChange

namespace GlobalTheory.DualCon.BaseChange

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} [GrpObj A] {A' : Over S'} [GrpObj A'] {φ : A'.left ⟶ A.left}

theorem lift_ofBase (hφ : IsGrpPullback A' A f φ) {X : Scheme.{0}} {s : X ⟶ S'} {s₀ : X ⟶ S} (hs : s ≫ f = s₀)
    {Y : Over S} (a₀ : Y ⟶ A) (t₀ : Y ⟶ Over.mk s₀) :
    (lift a₀ t₀).left ≫ ofBase hφ hs = (lift (liftPt hφ (t₀.left ≫ s) a₀.left
      (by rw [Over.w a₀, Category.assoc, hs]; exact (Over.w t₀).symm))
      (Over.homMk t₀.left rfl : Over.mk (t₀.left ≫ s) ⟶ Over.mk s)).left := by
  apply ext' hφ
  · rw [Category.assoc, ofBase_fst, lift_left_fst, lift_left_fst_assoc, liftPt_left]
  · rw [Category.assoc, ofBase_snd, lift_left_snd, lift_left_snd]
    rfl

theorem lift_toBase (hφ : IsGrpPullback A' A f φ) {X : Scheme.{0}} {s : X ⟶ S'} {s₀ : X ⟶ S} (hs : s ≫ f = s₀)
    {Y : Over S'} (a : Y ⟶ A') (t : Y ⟶ Over.mk s) :
    (lift a t).left ≫ toBase hφ hs = (lift (pushP hφ (s := Y.hom) rfl a)
      (Over.homMk t.left (by show t.left ≫ s₀ = Y.hom ≫ f; rw [← hs, ← Category.assoc]; exact congrArg (· ≫ f) (Over.w t)) :
        Over.mk (Y.hom ≫ f) ⟶ Over.mk s₀)).left := by
  apply left_ext
  · rw [Category.assoc, toBase_fst, lift_left_fst_assoc, lift_left_fst]
    rfl
  · rw [Category.assoc, toBase_snd, lift_left_snd, lift_left_snd]
    rfl

theorem fam_ofBase (hφ : IsGrpPullback A' A f φ) {X : Scheme.{0}} {s : X ⟶ S'} {s₀ : X ⟶ S} (hs : s ≫ f = s₀)
    {M : LB (A' ⊗ Over.mk s).left} (hM : Fam A' M) : Fam A (M.pull (ofBase hφ hs)) := by
  have hM₀ : (M.pull (ofBase hφ hs)).IsLB := pull_isLB hM.isLB _
  refine ⟨hM₀, (isAdditive_iff hM₀).2 fun Y a₀ a₀' t₀ ↦ ?_⟩
  have ev₀ : ∀ (a : Y ⟶ A), evc hM₀ a t₀ = evc hM.isLB
      (liftPt hφ (t₀.left ≫ s) a.left (by rw [Over.w a, Category.assoc, hs]; exact (Over.w t₀).symm))
      (Over.homMk t₀.left rfl : Over.mk (t₀.left ≫ s) ⟶ Over.mk s) := fun a ↦ by
    rw [evc, evc, cls_pull hM.isLB, ← pull_comp, lift_ofBase]
  have hs' : (t₀.left ≫ s) ≫ f = Y.hom := by rw [Category.assoc, hs]; exact Over.w t₀
  have hmul : liftPt hφ (t₀.left ≫ s) (a₀ * a₀').left
      (by rw [Over.w (a₀ * a₀'), Category.assoc, hs]; exact (Over.w t₀).symm) =
      liftPt hφ _ a₀.left (by rw [Over.w a₀, Category.assoc, hs]; exact (Over.w t₀).symm) *
        liftPt hφ _ a₀'.left (by rw [Over.w a₀', Category.assoc, hs]; exact (Over.w t₀).symm) :=
    pt_ext hφ (by
      rw [liftPt_left]
      exact (mul_left_comp hφ hs' (x₀ := a₀) (y₀ := a₀') (liftPt_left _ _ _ _) (liftPt_left _ _ _ _)).symm)
  rw [ev₀, ev₀, ev₀, hmul]
  exact (isAdditive_iff hM.isLB).1 hM.add _ _ _ _

theorem fam_toBase (hφ : IsGrpPullback A' A f φ) {X : Scheme.{0}} {s : X ⟶ S'} {s₀ : X ⟶ S} (hs : s ≫ f = s₀)
    {N : LB (A ⊗ Over.mk s₀).left} (hN : Fam A N) : Fam A' (N.pull (toBase hφ hs)) := by
  have hN' : (N.pull (toBase hφ hs)).IsLB := pull_isLB hN.isLB _
  refine ⟨hN', (isAdditive_iff hN').2 fun Y a a' t ↦ ?_⟩
  have ev₀ : ∀ (c : Y ⟶ A'), evc hN' c t = evc hN.isLB (pushP hφ (s := Y.hom) rfl c)
      (Over.homMk t.left (by show t.left ≫ s₀ = Y.hom ≫ f; rw [← hs, ← Category.assoc]; exact congrArg (· ≫ f) (Over.w t)) : Over.mk (Y.hom ≫ f) ⟶ Over.mk s₀) :=
    fun c ↦ by rw [evc, evc, cls_pull hN.isLB, ← pull_comp, lift_toBase]
  have hmul : pushP hφ (s := Y.hom) rfl (a * a') = pushP hφ (s := Y.hom) rfl a * pushP hφ (s := Y.hom) rfl a' :=
    Over.OverMorphism.ext (mul_left_comp hφ rfl rfl rfl)
  rw [ev₀, ev₀, ev₀, hmul]
  exact (isAdditive_iff hN.isLB).1 hN.add _ _ _ _

theorem pull_inj_iff {X Y : Scheme.{0}} (u : Y ⟶ X) (v : X ⟶ Y) (h : v ≫ u = 𝟙 X) (c d : Pic X) :
    c = d ↔ CechPic.pull u c = CechPic.pull u d :=
  ⟨congrArg _, fun e ↦ by
    have k := congrArg (CechPic.pull v) e
    rwa [← pull_comp, ← pull_comp, h, pull_id, pull_id] at k⟩

theorem toBase_lift_ofBase (hφ : IsGrpPullback A' A f φ) {X Z : Scheme.{0}} {s : X ⟶ S'} {s₀ : X ⟶ S}
    (hs : s ≫ f = s₀) {sZ : Z ⟶ S'} {sZ₀ : Z ⟶ S} (hsZ : sZ ≫ f = sZ₀) (x : Over.mk s₀ ⟶ Over.mk sZ₀)
    (x' : Over.mk s ⟶ Over.mk sZ) (hx : x.left = x'.left) :
    toBase hφ hs ≫ (lift (fst A (Over.mk s₀)) (snd A (Over.mk s₀) ≫ x)).left ≫ ofBase hφ hsZ =
      (lift (fst A' (Over.mk s)) (snd A' (Over.mk s) ≫ x')).left := by
  apply ext' hφ
  · rw [Category.assoc, Category.assoc, ofBase_fst, lift_left_fst, toBase_fst, lift_left_fst_assoc]
  · rw [Category.assoc, Category.assoc, ofBase_snd, lift_left_snd, Over.comp_left, toBase_snd_assoc,
      lift_left_snd, Over.comp_left, hx]

theorem ofBase_lift_toBase (hφ : IsGrpPullback A' A f φ) {X Z : Scheme.{0}} {s : X ⟶ S'} {s₀ : X ⟶ S}
    (hs : s ≫ f = s₀) {sZ : Z ⟶ S'} {sZ₀ : Z ⟶ S} (hsZ : sZ ≫ f = sZ₀) (x : Over.mk s₀ ⟶ Over.mk sZ₀)
    (x' : Over.mk s ⟶ Over.mk sZ) (hx : x.left = x'.left) :
    ofBase hφ hs ≫ (lift (fst A' (Over.mk s)) (snd A' (Over.mk s) ≫ x')).left ≫ toBase hφ hsZ =
      (lift (fst A (Over.mk s₀)) (snd A (Over.mk s₀) ≫ x)).left := by
  apply left_ext
  · rw [Category.assoc, Category.assoc, toBase_fst, lift_left_fst_assoc, ofBase_fst, lift_left_fst]
  · rw [Category.assoc, Category.assoc, toBase_snd, lift_left_snd, Over.comp_left, ofBase_snd_assoc,
      lift_left_snd, Over.comp_left, hx]

end GlobalTheory.DualCon.BaseChange

namespace GlobalTheory.DualCon.BaseChange

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} [GrpObj A] {A' : Over S'} [GrpObj A'] {φ : A'.left ⟶ A.left}

theorem rep_down (hφ : IsGrpPullback A' A f φ) {T B' : Over S'} (b' : B' ⟶ T) {P' : LB (A' ⊗ B').left}
    (h : Rep A' b' P') :
    Rep A (Over.homMk b'.left (by show b'.left ≫ T.hom ≫ f = B'.hom ≫ f; rw [← Category.assoc, Over.w b']) :
      Over.mk (B'.hom ≫ f) ⟶ Over.mk (T.hom ≫ f)) (P'.pull (ofBase hφ (s := B'.hom) rfl)) where
  fam := fam_ofBase hφ rfl h.fam
  univ T₁ t N hN := by
    have hs : (t.left ≫ T.hom) ≫ f = T₁.hom := by rw [Category.assoc]; exact Over.w t
    obtain ⟨x', ⟨hxb, hxN⟩, hu⟩ := h.univ (Over.mk (t.left ≫ T.hom)) (Over.homMk t.left rfl)
      (N.pull (toBase hφ hs)) (fam_toBase hφ hs hN)
    have key : ∀ (x : T₁ ⟶ Over.mk (B'.hom ≫ f)) (x' : Over.mk (t.left ≫ T.hom) ⟶ B'), x.left = x'.left →
        (LBIso N (ev (P'.pull (ofBase hφ (s := B'.hom) rfl)) (fst A T₁) (snd A T₁ ≫ x)) ↔
          LBIso (N.pull (toBase hφ hs)) (ev P' (fst A' _) (snd A' _ ≫ x'))) := fun x x' hx ↦ by
      have hQ := pull_isLB (pull_isLB h.fam.isLB (ofBase hφ (s := B'.hom) rfl))
        (lift (fst A T₁) (snd A T₁ ≫ x)).left
      rw [← cls_eq_iff hN.isLB hQ, ← cls_eq_iff (pull_isLB hN.isLB _) (pull_isLB h.fam.isLB _)]
      refine (pull_inj_iff _ _ (ofBase_toBase hφ hs) _ _).trans (Eq.congr_right ?_)
      show CechPic.pull (toBase hφ hs) (CechPic.pull (lift (fst A T₁) (snd A T₁ ≫ x)).left
        (CechPic.pull (ofBase hφ (s := B'.hom) rfl) (cls P' h.fam.isLB))) = _
      rw [← pull_comp, ← pull_comp, Category.assoc]
      exact congrArg (fun m ↦ CechPic.pull m (cls P' h.fam.isLB)) (toBase_lift_ofBase hφ hs rfl x x' hx)
    have hxl : x'.left ≫ b'.left = t.left := congrArg (fun z ↦ z.left) hxb
    refine ⟨Over.homMk x'.left (by show x'.left ≫ B'.hom ≫ f = T₁.hom; rw [← Category.assoc, Over.w x']; exact hs),
      ⟨Over.OverMorphism.ext hxl, (key _ x' rfl).2 hxN⟩, fun y ⟨hyb, hyN⟩ ↦ ?_⟩
    have hyl : y.left ≫ b'.left = t.left := congrArg (fun z ↦ z.left) hyb
    let y' : Over.mk (t.left ≫ T.hom) ⟶ B' := Over.homMk y.left
      (by
        show y.left ≫ B'.hom = t.left ≫ T.hom
        rw [← hyl, Category.assoc]
        exact congrArg (y.left ≫ ·) (Over.w b').symm)
    have e := hu y' ⟨Over.OverMorphism.ext hyl, (key y y' rfl).1 hyN⟩
    exact Over.OverMorphism.ext (congrArg (fun z ↦ z.left) e)

theorem rep_up (hφ : IsGrpPullback A' A f φ) {T : Over S'} {B : Over S} (b : B ⟶ Over.mk (T.hom ≫ f))
    {P : LB (A ⊗ B).left} (h : Rep A b P) :
    Rep A' (Over.homMk b.left rfl : Over.mk (b.left ≫ T.hom) ⟶ T)
      (P.pull (toBase hφ (s := b.left ≫ T.hom) (s₀ := B.hom) (by rw [Category.assoc]; exact Over.w b))) where
  fam := fam_toBase hφ _ h.fam
  univ T₁ t' N' hN' := by
    have hsB : (b.left ≫ T.hom) ≫ f = B.hom := by rw [Category.assoc]; exact Over.w b
    let t : Over.mk (T₁.hom ≫ f) ⟶ Over.mk (T.hom ≫ f) := Over.homMk t'.left
      (by show t'.left ≫ T.hom ≫ f = T₁.hom ≫ f; rw [← Category.assoc, Over.w t'])
    obtain ⟨x, ⟨hxb, hxN⟩, hu⟩ := h.univ (Over.mk (T₁.hom ≫ f)) t (N'.pull (ofBase hφ (s := T₁.hom) rfl))
      (fam_ofBase hφ rfl hN')
    have key : ∀ (x : Over.mk (T₁.hom ≫ f) ⟶ B) (x' : T₁ ⟶ Over.mk (b.left ≫ T.hom)), x.left = x'.left →
        (LBIso N' (ev (P.pull (toBase hφ hsB)) (fst A' T₁) (snd A' T₁ ≫ x')) ↔
          LBIso (N'.pull (ofBase hφ (s := T₁.hom) rfl)) (ev P (fst A _) (snd A _ ≫ x))) := fun x x' hx ↦ by
      have hQ := pull_isLB (pull_isLB h.fam.isLB (toBase hφ hsB)) (lift (fst A' T₁) (snd A' T₁ ≫ x')).left
      rw [← cls_eq_iff hN'.isLB hQ, ← cls_eq_iff (pull_isLB hN'.isLB _) (pull_isLB h.fam.isLB _)]
      refine (pull_inj_iff _ _ (toBase_ofBase hφ (s := T₁.hom) rfl) _ _).trans (Eq.congr_right ?_)
      show CechPic.pull (ofBase hφ (s := T₁.hom) rfl) (CechPic.pull (lift (fst A' T₁) (snd A' T₁ ≫ x')).left
        (CechPic.pull (toBase hφ hsB) (cls P h.fam.isLB))) = _
      rw [← pull_comp, ← pull_comp, Category.assoc]
      exact congrArg (fun m ↦ CechPic.pull m (cls P h.fam.isLB)) (ofBase_lift_toBase hφ rfl hsB x x' hx)
    have hxl : x.left ≫ b.left = t'.left := congrArg (fun z ↦ z.left) hxb
    refine ⟨Over.homMk x.left (by show x.left ≫ b.left ≫ T.hom = T₁.hom; rw [← Category.assoc, hxl, Over.w t']),
      ⟨Over.OverMorphism.ext hxl, (key x _ rfl).2 hxN⟩, fun y' ⟨hyb, hyN⟩ ↦ ?_⟩
    have hyl : y'.left ≫ b.left = t'.left := congrArg (fun z ↦ z.left) hyb
    let y : Over.mk (T₁.hom ≫ f) ⟶ B := Over.homMk y'.left (by
      show y'.left ≫ B.hom = T₁.hom ≫ f
      rw [← hsB, ← Category.assoc, ← Category.assoc, hyl, Over.w t'])
    have e := hu y ⟨Over.OverMorphism.ext hyl, (key y y' rfl).1 hyN⟩
    exact Over.OverMorphism.ext (congrArg (fun z ↦ z.left) e)

end GlobalTheory.DualCon.BaseChange

namespace GlobalTheory.DualCon

theorem hasRep_baseChange_iff : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (A : Over S) [GrpObj A] (A' : Over S') [GrpObj A']
    (φ : A'.left ⟶ A.left), IsGrpPullback A' A f φ → ∀ (g : ℕ) (T : Over S'),
    (HasRep A' g T ↔ HasRep A g (Over.mk (T.hom ≫ f))) ∧
      (HasRepAF A' g T ↔ HasRepAF A g (Over.mk (T.hom ≫ f))) := by
  intro S S' f A _ A' _ φ hφ g T
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro ⟨B', b', P', hR, hG⟩
    exact ⟨_, _, _, BaseChange.rep_down hφ b' hR, hG⟩
  · rintro ⟨B, b, P, hR, hG⟩
    exact ⟨_, _, _, BaseChange.rep_up hφ b hR, hG⟩
  · rintro ⟨B', b', P', hR, hG, hF⟩
    exact ⟨_, _, _, BaseChange.rep_down hφ b' hR, hG, hF⟩
  · rintro ⟨B, b, P, hR, hG, hF⟩
    exact ⟨_, _, _, BaseChange.rep_up hφ b hR, hG, hF⟩

end GlobalTheory.DualCon
