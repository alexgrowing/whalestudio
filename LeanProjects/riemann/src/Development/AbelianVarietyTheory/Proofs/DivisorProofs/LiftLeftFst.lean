import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbDual

variable {S S' : Scheme.{0}} {b : S' ⟶ S}

theorem left_ext {P Q : Over S} {X : Scheme.{0}} {u v : X ⟶ (P ⊗ Q).left}
    (h₁ : u ≫ (fst P Q).left = v ≫ (fst P Q).left) (h₂ : u ≫ (snd P Q).left = v ≫ (snd P Q).left) : u = v := by
  have w : v ≫ (P ⊗ Q).hom = u ≫ (P ⊗ Q).hom := by
    rw [← Over.w (fst P Q), ← Category.assoc, ← Category.assoc, h₁]
  have e := CartesianMonoidalCategory.hom_ext (Over.homMk u rfl : Over.mk (u ≫ (P ⊗ Q).hom) ⟶ P ⊗ Q)
    (Over.homMk v w) (Over.OverMorphism.ext h₁) (Over.OverMorphism.ext h₂)
  exact congrArg (fun z ↦ z.left) e

section Pt

variable {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] {φ : G'.left ⟶ G.left}

theorem pt_ext (hφ : IsGrpPullback G' G b φ) {Y : Over S'} {x y : Y ⟶ G'} (e : x.left ≫ φ = y.left ≫ φ) :
    x = y :=
  Over.OverMorphism.ext (hφ.1.hom_ext e (by rw [Over.w x, Over.w y]))

def liftPt (hφ : IsGrpPullback G' G b φ) {X : Scheme.{0}} (s : X ⟶ S') (x : X ⟶ G.left)
    (w : x ≫ G.hom = s ≫ b) : Over.mk s ⟶ G' :=
  Over.homMk (hφ.1.lift x s w) (hφ.1.lift_snd _ _ _)

theorem liftPt_left (hφ : IsGrpPullback G' G b φ) {X : Scheme.{0}} (s : X ⟶ S') (x : X ⟶ G.left)
    (w : x ≫ G.hom = s ≫ b) : (liftPt hφ s x w).left ≫ φ = x :=
  hφ.1.lift_fst _ _ _

theorem mul_left_comp (hφ : IsGrpPullback G' G b φ) {X : Scheme.{0}} {s : X ⟶ S'} {s₀ : X ⟶ S}
    (hs : s ≫ b = s₀) {x y : Over.mk s ⟶ G'} {x₀ y₀ : Over.mk s₀ ⟶ G} (hx : x.left ≫ φ = x₀.left)
    (hy : y.left ≫ φ = y₀.left) : (x * y).left ≫ φ = (x₀ * y₀).left := by
  subst hs
  exact (hφ.2 _ x y x₀ y₀ hx.symm hy.symm).symm

theorem one_left_comp (hφ : IsGrpPullback G' G b φ) {X : Scheme.{0}} {s : X ⟶ S'} {s₀ : X ⟶ S}
    (hs : s ≫ b = s₀) : (1 : Over.mk s ⟶ G').left ≫ φ = (1 : Over.mk s₀ ⟶ G).left := by
  let x₀ : Over.mk s₀ ⟶ G := Over.homMk ((1 : Over.mk s ⟶ G').left ≫ φ) (by
    show _ ≫ G.hom = s₀
    rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w (1 : Over.mk s ⟶ G')]
    exact hs)
  have e : x₀ = x₀ * x₀ := Over.OverMorphism.ext (by
    have := mul_left_comp hφ hs (x := 1) (y := 1) (x₀ := x₀) (y₀ := x₀) rfl rfl
    rw [_root_.mul_one] at this
    exact this)
  exact congrArg (fun z ↦ z.left) (left_eq_mul.1 e)

end Pt

section Pt

variable {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] {φ : G'.left ⟶ G.left}

def pushP (hφ : IsGrpPullback G' G b φ) {X : Scheme.{0}} {s : X ⟶ S'} {s₀ : X ⟶ S} (hs : s ≫ b = s₀)
    (x : Over.mk s ⟶ G') : Over.mk s₀ ⟶ G :=
  Over.homMk (x.left ≫ φ) (by
    show _ ≫ G.hom = s₀
    rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w x]
    exact hs)

@[reassoc]
theorem lift_left_fst {P Q Y : Over S} (a : Y ⟶ P) (t : Y ⟶ Q) : (lift a t).left ≫ (fst P Q).left = a.left := by
  rw [← Over.comp_left, lift_fst]

@[reassoc]
theorem lift_left_snd {P Q Y : Over S} (a : Y ⟶ P) (t : Y ⟶ Q) : (lift a t).left ≫ (snd P Q).left = t.left := by
  rw [← Over.comp_left, lift_snd]

theorem trR_w (T : Over S') :
    (fst G (Over.mk (T.hom ≫ b))).left ≫ G.hom = ((snd G (Over.mk (T.hom ≫ b))).left ≫ T.hom) ≫ b := by
  rw [Over.w (fst G _), ← Over.w (snd G (Over.mk (T.hom ≫ b))), Category.assoc]
  rfl

def trR (hφ : IsGrpPullback G' G b φ) (T : Over S') :
    Over.mk ((snd G (Over.mk (T.hom ≫ b))).left ≫ T.hom) ⟶ G' ⊗ T :=
  lift (liftPt hφ _ (fst G (Over.mk (T.hom ≫ b))).left (trR_w T))
    (Over.homMk (snd G (Over.mk (T.hom ≫ b))).left rfl)

@[reassoc]
theorem trR_fst (hφ : IsGrpPullback G' G b φ) (T : Over S') :
    (trR hφ T).left ≫ (fst G' T).left ≫ φ = (fst G (Over.mk (T.hom ≫ b))).left := by
  exact (congrArg (· ≫ φ) (lift_left_fst _ _)).trans (liftPt_left _ _ _ _)

@[reassoc]
theorem trR_snd (hφ : IsGrpPullback G' G b φ) (T : Over S') :
    (trR hφ T).left ≫ (snd G' T).left = (snd G (Over.mk (T.hom ≫ b))).left :=
  lift_left_snd _ _

theorem trL_w (T : Over S') :
    (snd (Over.mk (T.hom ≫ b)) G).left ≫ G.hom = ((fst (Over.mk (T.hom ≫ b)) G).left ≫ T.hom) ≫ b := by
  rw [Over.w (snd _ G), ← Over.w (fst (Over.mk (T.hom ≫ b)) G), Category.assoc]
  rfl

def trL (hφ : IsGrpPullback G' G b φ) (T : Over S') :
    Over.mk ((fst (Over.mk (T.hom ≫ b)) G).left ≫ T.hom) ⟶ T ⊗ G' :=
  lift (Over.homMk (fst (Over.mk (T.hom ≫ b)) G).left rfl)
    (liftPt hφ _ (snd (Over.mk (T.hom ≫ b)) G).left (trL_w T))

@[reassoc]
theorem trL_snd (hφ : IsGrpPullback G' G b φ) (T : Over S') :
    (trL hφ T).left ≫ (snd T G').left ≫ φ = (snd (Over.mk (T.hom ≫ b)) G).left := by
  exact (congrArg (· ≫ φ) (lift_left_snd _ _)).trans (liftPt_left _ _ _ _)

@[reassoc]
theorem trL_fst (hφ : IsGrpPullback G' G b φ) (T : Over S') :
    (trL hφ T).left ≫ (fst T G').left = (fst (Over.mk (T.hom ≫ b)) G).left :=
  lift_left_fst _ _

end Pt

section Main

variable {A B : Over S} [GrpObj A] [GrpObj B] {A' B' : Over S'} [GrpObj A'] [GrpObj B']
  {f : A'.left ⟶ A.left} {g : B'.left ⟶ B.left} {h : (A' ⊗ B').left ⟶ (A ⊗ B).left}

theorem lift_comp_eq (h₁ : h ≫ (fst A B).left = (fst A' B').left ≫ f)
    (h₂ : h ≫ (snd A B).left = (snd A' B').left ≫ g) {X : Scheme.{0}} {s : X ⟶ S'} {s₀ : X ⟶ S}
    (a : Over.mk s ⟶ A') (t : Over.mk s ⟶ B') (a₀ : Over.mk s₀ ⟶ A) (t₀ : Over.mk s₀ ⟶ B)
    (ha : a.left ≫ f = a₀.left) (ht : t.left ≫ g = t₀.left) : (lift a t).left ≫ h = (lift a₀ t₀).left := by
  apply left_ext
  · rw [Category.assoc, h₁, lift_left_fst_assoc, ha, lift_left_fst]
  · rw [Category.assoc, h₂, lift_left_snd_assoc, ht, lift_left_snd]

theorem evc_eq (h₁ : h ≫ (fst A B).left = (fst A' B').left ≫ f)
    (h₂ : h ≫ (snd A B).left = (snd A' B').left ≫ g) {P : LB (A ⊗ B).left} {P' : LB (A' ⊗ B').left}
    (hP : P.IsLB) (hP' : P'.IsLB) (e : LBIso (P.pull h) P') {X : Scheme.{0}} {s : X ⟶ S'} {s₀ : X ⟶ S}
    (a : Over.mk s ⟶ A') (t : Over.mk s ⟶ B') (a₀ : Over.mk s₀ ⟶ A) (t₀ : Over.mk s₀ ⟶ B)
    (ha : a.left ≫ f = a₀.left) (ht : t.left ≫ g = t₀.left) : evc hP' a t = evc hP a₀ t₀ := by
  rw [evc, evc, ← (cls_eq_iff (pull_isLB hP h) hP').2 e, cls_pull hP, ← pull_comp,
    lift_comp_eq h₁ h₂ a t a₀ t₀ ha ht]

theorem evc_trR (hf : IsGrpPullback A' A b f) (hg : IsGrpPullback B' B b g)
    (h₁ : h ≫ (fst A B).left = (fst A' B').left ≫ f) (h₂ : h ≫ (snd A B).left = (snd A' B').left ≫ g)
    {P : LB (A ⊗ B).left} {P' : LB (A' ⊗ B').left} (hP : P.IsLB) (hP' : P'.IsLB) (e : LBIso (P.pull h) P')
    (T : Over S') (y : T ⟶ B') :
    CechPic.pull (trR hf T).left (evc hP' (fst A' T) (snd A' T ≫ y)) =
      evc hP (fst A (Over.mk (T.hom ≫ b))) (snd A (Over.mk (T.hom ≫ b)) ≫ pushP hg (s := T.hom) rfl y) := by
  rw [pull_evc]
  refine evc_eq h₁ h₂ hP hP' e _ _ _ _ ?_ ?_
  · rw [Over.comp_left, Category.assoc]
    exact trR_fst hf T
  · simp only [Over.comp_left, Category.assoc, trR_snd_assoc]
    rfl

theorem evc_trL (hf : IsGrpPullback A' A b f) (hg : IsGrpPullback B' B b g)
    (h₁ : h ≫ (fst A B).left = (fst A' B').left ≫ f) (h₂ : h ≫ (snd A B).left = (snd A' B').left ≫ g)
    {P : LB (A ⊗ B).left} {P' : LB (A' ⊗ B').left} (hP : P.IsLB) (hP' : P'.IsLB) (e : LBIso (P.pull h) P')
    (T : Over S') (x : T ⟶ A') :
    CechPic.pull (trL hg T).left (evc hP' (fst T B' ≫ x) (snd T B')) =
      evc hP (fst (Over.mk (T.hom ≫ b)) B ≫ pushP hf (s := T.hom) rfl x) (snd (Over.mk (T.hom ≫ b)) B) := by
  rw [pull_evc]
  refine evc_eq h₁ h₂ hP hP' e _ _ _ _ ?_ ?_
  · simp only [Over.comp_left, Category.assoc, trL_fst_assoc]
    rfl
  · rw [Over.comp_left, Category.assoc]
    exact trL_snd hg T

theorem lift_trR (hf : IsGrpPullback A' A b f) (T : Over S') {Y : Over S} (a₀ : Y ⟶ A)
    (t₀ : Y ⟶ Over.mk (T.hom ≫ b)) :
    (lift a₀ t₀).left ≫ (trR hf T).left = (lift (liftPt hf (t₀.left ≫ T.hom) a₀.left
      (by rw [Over.w a₀, Category.assoc]; exact (Over.w t₀).symm))
      (Over.homMk t₀.left rfl : Over.mk (t₀.left ≫ T.hom) ⟶ T)).left := by
  apply left_ext
  · rw [lift_left_fst]
    apply hf.1.hom_ext
    · rw [Category.assoc, Category.assoc, trR_fst, lift_left_fst, liftPt_left]
    · rw [Category.assoc, Category.assoc, Over.w (fst A' T), ← Over.w (snd A' T), trR_snd_assoc,
        lift_left_snd_assoc]
      exact (Over.w (liftPt hf _ _ _)).symm
  · rw [Category.assoc, trR_snd, lift_left_snd, lift_left_snd]
    rfl

theorem trR_section (hf : IsGrpPullback A' A b f) (T : Over S') :
    (lift (pushP hf (s := (A' ⊗ T).hom) rfl (fst A' T))
      (Over.homMk (snd A' T).left (by show _ ≫ T.hom ≫ b = _ ≫ b; rw [← Category.assoc, Over.w (snd A' T)]) :
        Over.mk ((A' ⊗ T).hom ≫ b) ⟶ Over.mk (T.hom ≫ b))).left ≫ (trR hf T).left = 𝟙 _ := by
  rw [lift_trR]
  apply left_ext
  · rw [lift_left_fst]
    refine Eq.trans ?_ (Category.id_comp _).symm
    apply hf.1.hom_ext
    · rw [liftPt_left]
      rfl
    · exact ((Over.w _).trans (Over.w (snd A' T))).trans (Over.w (fst A' T)).symm
  · rw [lift_left_snd]
    exact (Category.id_comp _).symm

theorem IsDual.baseChange (hf : IsGrpPullback A' A b f) (hg : IsGrpPullback B' B b g)
    (h₁ : h ≫ (fst A B).left = (fst A' B').left ≫ f) (h₂ : h ≫ (snd A B).left = (snd A' B').left ≫ g)
    {P : LB (A ⊗ B).left} {P' : LB (A' ⊗ B').left} (hP' : P'.IsLB) (e : LBIso (P.pull h) P')
    (hd : IsDual A B P) : IsDual A' B' P' := by
  refine ⟨hP', (isAdditive_iff hP').2 fun Y a a' t ↦ ?_, (triv_ev_iff hP' _ _).2 ?_, fun T M hM hA ↦ ?_⟩
  · rw [evc_eq h₁ h₂ hd.isLB hP' e (a * a') t (pushP hf (s := Y.hom) rfl a * pushP hf (s := Y.hom) rfl a') (pushP hg (s := Y.hom) rfl t)
      (mul_left_comp hf rfl rfl rfl) rfl, evc_eq h₁ h₂ hd.isLB hP' e a t (pushP hf (s := Y.hom) rfl a) (pushP hg (s := Y.hom) rfl t) rfl rfl,
      evc_eq h₁ h₂ hd.isLB hP' e a' t (pushP hf (s := Y.hom) rfl a') (pushP hg (s := Y.hom) rfl t) rfl rfl]
    exact (isAdditive_iff hd.isLB).1 hd.additive _ _ _ _
  · rw [evc_eq h₁ h₂ hd.isLB hP' e (𝟙 A') 1 (pushP hf (s := A'.hom) rfl (𝟙 A')) (1 : Over.mk (A'.hom ≫ b) ⟶ B) rfl
      (one_left_comp hg rfl)]
    exact evc_one_right hd.isLB hd.zero _
  · let T₀ : Over S := Over.mk (T.hom ≫ b)
    let k := trR hf T
    have hM₀ : (M.pull k.left).IsLB := pull_isLB hM _
    have ev₀ : ∀ (Y : Over S) (a₀ : Y ⟶ A) (t₀ : Y ⟶ T₀), evc hM₀ a₀ t₀ = evc hM
        (liftPt hf (t₀.left ≫ T.hom) a₀.left (by rw [Over.w a₀, Category.assoc]; exact (Over.w t₀).symm))
        (Over.homMk t₀.left rfl : Over.mk (t₀.left ≫ T.hom) ⟶ T) := fun Y a₀ t₀ ↦ by
      rw [evc, evc, cls_pull hM, ← pull_comp, lift_trR]
    have hadd : IsAdditive (M.pull k.left) := (isAdditive_iff hM₀).2 fun Y a₀ a₀' t₀ ↦ by
      have hs : (t₀.left ≫ T.hom) ≫ b = Y.hom := by rw [Category.assoc]; exact Over.w t₀
      have w₁ : a₀.left ≫ A.hom = (t₀.left ≫ T.hom) ≫ b := by rw [Over.w a₀]; exact hs.symm
      have w₂ : a₀'.left ≫ A.hom = (t₀.left ≫ T.hom) ≫ b := by rw [Over.w a₀']; exact hs.symm
      have w₃ : (a₀ * a₀').left ≫ A.hom = (t₀.left ≫ T.hom) ≫ b := by rw [Over.w (a₀ * a₀')]; exact hs.symm
      have hmul : liftPt hf (t₀.left ≫ T.hom) (a₀ * a₀').left w₃ =
          liftPt hf _ a₀.left w₁ * liftPt hf _ a₀'.left w₂ :=
        pt_ext hf (by
          rw [liftPt_left]
          exact (mul_left_comp hf hs (x₀ := a₀) (y₀ := a₀') (liftPt_left _ _ _ _) (liftPt_left _ _ _ _)).symm)
      rw [ev₀, ev₀, ev₀, hmul]
      exact (isAdditive_iff hM).1 hA _ _ _ _
    obtain ⟨x₀, hx₀, hu⟩ := hd.univ T₀ _ hM₀ hadd
    obtain ⟨j, hj⟩ : ∃ j : (A' ⊗ T).left ⟶ (A ⊗ T₀).left, j ≫ k.left = 𝟙 (A' ⊗ T).left :=
      ⟨_, trR_section hf T⟩
    have inj : ∀ c c' : Pic (A' ⊗ T).left, CechPic.pull k.left c = CechPic.pull k.left c' → c = c' :=
      fun c c' hc ↦ by
        have := congrArg (CechPic.pull j) hc
        rwa [← pull_comp, ← pull_comp, hj, pull_id, pull_id] at this
    have key : ∀ y : T ⟶ B', LBIso M (ev P' (fst A' T) (snd A' T ≫ y)) ↔
        LBIso (X := (A ⊗ T₀).left) (M.pull k.left) (ev P (fst A (Over.mk (T.hom ≫ b))) (snd A (Over.mk (T.hom ≫ b)) ≫ pushP hg (s := T.hom) rfl y)) := fun y ↦ by
      have c₁ : LBIso M (ev P' (fst A' T) (snd A' T ≫ y)) ↔ cls M hM = evc hP' (fst A' T) (snd A' T ≫ y) :=
        (cls_eq_iff hM (pull_isLB hP' _)).symm
      have c₂ : LBIso (X := (A ⊗ T₀).left) (M.pull k.left) (ev P (fst A (Over.mk (T.hom ≫ b))) (snd A (Over.mk (T.hom ≫ b)) ≫ pushP hg (s := T.hom) rfl y)) ↔
          CechPic.pull k.left (cls M hM) = evc hd.isLB (fst A (Over.mk (T.hom ≫ b))) (snd A (Over.mk (T.hom ≫ b)) ≫ pushP hg (s := T.hom) rfl y) :=
        (cls_eq_iff hM₀ (pull_isLB hd.isLB _)).symm
      rw [c₁, c₂, ← evc_trR hf hg h₁ h₂ hd.isLB hP' e]
      exact ⟨congrArg _, inj _ _⟩
    refine ⟨liftPt hg T.hom x₀.left (Over.w x₀), (key _).2 ?_, fun y hy ↦ ?_⟩
    · have hx : pushP hg (s := T.hom) rfl (liftPt hg T.hom x₀.left (Over.w x₀)) = x₀ :=
        Over.OverMorphism.ext (liftPt_left _ _ _ _)
      rw [hx]
      exact hx₀
    · refine pt_ext hg ?_
      rw [liftPt_left]
      exact congrArg (fun z ↦ z.left) (hu _ ((key y).1 hy))

theorem IsPerfect.baseChange (hf : IsGrpPullback A' A b f) (hg : IsGrpPullback B' B b g)
    (h₁ : h ≫ (fst A B).left = (fst A' B').left ≫ f) (h₂ : h ≫ (snd A B).left = (snd A' B').left ≫ g)
    {P : LB (A ⊗ B).left} {P' : LB (A' ⊗ B').left} (hP' : P'.IsLB) (e : LBIso (P.pull h) P')
    (hd : IsPerfect A B P) : IsPerfect A' B' P' := by
  refine ⟨hP', (triv_ev_iff hP' _ _).2 ?_, (triv_ev_iff hP' _ _).2 ?_, fun T x hx ↦ ?_, fun T x hx ↦ ?_⟩
  · rw [evc_eq h₁ h₂ hd.isLB hP' e (1 : B' ⟶ A') (𝟙 B') (1 : Over.mk (B'.hom ≫ b) ⟶ A) (pushP hg (s := B'.hom) rfl (𝟙 B'))
      (one_left_comp hf rfl) rfl]
    exact evc_one_left hd.isLB hd.zero_left _
  · rw [evc_eq h₁ h₂ hd.isLB hP' e (𝟙 A') (1 : A' ⟶ B') (pushP hf (s := A'.hom) rfl (𝟙 A')) (1 : Over.mk (A'.hom ≫ b) ⟶ B) rfl
      (one_left_comp hg rfl)]
    exact evc_one_right hd.isLB hd.zero_right _
  · have h0 := hd.ker_left _ (pushP hf (s := T.hom) rfl x) ((triv_ev_iff hd.isLB _ _).2 (by
      rw [← evc_trL hf hg h₁ h₂ hd.isLB hP' e, (triv_ev_iff hP' _ _).1 hx, map_zero]))
    exact pt_ext hf ((congrArg (fun z ↦ z.left) h0).trans (one_left_comp hf (s := T.hom) rfl).symm)
  · have h0 := hd.ker_right _ (pushP hg (s := T.hom) rfl x) ((triv_ev_iff hd.isLB _ _).2 (by
      rw [← evc_trR hf hg h₁ h₂ hd.isLB hP' e, (triv_ev_iff hP' _ _).1 hx, map_zero]))
    exact pt_ext hg ((congrArg (fun z ↦ z.left) h0).trans (one_left_comp hg (s := T.hom) rfl).symm)

end Main

end GlobalTheory.AbDual
