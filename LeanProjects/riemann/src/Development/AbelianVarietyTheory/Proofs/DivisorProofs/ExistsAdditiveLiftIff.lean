import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxes
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Cris GlobalTheory.DeRham
  GlobalTheory.Published

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BirigidLift

section General

variable {S : Scheme.{0}} {A B D : Over S} [GrpObj A] [GrpObj B] [GrpObj D]

omit [GrpObj A] in

theorem isAdditive_swap_iff {P : LB (A ⊗ B).left} (hP : P.IsLB) : IsAdditive (swap P) ↔
    ∀ (Y : Over S) (a : Y ⟶ A) (b b' : Y ⟶ B), evc hP a (b * b') = evc hP a b + evc hP a b' := by
  have hs : (swap P).IsLB := pull_isLB hP _
  rw [isAdditive_iff hs]
  simp only [evc_swap hP hs]
  exact ⟨fun h Y a b b' ↦ h Y b b' a, fun h Y b b' a ↦ h Y a b b'⟩

omit [GrpObj B] in

theorem triv_left {P : LB (A ⊗ B).left} (hP : P.IsLB) (h : IsAdditive P) : Triv (ev P (1 : B ⟶ A) (𝟙 B)) :=
  (triv_ev_iff hP _ _).2 (h.evc_one hP _)

omit [GrpObj A] in

theorem triv_right {P : LB (A ⊗ B).left} (hP : P.IsLB) (h : IsAdditive (swap P)) :
    Triv (ev P (𝟙 A) (1 : A ⟶ B)) := by
  have hs : (swap P).IsLB := pull_isLB hP _
  rw [triv_ev_iff hP, ← evc_swap hP hs]
  exact h.evc_one hs _

theorem dual_ext {Q : LB (A ⊗ D).left} (h : IsDual A D Q) {T : Over S} {y y' : T ⟶ D}
    (e : evc h.isLB (fst A T) (snd A T ≫ y) = evc h.isLB (fst A T) (snd A T ≫ y')) : y = y' := by
  have hM : (ev Q (fst A T) (snd A T ≫ y)).IsLB := pull_isLB h.isLB _
  refine (h.univ T _ hM ((isAdditive_iff hM).2 fun Y a a' t ↦ ?_)).unique ((cls_eq_iff hM hM).1 rfl)
    ((cls_eq_iff hM (pull_isLB h.isLB _)).1 e)
  simp only [evc_ev h.isLB, lift_fst, lift_snd_assoc]
  exact (isAdditive_iff h.isLB).1 h.additive _ _ _ _

omit [GrpObj A] [GrpObj B] [GrpObj D] in

theorem evc_of_cls {Q : LB (A ⊗ D).left} (hQ : Q.IsLB) {P : LB (A ⊗ B).left} (hP : P.IsLB) {x : B ⟶ D}
    (e : cls P hP = evc hQ (fst A B) (snd A B ≫ x)) {Y : Over S} (a : Y ⟶ A) (b : Y ⟶ B) :
    evc hP a b = evc hQ a (b ≫ x) := by
  rw [evc, e, pull_evc, lift_fst, lift_snd_assoc]

theorem exists_hom {Q : LB (A ⊗ D).left} (h : IsDual A D Q) (h' : IsAdditive (swap Q)) {P : LB (A ⊗ B).left}
    (hP : P.IsLB) (a₁ : IsAdditive P) (a₂ : IsAdditive (swap P)) :
    ∃ x : B ⟶ D, IsMonHom x ∧ cls P hP = evc h.isLB (fst A B) (snd A B ≫ x) := by
  obtain ⟨x, hx, -⟩ := h.univ B P hP a₁
  have e : cls P hP = evc h.isLB (fst A B) (snd A B ≫ x) := (cls_eq_iff hP (pull_isLB h.isLB _)).2 hx
  have k : ∀ {T : Over S} (u v : T ⟶ B), (u * v) ≫ x = (u ≫ x) * (v ≫ x) := fun u v ↦ dual_ext h <| by
    rw [MonObj.comp_mul, (isAdditive_swap_iff h.isLB).1 h', ← Category.assoc, ← Category.assoc, ← Category.assoc,
      ← evc_of_cls h.isLB hP e, ← evc_of_cls h.isLB hP e, ← evc_of_cls h.isLB hP e, MonObj.comp_mul,
      (isAdditive_swap_iff hP).1 a₂]
  refine ⟨x, ⟨?_, ?_⟩, e⟩
  · have e₁ := k (1 : 𝟙_ (Over S) ⟶ B) 1
    rw [_root_.mul_one] at e₁
    have e₂ := left_eq_mul.1 e₁
    simpa [Hom.one_def] using e₂
  · have e₁ := k (fst B B) (snd B B)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at e₁
    rw [e₁]
    congr 1

theorem additive_ev {Q : LB (A ⊗ D).left} (hQ : Q.IsLB) (a₁ : IsAdditive Q) (a₂ : IsAdditive (swap Q)) (x : B ⟶ D)
    [IsMonHom x] : IsAdditive (ev Q (fst A B) (snd A B ≫ x)) ∧ IsAdditive (swap (ev Q (fst A B) (snd A B ≫ x))) := by
  have hP : (ev Q (fst A B) (snd A B ≫ x)).IsLB := pull_isLB hQ _
  refine ⟨(isAdditive_iff hP).2 fun Y a a' t ↦ ?_, (isAdditive_swap_iff hP).2 fun Y a b b' ↦ ?_⟩
  · simp only [evc_of_cls hQ hP rfl]
    exact (isAdditive_iff hQ).1 a₁ _ _ _ _
  · simp only [evc_of_cls hQ hP rfl, MonObj.mul_comp]
    exact (isAdditive_swap_iff hQ).1 a₂ _ _ _ _

theorem additive_pull {S' : Scheme.{0}} {b : S' ⟶ S} {A' B' : Over S'} [GrpObj A'] [GrpObj B']
    {f : A'.left ⟶ A.left} {g : B'.left ⟶ B.left} {l : (A' ⊗ B').left ⟶ (A ⊗ B).left}
    (hf : IsGrpPullback A' A b f) (hg : IsGrpPullback B' B b g)
    (l₁ : l ≫ (fst A B).left = (fst A' B').left ≫ f) (l₂ : l ≫ (snd A B).left = (snd A' B').left ≫ g)
    {P : LB (A ⊗ B).left} {P' : LB (A' ⊗ B').left} (hP : P.IsLB) (hP' : P'.IsLB) (e : LBIso (P.pull l) P')
    (a₁ : IsAdditive P) (a₂ : IsAdditive (swap P)) : IsAdditive P' ∧ IsAdditive (swap P') := by
  have k : ∀ (Y : Over S') (a : Y ⟶ A') (t : Y ⟶ B'),
      evc hP' a t = evc hP (pushP hf (s := Y.hom) rfl a) (pushP hg (s := Y.hom) rfl t) := fun Y a t ↦
    evc_eq l₁ l₂ hP hP' e a t _ _ rfl rfl
  refine ⟨(isAdditive_iff hP').2 fun Y a a' t ↦ ?_, (isAdditive_swap_iff hP').2 fun Y a t t' ↦ ?_⟩
  · rw [evc_eq l₁ l₂ hP hP' e (a * a') t (pushP hf (s := Y.hom) rfl a * pushP hf (s := Y.hom) rfl a')
      (pushP hg (s := Y.hom) rfl t) (mul_left_comp hf rfl rfl rfl) rfl, k, k]
    exact (isAdditive_iff hP).1 a₁ _ _ _ _
  · rw [evc_eq l₁ l₂ hP hP' e a (t * t') (pushP hf (s := Y.hom) rfl a)
      (pushP hg (s := Y.hom) rfl t * pushP hg (s := Y.hom) rfl t') rfl (mul_left_comp hg rfl rfl rfl), k, k]
    exact (isAdditive_swap_iff hP).1 a₂ _ _ _ _

omit [GrpObj A] [GrpObj B] [GrpObj D] in

theorem pull_evc_eq {S' : Scheme.{0}} {A' B' D' : Over S'} {f : A'.left ⟶ A.left} {g : B'.left ⟶ B.left}
    {d : D'.left ⟶ D.left} {l : (A' ⊗ B').left ⟶ (A ⊗ B).left} {m : (A' ⊗ D').left ⟶ (A ⊗ D).left}
    (l₁ : l ≫ (fst A B).left = (fst A' B').left ≫ f) (l₂ : l ≫ (snd A B).left = (snd A' B').left ≫ g)
    (m₁ : m ≫ (fst A D).left = (fst A' D').left ≫ f) (m₂ : m ≫ (snd A D).left = (snd A' D').left ≫ d)
    {Q : LB (A ⊗ D).left} (hQ : Q.IsLB) (hQ' : (Q.pull m).IsLB) {x : B ⟶ D} {x' : B' ⟶ D'}
    (e : g ≫ x.left = x'.left ≫ d) :
    CechPic.pull l (evc hQ (fst A B) (snd A B ≫ x)) = evc hQ' (fst A' B') (snd A' B' ≫ x') := by
  rw [evc, evc, cls_pull hQ, ← pull_comp, ← pull_comp]
  congr 2
  apply left_ext
  · rw [Category.assoc, Category.assoc, lift_left_fst, m₁, lift_left_fst_assoc, l₁]
  · rw [Category.assoc, Category.assoc, lift_left_snd, m₂, lift_left_snd_assoc, Over.comp_left, Over.comp_left,
      ← Category.assoc, l₂, Category.assoc, Category.assoc, e]

theorem additive_of_triv (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {H : LB (A ⊗ B).left} (hH : H.IsLB)
    (hamp : Out.RelAmple (A ⊗ B) H) {P : LB (A ⊗ B).left} (hP : P.IsLB) (h₁ : Triv (ev P (1 : B ⟶ A) (𝟙 B)))
    (h₂ : Triv (ev P (𝟙 A) (1 : A ⟶ B))) : IsAdditive P ∧ IsAdditive (swap P) := by
  have hG := AbelianSchemeGerms.isAbelianScheme_tensor A B hA hB
  have key : ∀ (F : (A ⊗ B) ⊗ (A ⊗ B) ⟶ A ⊗ B),
      CechPic.pull (lift (1 : A ⊗ B ⟶ A ⊗ B) (𝟙 _) ≫ F).left (cls P hP) = 0 →
      CechPic.pull (lift (𝟙 _) (1 : A ⊗ B ⟶ A ⊗ B) ≫ F).left (cls P hP) = 0 →
      ∀ (Y : Over S) (x x' y : Y ⟶ A ⊗ B), CechPic.pull (lift (x * x') y ≫ F).left (cls P hP) =
        CechPic.pull (lift x y ≫ F).left (cls P hP) + CechPic.pull (lift x' y ≫ F).left (cls P hP) := by
    intro F e₁ e₂ Y x x' y
    have t := Biadditive.triv_add F GlobalTheory.laws_without_cohomology.1 hG hH hamp hP
      ((cls_eq_zero_iff (pull_isLB hP _)).1 e₁) ((cls_eq_zero_iff (pull_isLB hP _)).1 e₂) x x' y
    have z := (cls_linComb hP _ _ (LB.isLB_linComb hP _ _)).symm.trans
      ((cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 t)
    rw [Fin.sum_univ_three] at z
    have z' : (1 : ℤ) • CechPic.pull (lift (x * x') y ≫ F).left (cls P hP) +
        (-1 : ℤ) • CechPic.pull (lift x y ≫ F).left (cls P hP) +
        (-1 : ℤ) • CechPic.pull (lift x' y ≫ F).left (cls P hP) = 0 := z
    rw [one_zsmul, neg_one_zsmul, neg_one_zsmul] at z'
    rw [← sub_eq_zero, ← z']
    abel
  refine ⟨(isAdditive_iff hP).2 fun Y a a' t ↦ ?_, (isAdditive_swap_iff hP).2 fun Y a t t' ↦ ?_⟩
  · have e := key (lift (fst _ _ ≫ fst A B) (snd _ _ ≫ snd A B)) ?_ ?_ Y (lift a 1) (lift a' 1) (lift 1 t)
    · simpa only [comp_lift, lift_fst_assoc, lift_snd_assoc, MonObj.mul_comp, lift_fst, lift_snd, evc] using e
    · rw [comp_lift, lift_fst_assoc, lift_snd_assoc, MonObj.one_comp]
      exact evc_one_left hP h₁ _
    · rw [comp_lift, lift_fst_assoc, lift_snd_assoc, MonObj.one_comp]
      exact evc_one_right hP h₂ _
  · have e := key (lift (snd _ _ ≫ fst A B) (fst _ _ ≫ snd A B)) ?_ ?_ Y (lift 1 t) (lift 1 t') (lift a 1)
    · simpa only [comp_lift, lift_fst_assoc, lift_snd_assoc, MonObj.mul_comp, lift_fst, lift_snd, evc] using e
    · rw [comp_lift, lift_fst_assoc, lift_snd_assoc, MonObj.one_comp]
      exact evc_one_right hP h₂ _
    · rw [comp_lift, lift_fst_assoc, lift_snd_assoc, MonObj.one_comp]
      exact evc_one_left hP h₁ _

theorem exists_relAmple_prod [IsAffine S] (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {L : LB A.left}
    (hL : L.IsLB) (aL : Out.RelAmple A L) {M : LB B.left} (hM : M.IsLB) (aM : Out.RelAmple B M) :
    ∃ H : LB (A ⊗ B).left, H.IsLB ∧ Out.RelAmple (A ⊗ B) H := by
  obtain ⟨H, hH, eH⟩ := cls_surj (CechPic.pull (fst A B).left (cls L hL) + CechPic.pull (snd A B).left (cls M hM))
  have hd := LB.isLB_div hH (pull_isLB hL (fst A B).left)
  have last : LBIso (M.pull (snd A B).left) (H.div (L.pull (fst A B).left)) := by
    refine (cls_eq_iff (pull_isLB hM _) hd).1 ?_
    rw [cls_div hH (pull_isLB hL (fst A B).left), eH, cls_pull hL, cls_pull hM, add_sub_cancel_left]
  haveI := hA.proper
  haveI := hB.proper
  haveI := (AbelianSchemeGerms.isAbelianScheme_tensor A B hA hB).proper
  exact ⟨H, hH, (relAmple_iff_isAmpleLB_of_isAffine _ hH).2 (IsAmpleLB.box
    ((relAmple_iff_isAmpleLB_of_isAffine _ hL).1 aL) ((relAmple_iff_isAmpleLB_of_isAffine _ hM).1 aM)
    hH (p := (fst A B).left) (q := (snd A B).left) (f := A.hom) (g := B.hom) (IsPullback.of_hasPullback _ _) last)⟩

end General

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {κ : DividedPowers I} {π : R →+* R₀}
  {A B : Over (Sp R)} [GrpObj A] [GrpObj B] {A₀ B₀ : Over (Sp R₀)} [GrpObj A₀] [GrpObj B₀]
  {i : A₀.left ⟶ A.left} {j : B₀.left ⟶ B.left} {l : (A₀ ⊗ B₀).left ⟶ (A ⊗ B).left} {g g' : ℕ}

theorem exists_dual_pair (HD : DualAbelianScheme) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    (h : IsGrpPullback A₀ A (spMap π) i) :
    ∃ (D : Over (Sp R)) (_ : GrpObj D) (Q : LB (A ⊗ D).left) (D₀ : Over (Sp R₀)) (_ : GrpObj D₀)
      (d : D₀.left ⟶ D.left) (m : (A₀ ⊗ D₀).left ⟶ (A ⊗ D).left), IsAbelianScheme D ∧
      SmoothOfRelativeDimension g D.hom ∧ IsDual A D Q ∧ IsDual D A (swap Q) ∧ IsGrpPullback D₀ D (spMap π) d ∧
      m ≫ (fst A D).left = (fst A₀ D₀).left ≫ i ∧ m ≫ (snd A D).left = (snd A₀ D₀).left ≫ d ∧
      IsDual A₀ D₀ (Q.pull m) ∧ IsAdditive (swap (Q.pull m)) := by
  obtain ⟨D, _, Q, hD, hd, q, q'⟩ := HD _ A hA
  have k := isGrpPullback_pullback D (spMap π)
  obtain ⟨m, m₁, m₂⟩ := exists_prod_pullback h k
  have hQ := pull_isLB q.isLB m
  have e : LBIso (Q.pull m) (Q.pull m) := (cls_eq_iff hQ hQ).1 rfl
  exact ⟨D, _, Q, _, _, _, m, hD, hd g hg, q, q', k, m₁, m₂, q.baseChange h k m₁ m₂ hQ e,
    (additive_pull h k m₁ m₂ q.isLB hQ e q.additive q'.additive).2⟩

theorem exists_lift_of_cupSquare (HG : GrothendieckMessing.At κ π) (HR : AbelianDeRham) (HD : DualAbelianScheme)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) (hB : IsAbelianScheme B)
    (hg' : SmoothOfRelativeDimension g' B.hom) (h : IsGrpPullback A₀ A (spMap π) i)
    (k : IsGrpPullback B₀ B (spMap π) j) (l₁ : l ≫ (fst A B).left = (fst A₀ B₀).left ≫ i)
    (l₂ : l ≫ (snd A B).left = (snd A₀ B₀).left ≫ j) (C : CupSquare κ (spMap π) (A₀ ⊗ B₀))
    {P₀ : LB (A₀ ⊗ B₀).left} (hP₀ : P₀.IsLB) (a₁ : IsAdditive P₀) (a₂ : IsAdditive (swap P₀))
    {φ₀ : Crys κ (spMap π) A₀ →ₗ[R] Crys κ (spMap π) B₀ →ₗ[R] R} (hφ₀ : IsCorrForm κ (spMap π) A₀ B₀ P₀ φ₀)
    (z : ∀ a ∈ liftFil κ h, ∀ b ∈ liftFil κ k, φ₀ a b = 0) :
    ∃ P : LB (A ⊗ B).left, P.IsLB ∧ IsAdditive P ∧ IsAdditive (swap P) ∧ LBIso (P.pull l) P₀ := by
  obtain ⟨D, _, Q, D₀, _, d, m, hD, gD, q, q', kd, m₁, m₂, q₀, q₀'⟩ := exists_dual_pair HD hA hg h
  obtain ⟨x₀, _, e₀⟩ := exists_hom q₀ q₀' hP₀ a₁ a₂
  obtain ⟨⟨ψ, hψ, -⟩, perf⟩ := AbelianDualCrystal.duality HR hA hg hD gD (q.isPerfect q')
  obtain ⟨ψ₀, hψ₀, eψ⟩ := AbelianDualCrystal.exists_crystal_pairing κ h kd m₁ m₂ q.isLB q₀.isLB
    ((cls_eq_iff q₀.isLB q₀.isLB).1 rfl) hψ
  have adj : ∀ a b, ψ₀ a (push κ (spMap π) x₀ b) = φ₀ a b := fun a b ↦ by
    have := hψ₀.adjoint C q₀.isLB hP₀ hφ₀ (𝟙 A₀) x₀ ((cls_eq_iff (pull_isLB q₀.isLB _) (pull_isLB hP₀ _)).1 <| by
      rw [cls_ev q₀.isLB, cls_ev hP₀, evc_of_cls q₀.isLB hP₀ e₀, Category.comp_id]) a b
    rwa [push_id] at this
  obtain ⟨x, ⟨_, ex⟩, -⟩ := HG.2.2 g' B₀ B j k hB hg' g D₀ D d kd hD gD x₀ fun b hb ↦ by
    refine ((perf ψ hψ).2.2 _).2 fun a ha ↦ ?_
    obtain ⟨a, rfl⟩ := (HG.1.crysToDR_bijective h hA hg).2 a
    rw [← eψ, adj]
    exact z a ha b hb
  have hP : (ev Q (fst A B) (snd A B ≫ x)).IsLB := pull_isLB q.isLB _
  obtain ⟨b₁, b₂⟩ := additive_ev q.isLB q.additive q'.additive x
  refine ⟨_, hP, b₁, b₂, (cls_eq_iff (pull_isLB hP _) hP₀).1 ?_⟩
  rw [cls_pull hP, cls_ev q.isLB, e₀]
  exact pull_evc_eq l₁ l₂ m₁ m₂ q.isLB q₀.isLB ex

theorem lift_unique_of_additive (HG : GrothendieckMessing.LiftHom κ π) (HD : DualAbelianScheme)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) (hB : IsAbelianScheme B)
    (hg' : SmoothOfRelativeDimension g' B.hom) (h : IsGrpPullback A₀ A (spMap π) i)
    (k : IsGrpPullback B₀ B (spMap π) j) (l₁ : l ≫ (fst A B).left = (fst A₀ B₀).left ≫ i)
    (l₂ : l ≫ (snd A B).left = (snd A₀ B₀).left ≫ j) {P P' : LB (A ⊗ B).left} (hP : P.IsLB) (a₁ : IsAdditive P)
    (a₂ : IsAdditive (swap P)) (hP' : P'.IsLB) (a₁' : IsAdditive P') (a₂' : IsAdditive (swap P'))
    (e : LBIso (P.pull l) (P'.pull l)) : LBIso P P' := by
  obtain ⟨D, _, Q, D₀, _, d, m, hD, gD, q, q', kd, m₁, m₂, q₀, q₀'⟩ := exists_dual_pair HD hA hg h
  obtain ⟨x, _, ex⟩ := exists_hom q q'.additive hP a₁ a₂
  obtain ⟨x', _, ex'⟩ := exists_hom q q'.additive hP' a₁' a₂'
  have hP₀ := pull_isLB hP' l
  obtain ⟨b₁, b₂⟩ := additive_pull h k l₁ l₂ hP hP₀ e a₁ a₂
  obtain ⟨x₀, _, e₀⟩ := exists_hom q₀ q₀' hP₀ b₁ b₂
  have red : ∀ y : B ⟶ D, CechPic.pull l (evc q.isLB (fst A B) (snd A B ≫ y)) = cls _ hP₀ →
      j ≫ y.left = x₀.left ≫ d := fun y hy ↦ by
    have w : (j ≫ y.left) ≫ D.hom = B₀.hom ≫ spMap π := by rw [Category.assoc, Over.w y, k.1.w]
    have ey : j ≫ y.left = (liftPt kd B₀.hom _ w).left ≫ d := (liftPt_left kd _ _ w).symm
    have : (liftPt kd B₀.hom _ w : B₀ ⟶ D₀) = x₀ := dual_ext q₀ <|
      (pull_evc_eq l₁ l₂ m₁ m₂ q.isLB q₀.isLB (x' := (liftPt kd B₀.hom _ w : B₀ ⟶ D₀)) ey).symm.trans
        (hy.trans e₀)
    rw [← this]
    exact ey
  obtain rfl : x = x' := HG.unique k hB hg' kd hD gD x₀
    (red x (by rw [← ex, ← cls_pull hP l (pull_isLB hP l)]; exact (cls_eq_iff _ _).2 e))
    (red x' (by rw [← ex', ← cls_pull hP' l hP₀]))
  exact (cls_eq_iff hP hP').1 (ex.trans ex'.symm)

theorem vanish_of_lift (HR : AbelianDeRham) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    (hB : IsAbelianScheme B) (hg' : SmoothOfRelativeDimension g' B.hom) (h : IsGrpPullback A₀ A (spMap π) i)
    (k : IsGrpPullback B₀ B (spMap π) j) (l₁ : l ≫ (fst A B).left = (fst A₀ B₀).left ≫ i)
    (l₂ : l ≫ (snd A B).left = (snd A₀ B₀).left ≫ j) (C : CupSquare κ (spMap π) (A₀ ⊗ B₀))
    {P : LB (A ⊗ B).left} (hP : P.IsLB) (h₁ : Triv (ev P (1 : B ⟶ A) (𝟙 B))) (h₂ : Triv (ev P (𝟙 A) (1 : A ⟶ B)))
    {P₀ : LB (A₀ ⊗ B₀).left} (hP₀ : P₀.IsLB) (e : LBIso (P.pull l) P₀)
    {φ₀ : Crys κ (spMap π) A₀ →ₗ[R] Crys κ (spMap π) B₀ →ₗ[R] R} (hφ₀ : IsCorrForm κ (spMap π) A₀ B₀ P₀ φ₀) :
    ∀ a ∈ liftFil κ h, ∀ b ∈ liftFil κ k, φ₀ a b = 0 := by
  intro a ha b hb
  have hAB := AbelianSchemeGerms.isAbelianScheme_tensor A B hA hB
  have gAB := smooth_prod hg hg'
  obtain ⟨φ, hφ⟩ := exists_isCorrForm (cupSquare_of_free HR.1 hAB gAB) hP h₁ h₂
  obtain ⟨φ₁, h₀, e₀⟩ := AbelianDualCrystal.exists_crystal_pairing κ h k l₁ l₂ hP hP₀ e hφ
  obtain rfl := hφ₀.unique C hP₀ h₀
  obtain ⟨ψ, hψ, eψ⟩ := hφ.isPolForm
  have t := (HR.2.2.2.2 R _ _ hAB gAB P hP ψ hψ).1 _ (push_mem_Fil (inl A B) ha) _ (push_mem_Fil (inr A B) hb)
  rw [eψ, push_push _ _ _ (lift_fst _ _), push_push _ _ _ (lift_snd _ _), push_push _ _ _ (lift_fst _ _),
    push_id, push_id, push_one] at t
  rw [e₀]
  simpa using t

theorem exists_additive_lift_iff (HG : GrothendieckDeformation) (HR : AbelianDeRham) (HD : AbelianDualCrystal)
    (hκ : IsNilDP κ) (hπ : Function.Surjective π) (hI : RingHom.ker π = I)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) (hB : IsAbelianScheme B)
    (hg' : SmoothOfRelativeDimension g' B.hom) (h : IsGrpPullback A₀ A (spMap π) i)
    (k : IsGrpPullback B₀ B (spMap π) j) (l₁ : l ≫ (fst A B).left = (fst A₀ B₀).left ≫ i)
    (l₂ : l ≫ (snd A B).left = (snd A₀ B₀).left ≫ j)
    {P₀ : LB (A₀ ⊗ B₀).left} (hP₀ : P₀.IsLB) (a₁ : IsAdditive P₀) (a₂ : IsAdditive (swap P₀))
    {φ₀ : Crys κ (spMap π) A₀ →ₗ[R] Crys κ (spMap π) B₀ →ₗ[R] R} (hφ₀ : IsCorrForm κ (spMap π) A₀ B₀ P₀ φ₀) :
    (∃ P : LB (A ⊗ B).left, P.IsLB ∧ IsAdditive P ∧ IsAdditive (swap P) ∧ LBIso (P.pull l) P₀) ↔
      ∀ a ∈ liftFil κ h, ∀ b ∈ liftFil κ k, φ₀ a b = 0 :=
  have C := AbelianDualCrystal.cupSquare_crys_prod HR.1 HD.2 hκ hπ hI hA hg hB hg' h k
  ⟨fun ⟨_, hP, b₁, b₂, e⟩ ↦ vanish_of_lift HR hA hg hB hg' h k l₁ l₂ C hP (triv_left hP b₁) (triv_right hP b₂)
      hP₀ e hφ₀,
    exists_lift_of_cupSquare (HG R I κ hκ R₀ π hπ hI) HR HD.1 hA hg hB hg' h k l₁ l₂ C hP₀ a₁ a₂ hφ₀⟩

theorem exists_lift (HG : GrothendieckDeformation) (HR : AbelianDeRham) (HD : AbelianDualCrystal)
    (hκ : IsNilDP κ) (hπ : Function.Surjective π) (hI : RingHom.ker π = I)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) (hB : IsAbelianScheme B)
    (hg' : SmoothOfRelativeDimension g' B.hom) (h : IsGrpPullback A₀ A (spMap π) i)
    (k : IsGrpPullback B₀ B (spMap π) j) (l₁ : l ≫ (fst A B).left = (fst A₀ B₀).left ≫ i)
    (l₂ : l ≫ (snd A B).left = (snd A₀ B₀).left ≫ j)
    {L : LB A₀.left} (hL : L.IsLB) (aL : Out.RelAmple A₀ L) {M : LB B₀.left} (hM : M.IsLB) (aM : Out.RelAmple B₀ M)
    {P₀ : LB (A₀ ⊗ B₀).left} (hP₀ : P₀.IsLB) (h₁ : Triv (ev P₀ (1 : B₀ ⟶ A₀) (𝟙 B₀)))
    (h₂ : Triv (ev P₀ (𝟙 A₀) (1 : A₀ ⟶ B₀)))
    {φ₀ : Crys κ (spMap π) A₀ →ₗ[R] Crys κ (spMap π) B₀ →ₗ[R] R} (hφ₀ : IsCorrForm κ (spMap π) A₀ B₀ P₀ φ₀)
    (z : ∀ a ∈ liftFil κ h, ∀ b ∈ liftFil κ k, φ₀ a b = 0) :
    ∃ P : LB (A ⊗ B).left, P.IsLB ∧ Triv (ev P (1 : B ⟶ A) (𝟙 B)) ∧ Triv (ev P (𝟙 A) (1 : A ⟶ B)) ∧
      IsAdditive P ∧ IsAdditive (swap P) ∧ LBIso (P.pull l) P₀ := by
  have hA₀ := PolPull.isAbelianScheme_of_isGrpPullback hA h
  have hB₀ := PolPull.isAbelianScheme_of_isGrpPullback hB k
  obtain ⟨H, hH, aH⟩ := exists_relAmple_prod hA₀ hB₀ hL aL hM aM
  obtain ⟨a₁, a₂⟩ := additive_of_triv hA₀ hB₀ hH aH hP₀ h₁ h₂
  obtain ⟨P, hP, b₁, b₂, e⟩ :=
    (exists_additive_lift_iff HG HR HD hκ hπ hI hA hg hB hg' h k l₁ l₂ hP₀ a₁ a₂ hφ₀).2 z
  exact ⟨P, hP, triv_left hP b₁, triv_right hP b₂, b₁, b₂, e⟩

theorem lift_unique (HG : GrothendieckDeformation) (HD : DualAbelianScheme)
    (hκ : IsNilDP κ) (hπ : Function.Surjective π) (hI : RingHom.ker π = I)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) (hB : IsAbelianScheme B)
    (hg' : SmoothOfRelativeDimension g' B.hom) (h : IsGrpPullback A₀ A (spMap π) i)
    (k : IsGrpPullback B₀ B (spMap π) j) (l₁ : l ≫ (fst A B).left = (fst A₀ B₀).left ≫ i)
    (l₂ : l ≫ (snd A B).left = (snd A₀ B₀).left ≫ j)
    {L : LB A.left} (hL : L.IsLB) (aL : Out.RelAmple A L) {M : LB B.left} (hM : M.IsLB) (aM : Out.RelAmple B M)
    {P₀ : LB (A₀ ⊗ B₀).left} (hP₀ : P₀.IsLB) {P P' : LB (A ⊗ B).left} (hP : P.IsLB)
    (h₁ : Triv (ev P (1 : B ⟶ A) (𝟙 B))) (h₂ : Triv (ev P (𝟙 A) (1 : A ⟶ B))) (e : LBIso (P.pull l) P₀)
    (hP' : P'.IsLB) (h₁' : Triv (ev P' (1 : B ⟶ A) (𝟙 B))) (h₂' : Triv (ev P' (𝟙 A) (1 : A ⟶ B)))
    (e' : LBIso (P'.pull l) P₀) : LBIso P P' := by
  obtain ⟨H, hH, aH⟩ := exists_relAmple_prod hA hB hL aL hM aM
  obtain ⟨a₁, a₂⟩ := additive_of_triv hA hB hH aH hP h₁ h₂
  obtain ⟨a₁', a₂'⟩ := additive_of_triv hA hB hH aH hP' h₁' h₂'
  exact lift_unique_of_additive (HG R I κ hκ R₀ π hπ hI).2.2 HD hA hg hB hg' h k l₁ l₂ hP a₁ a₂ hP' a₁' a₂'
    ((cls_eq_iff (pull_isLB hP l) (pull_isLB hP' l)).1
      (((cls_eq_iff (pull_isLB hP l) hP₀).2 e).trans ((cls_eq_iff (pull_isLB hP' l) hP₀).2 e').symm))

end GlobalTheory.BirigidLift
