import Mathlib
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.DualUniv

theorem isIso_of_closedImmersion {R : Type} [CommRing R] {Z : Scheme.{0}} (f : Z ⟶ Sp R) [IsClosedImmersion f]
    [Flat f] [Surjective f] : IsIso f := by
  have : IsAffine Z := isAffine_of_isAffineHom f
  have h₁ : f.appTop.hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).1 ⟨inferInstance, inferInstance⟩
  have h₂ : Function.Surjective f.appTop.hom := (IsClosedImmersion.isAffine_surjective_of_isAffine f).2
  have h₃ : Function.Bijective f.appTop.hom := ⟨h₁.injective, h₂⟩
  have : IsIso f.appTop := (ConcreteCategory.isIso_iff_bijective _).2 h₃
  exact (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme) (arrowIsoSpecΓOfIsAffine f)).2
    (inferInstanceAs (IsIso (Spec.map f.appTop)))

variable {S : Scheme.{0}}

def IsAddCls (A : Over S) [GrpObj A] (m : Pic A.left) : Prop :=
  ∀ (Y : Over S) (a a' : Y ⟶ A),
    CechPic.pull (a * a').left m = CechPic.pull a.left m + CechPic.pull a'.left m

theorem preDual_baseChange {S' : Scheme.{0}} {b : S' ⟶ S} {A B : Over S} [GrpObj A] [GrpObj B] {A' B' : Over S'}
    [GrpObj A'] [GrpObj B'] {f : A'.left ⟶ A.left} {g : B'.left ⟶ B.left} {h : (A' ⊗ B').left ⟶ (A ⊗ B).left}
    (hf : IsGrpPullback A' A b f) (hg : IsGrpPullback B' B b g)
    (h₁ : h ≫ (fst A B).left = (fst A' B').left ≫ f) (h₂ : h ≫ (snd A B).left = (snd A' B').left ≫ g)
    {P : LB (A ⊗ B).left} {P' : LB (A' ⊗ B').left} (hP' : P'.IsLB) (e : LBIso (P.pull h) P')
    (hd : PreDual A B P) : PreDual A' B' P' := by
  obtain ⟨a₁, a₂⟩ := GlobalTheory.BirigidLift.additive_pull hf hg h₁ h₂ hd.isLB hP' e hd.add₁ hd.add₂
  refine ⟨hP', a₁, a₂, fun T y hy ↦ ?_, fun k _ _ t ↦ ?_⟩
  · have h0 := hd.right _ (pushP hg (s := T.hom) rfl y) ((triv_ev_iff hd.isLB _ _).2 (by
      rw [← evc_trR hf hg h₁ h₂ hd.isLB hP' e, (triv_ev_iff hP' _ _).1 hy, map_zero]))
    exact pt_ext hg ((congrArg (fun z ↦ z.left) h0).trans (one_left_comp hg (s := T.hom) rfl).symm)
  · refine Set.Finite.of_injOn (f := pushP hf (s := t) rfl) (fun x hx ↦ ?_)
      (fun x _ y _ e ↦ pt_ext hf (congrArg (fun z ↦ z.left) e)) (hd.left k (t ≫ b))
    refine (triv_ev_iff hd.isLB _ _).2 ?_
    have := evc_trL hf hg h₁ h₂ hd.isLB hP' e (Over.mk t) x
    rw [(triv_ev_iff hP' _ _).1 hx, map_zero] at this
    exact this.symm

theorem exists_point_fibre (H3 : PointSurj) {A B : Over S} [GrpObj A] [GrpObj B] (hA : IsAbelianScheme A)
    (hB : IsAbelianScheme B) {P : LB (A ⊗ B).left} (hP : PreDual A B P) {m : Pic A.left} (hm : IsAddCls A m)
    (k : Type) [Field k] [IsAlgClosed k] (s : Sp k ⟶ S) :
    ∃ y : Over.mk ((𝟙_ (Over (Sp k))).hom ≫ s) ⟶ B,
      evc hP.isLB (fst A (Over.mk ((𝟙_ (Over (Sp k))).hom ≫ s)))
          (snd A (Over.mk ((𝟙_ (Over (Sp k))).hom ≫ s)) ≫ y) =
        CechPic.pull (fst A (Over.mk ((𝟙_ (Over (Sp k))).hom ≫ s))).left m := by
  have hf := isGrpPullback_pullback A s
  have hg := isGrpPullback_pullback B s
  obtain ⟨h, h₁, h₂⟩ := exists_prod_pullback hf hg
  have hP' : (P.pull h).IsLB := pull_isLB hP.isLB h
  have e : LBIso (P.pull h) (P.pull h) := (cls_eq_iff hP' hP').1 rfl
  have hd := preDual_baseChange hf hg h₁ h₂ hP' e hP
  have hA' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hf
  have hB' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hB hg
  obtain ⟨M, hM, eM⟩ := cls_surj (CechPic.pull
    ((fst ((Over.pullback s).obj A) (𝟙_ (Over (Sp k)))).left ≫ pullback.fst A.hom s) m)
  have hadd : IsAdditive M := (isAdditive_iff hM).2 fun Y a a' t ↦ by
    simp only [evc, eM, ← pull_comp, lift_left_fst_assoc]
    rw [mul_left_comp hf (s₀ := Y.hom ≫ s) rfl (x := a) (y := a') (x₀ := pushP hf (s := Y.hom) rfl a)
      (y₀ := pushP hf (s := Y.hom) rfl a') rfl rfl]
    exact hm _ _ _
  have fin : Set.Finite {x : 𝟙_ (Over (Sp k)) ⟶ (Over.pullback s).obj A |
      Triv (ev (P.pull h) (toUnit ((Over.pullback s).obj B) ≫ x) (𝟙 ((Over.pullback s).obj B)))} := by
    refine (hd.left k (𝟙 _)).subset fun x hx ↦ ?_
    refine (triv_ev_iff hP' _ _).2 ?_
    have e₂ := congrArg (CechPic.pull (snd (𝟙_ (Over (Sp k))) ((Over.pullback s).obj B)).left)
      ((triv_ev_iff hP' _ _).1 hx)
    rw [pull_evc, map_zero, Category.comp_id, ← Category.assoc,
      toUnit_unique (snd (𝟙_ (Over (Sp k))) ((Over.pullback s).obj B) ≫ toUnit _) (fst _ _)] at e₂
    exact e₂
  obtain ⟨y, hy⟩ := H3 k _ _ hA' hB' (P.pull h) hP' hd.add₁ hd.add₂ fin M hM hadd
  refine ⟨pushP hg (s := (𝟙_ (Over (Sp k))).hom) rfl y, ?_⟩
  have c := (cls_eq_iff hM (pull_isLB hP' _)).2 hy
  rw [← evc_trR hf hg h₁ h₂ hP.isLB hP' e]
  have c' : evc hP' (fst _ _) (snd _ _ ≫ y) = _ := c.symm.trans eM
  rw [c', ← pull_comp]
  exact congrArg (fun q ↦ CechPic.pull q m) (trR_fst hf _)

theorem exists_section (H1 : TrivLocus) (H2 : TrivLocusFlat) (H3 : PointSurj) {C : Type} [CommRing C]
    [IsNoetherianRing C] (A B : Over (Sp C)) [GrpObj A] [GrpObj B] (g : ℕ) (hA : IsAbelianScheme A)
    (hB : IsAbelianScheme B) (gA : SmoothOfRelativeDimension g A.hom) (gB : SmoothOfRelativeDimension g B.hom)
    {P : LB (A ⊗ B).left} (hP : PreDual A B P) {m : Pic A.left} (hm : IsAddCls A m) :
    ∃ x : Over.mk (𝟙 (Sp C)) ⟶ B, evc hP.isLB (fst A (Over.mk (𝟙 (Sp C)))) (snd A (Over.mk (𝟙 (Sp C))) ≫ x) =
      CechPic.pull (fst A (Over.mk (𝟙 (Sp C)))).left m := by
  obtain ⟨N, hN, eN⟩ := cls_surj (cls P hP.isLB - CechPic.pull (fst A B).left m)
  have ecl : ∀ {Y : Over (Sp C)} (a : Y ⟶ A) (t : Y ⟶ B),
      evc hN a t = evc hP.isLB a t - CechPic.pull a.left m := by
    intro Y a t
    rw [evc, eN, map_sub, ← pull_comp, lift_left_fst]
    rfl
  have rep : ∀ (T : Over (Sp C)) (y : T ⟶ B), Triv (ev N (fst A T) (snd A T ≫ y)) ↔
      evc hP.isLB (fst A T) (snd A T ≫ y) = CechPic.pull (fst A T).left m := fun T y ↦ by
    rw [triv_ev_iff hN, ecl, sub_eq_zero]
  have h0 : Triv (ev N (1 : B ⟶ A) (𝟙 B)) := by
    have z : CechPic.pull (1 : B ⟶ A).left m = 0 := by
      have := hm B 1 1
      rw [_root_.mul_one] at this
      exact left_eq_add.1 this
    rw [triv_ev_iff hN, ecl, hP.add₁.evc_one hP.isLB, z, sub_zero]
  have tr := GlobalTheory.BirigidLift.triv_right hP.isLB hP.add₂
  have uniq : ∀ (T : Over (Sp C)) (y y' : T ⟶ B),
      evc hP.isLB (fst A T) (snd A T ≫ y) = CechPic.pull (fst A T).left m →
      evc hP.isLB (fst A T) (snd A T ≫ y') = CechPic.pull (fst A T).left m → y = y' := by
    intro T y y' e e'
    have a2 := (GlobalTheory.BirigidLift.isAdditive_swap_iff hP.isLB).1 hP.add₂
    have k1 := a2 _ (fst A T) (snd A T ≫ y) (snd A T ≫ y'⁻¹)
    have k2 := a2 _ (fst A T) (snd A T ≫ y') (snd A T ≫ y'⁻¹)
    rw [← MonObj.comp_mul] at k1 k2
    rw [_root_.mul_inv_cancel, MonObj.comp_one, evc_one_right hP.isLB tr] at k2
    have z := hP.right T (y * y'⁻¹) ((triv_ev_iff hP.isLB _ _).2 (by rw [k1, e, ← e', ← k2]))
    exact mul_inv_eq_one.1 z
  have : LocallyOfFiniteType B.hom := by
    have := hB.smooth
    infer_instance
  have : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
  obtain ⟨Z, i, hci, hiff⟩ := H1 _ A B hA ‹_› N hN h0
  have : IsClosedImmersion i.left := hci
  have hw : i.left ≫ B.hom = Z.hom := Over.w i
  have hmono : Mono Z.hom := ⟨fun {W} u v e ↦ by
    let u' : Over.mk (u ≫ Z.hom) ⟶ Z := Over.homMk u rfl
    let v' : Over.mk (u ≫ Z.hom) ⟶ Z := Over.homMk v e.symm
    have e₁ := uniq _ (u' ≫ i) (v' ≫ i) ((rep _ _).1 ((hiff _ _).2 ⟨u', rfl⟩))
      ((rep _ _).1 ((hiff _ _).2 ⟨v', rfl⟩))
    exact (cancel_mono i.left).1 (congrArg (fun q ↦ q.left) e₁)⟩
  have hprop : IsProper Z.hom := by
    have := hB.proper
    rw [← hw]
    infer_instance
  have hcl : IsClosedImmersion Z.hom := (IsClosedImmersion.iff_isProper_and_mono _).2 ⟨hprop, hmono⟩
  have hfl : Flat Z.hom := H2 _ A B Z g hA gA gB N hN i ⟨hci, hiff⟩ inferInstance
  have hsu : Surjective Z.hom := ⟨fun c ↦ by
    let κ := (Sp C).residueField c
    let k := AlgebraicClosure κ
    let s : Sp k ⟶ Sp C := Spec.map (CommRingCat.ofHom (algebraMap κ k)) ≫ (Sp C).fromSpecResidueField c
    obtain ⟨y, hy⟩ := exists_point_fibre H3 hA hB hP hm k s
    obtain ⟨z, rfl⟩ := (hiff _ y).1 ((rep _ _).2 hy)
    obtain ⟨p⟩ : Nonempty (Sp k) := inferInstance
    refine ⟨z.left p, ?_⟩
    have e : z.left ≫ Z.hom = (𝟙_ (Over (Sp k))).hom ≫ s := Over.w z
    have e' : z.left ≫ Z.hom = s := e.trans (Category.id_comp s)
    rw [← Scheme.Hom.comp_apply, e']
    exact (Scheme.Hom.comp_apply _ _ p).trans (Scheme.fromSpecResidueField_apply c _)⟩
  have : IsIso Z.hom := isIso_of_closedImmersion Z.hom
  let z : Over.mk (𝟙 (Sp C)) ⟶ Z := Over.homMk (inv Z.hom) (by simp)
  exact ⟨z ≫ i, (rep _ _).1 ((hiff _ _).2 ⟨z, rfl⟩)⟩

theorem univNoeth : TrivLocus → TrivLocusFlat → PointSurj → ∀ (R : Type) [CommRing R] [IsNoetherianRing R]
    (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B →
    SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom →
    ∀ P : LB (A ⊗ B).left, PreDual A B P → UnivNoeth A B P := by
  intro H1 H2 H3 R _ _ A B _ _ g hA hB gA gB P hP C _ _ t M hM hadd
  have hf := isGrpPullback_pullback A t
  have hg := isGrpPullback_pullback B t
  obtain ⟨h, h₁, h₂⟩ := exists_prod_pullback hf hg
  have hP' : (P.pull h).IsLB := pull_isLB hP.isLB h
  have e : LBIso (P.pull h) (P.pull h) := (cls_eq_iff hP' hP').1 rfl
  have hd := preDual_baseChange hf hg h₁ h₂ hP' e hP
  have hA' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hf
  have hB' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hB hg
  have gA' : SmoothOfRelativeDimension g ((Over.pullback t).obj A).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hf.1 gA
  have gB' : SmoothOfRelativeDimension g ((Over.pullback t).obj B).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hg.1 gB
  let r : ((Over.pullback t).obj A).left ⟶ (A ⊗ Over.mk t).left :=
    Limits.pullback.lift (pullback.fst A.hom t) ((Over.pullback t).obj A).hom hf.1.w
  have r₁ : r ≫ (fst A (Over.mk t)).left = pullback.fst A.hom t := Limits.pullback.lift_fst _ _ _
  have r₂ : r ≫ (snd A (Over.mk t)).left = ((Over.pullback t).obj A).hom := Limits.pullback.lift_snd _ _ _
  have key : ∀ (Y : Over (Sp C)) (a : Y ⟶ (Over.pullback t).obj A) (a₀ : Over.mk (Y.hom ≫ t) ⟶ A),
      a.left ≫ pullback.fst A.hom t = a₀.left →
      CechPic.pull a.left (CechPic.pull r (cls M hM)) =
        evc hM a₀ (Over.homMk Y.hom rfl : Over.mk (Y.hom ≫ t) ⟶ Over.mk t) := by
    intro Y a a₀ ea
    rw [← pull_comp, evc]
    refine congrArg (fun q ↦ CechPic.pull q (cls M hM)) (left_ext ?_ ?_)
    · rw [Category.assoc, r₁, lift_left_fst, ea]
    · rw [Category.assoc, r₂, lift_left_snd]
      exact Over.w a
  have hm : IsAddCls ((Over.pullback t).obj A) (CechPic.pull r (cls M hM)) := fun Y a a' ↦ by
    rw [key Y (a * a') (pushP hf (s := Y.hom) rfl a * pushP hf (s := Y.hom) rfl a')
        (mul_left_comp hf rfl rfl rfl), key Y a (pushP hf (s := Y.hom) rfl a) rfl,
      key Y a' (pushP hf (s := Y.hom) rfl a') rfl]
    exact (isAdditive_iff hM).1 hadd _ _ _ _
  obtain ⟨x', hx⟩ := exists_section H1 H2 H3 _ _ g hA' hB' gA' gB' hd hm
  have wx : x'.left ≫ ((Over.pullback t).obj B).hom = 𝟙 (Sp C) := Over.w x'
  let x : Over.mk t ⟶ B := Over.homMk (x'.left ≫ pullback.fst B.hom t) (by
    show (x'.left ≫ pullback.fst B.hom t) ≫ B.hom = t
    rw [Category.assoc, hg.1.w, ← Category.assoc, wx]
    exact Category.id_comp t)
  refine ⟨x, (cls_eq_iff hM (pull_isLB hP.isLB _)).1 ?_⟩
  have w : (fst A (Over.mk t)).left ≫ A.hom = (snd A (Over.mk t)).left ≫ t :=
    (Over.w (fst A (Over.mk t))).trans (Over.w (snd A (Over.mk t))).symm
  let a := liftPt hf (snd A (Over.mk t)).left (fst A (Over.mk t)).left w
  let τ : Over.mk (snd A (Over.mk t)).left ⟶ Over.mk (𝟙 (Sp C)) :=
    Over.homMk (snd A (Over.mk t)).left (by simp)
  have ar : a.left ≫ r = 𝟙 _ := by
    apply left_ext
    · rw [Category.assoc, r₁, Category.id_comp]
      exact liftPt_left _ _ _ _
    · rw [Category.assoc, r₂, Category.id_comp]
      exact Over.w a
  have c := congrArg (CechPic.pull (lift a τ).left) hx
  rw [pull_evc, ← pull_comp, lift_left_fst, lift_fst, lift_snd_assoc,
    evc_eq h₁ h₂ hP.isLB hP' e a (τ ≫ x') (fst A (Over.mk t)) (snd A (Over.mk t) ≫ x)
      (liftPt_left _ _ _ _) rfl, ← pull_comp, ar] at c
  exact (c.trans (pull_id _)).symm

end GlobalTheory.CompanionTheory.DualUniv
