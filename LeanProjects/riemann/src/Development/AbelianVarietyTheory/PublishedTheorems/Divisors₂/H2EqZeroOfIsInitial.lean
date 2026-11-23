import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AbDual

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published.AbelianDualCrystal.Test

section Dual

variable {S : Scheme.{0}} {A B A₁ B₁ : Over S} [GrpObj A] [GrpObj B] [GrpObj A₁] [GrpObj B₁]
  {P : LB (A ⊗ B).left} {P₁ : LB (A₁ ⊗ B₁).left}

theorem point_ext (h : IsDual A B P) {T : Over S} {x y : T ⟶ B}
    (e : evc h.isLB (fst A T) (snd A T ≫ x) = evc h.isLB (fst A T) (snd A T ≫ y)) : x = y := by
  have hM : (ev P (fst A T) (snd A T ≫ x)).IsLB := pull_isLB h.isLB _
  refine (h.univ T _ hM ((isAdditive_iff hM).2 fun Y a a' t ↦ ?_)).unique
    ((cls_eq_iff hM hM).1 rfl) ((cls_eq_iff hM (pull_isLB h.isLB _)).1 e)
  simp only [evc_ev h.isLB, lift_fst, lift_snd_assoc]
  exact (isAdditive_iff h.isLB).1 h.additive _ _ _ _

theorem exists_dualHom (h : IsDual A B P) (h' : IsDual B A (swap P)) (h₁ : IsDual A₁ B₁ P₁)
    (h₁' : IsDual B₁ A₁ (swap P₁)) (u : A ⟶ A₁) [IsMonHom u] :
    ∃ v : B₁ ⟶ B, IsMonHom v ∧ LBIso (ev P (fst A B₁) (snd A B₁ ≫ v)) (ev P₁ (fst A B₁ ≫ u) (snd A B₁)) ∧
      ∀ v' : B₁ ⟶ B, LBIso (ev P (fst A B₁) (snd A B₁ ≫ v')) (ev P₁ (fst A B₁ ≫ u) (snd A B₁)) → v' = v := by
  have hM : (ev P₁ (fst A B₁ ≫ u) (snd A B₁)).IsLB := pull_isLB h₁.isLB _
  obtain ⟨v, hv, hu⟩ := h.univ B₁ _ hM ((isAdditive_iff hM).2 fun Y a a' t ↦ by
    simp only [evc_ev h₁.isLB, lift_fst_assoc, lift_snd, MonObj.mul_comp]
    exact (isAdditive_iff h₁.isLB).1 h₁.additive _ _ _ _)
  have e := (cls_eq_iff hM (pull_isLB h.isLB _)).2 hv
  have k : ∀ (Y : Over S) (a : Y ⟶ A) (b : Y ⟶ B₁), evc h.isLB a (b ≫ v) = evc h₁.isLB (a ≫ u) b := fun Y a b ↦ by
    have := congrArg (CechPic.pull (lift a b).left) e
    rw [cls_ev h₁.isLB, cls_ev h.isLB, pull_evc, pull_evc] at this
    simpa using this.symm
  have add : ∀ {C D : Over S} [GrpObj C] [GrpObj D] {Q : LB (C ⊗ D).left} (hQ : Q.IsLB) (_ : IsDual D C (swap Q))
      (Y : Over S) (a : Y ⟶ C) (b b' : Y ⟶ D), evc hQ a (b * b') = evc hQ a b + evc hQ a b' := by
    intro C D _ _ Q hQ q Y a b b'
    simpa only [evc_swap hQ] using (isAdditive_iff q.isLB).1 q.additive Y b b' a
  have m : ∀ (Y : Over S) (b b' : Y ⟶ B₁), (b * b') ≫ v = (b ≫ v) * (b' ≫ v) := fun Y b b' ↦
    point_ext h (by
      rw [← Category.assoc, k, MonObj.comp_mul, MonObj.comp_mul, add h₁.isLB h₁', add h.isLB h',
        ← Category.assoc, ← Category.assoc, k, k])
  refine ⟨v, ⟨?_, ?_⟩, (cls_eq_iff (pull_isLB h.isLB _) hM).1 e.symm,
    fun v' hv' ↦ hu v' ((cls_eq_iff hM (pull_isLB h.isLB _)).1 ((cls_eq_iff (pull_isLB h.isLB _) hM).2 hv').symm)⟩
  · have := m (𝟙_ _) 1 1
    rw [_root_.mul_one] at this
    have e1 : (1 : 𝟙_ (Over S) ⟶ B₁) ≫ v = 1 := left_eq_mul.1 this
    simpa [Hom.one_def] using e1
  · have := m (B₁ ⊗ B₁) (fst _ _) (snd _ _)
    simpa [Hom.mul_def, lift_fst_comp_snd_comp] using this

theorem dual_unique {B' : Over S} [GrpObj B'] {P' : LB (A ⊗ B').left} (h : IsDual A B P) (h' : IsDual A B' P') :
    Nonempty (B ≅ B') := by
  have key : ∀ {C D : Over S} [GrpObj C] [GrpObj D] {Q : LB (A ⊗ C).left} {Q' : LB (A ⊗ D).left}
      (q : IsDual A C Q) (q' : IsDual A D Q'), ∃ x : C ⟶ D, ∀ (Y : Over S) (a : Y ⟶ A) (b : Y ⟶ C),
        evc q'.isLB a (b ≫ x) = evc q.isLB a b := by
    intro C D _ _ Q Q' q q'
    obtain ⟨x, hx, -⟩ := q'.univ C Q q.isLB q.additive
    refine ⟨x, fun Y a b ↦ ?_⟩
    have := congrArg (CechPic.pull (lift a b).left) ((cls_eq_iff q.isLB (pull_isLB q'.isLB _)).2 hx)
    rw [cls_ev q'.isLB, pull_evc] at this
    simpa [evc] using this.symm
  obtain ⟨x, hx⟩ := key h h'
  obtain ⟨y, hy⟩ := key h' h
  exact ⟨⟨x, y, point_ext h (by rw [← Category.assoc, hy, hx, Category.comp_id]),
    point_ext h' (by rw [← Category.assoc, hx, hy, Category.comp_id])⟩⟩

theorem id_eq_one_of_dual (h : IsDual A B P) (h' : IsDual B A (swap P)) (e : 𝟙 B = 1) : 𝟙 A = 1 := by
  have p := h.isPerfect h'
  refine p.ker_left _ _ ((triv_ev_iff h.isLB _ _).2 ?_)
  rw [← Category.comp_id (snd A B), e, MonObj.comp_one, evc_one_right h.isLB h.zero]

theorem id_eq_one_of_triv (h : IsDual A B (LB.triv _)) : 𝟙 B = 1 :=
  h.eq_one _ ((triv_ev_iff h.isLB _ _).2 (map_zero _))

theorem isDual_unit_swap : IsDual (𝟙_ (Over S)) (𝟙_ (Over S)) (swap (LB.triv _)) := by
  have hs : (swap (LB.triv (𝟙_ (Over S) ⊗ 𝟙_ (Over S)).left)).IsLB := pull_isLB (LB.isLB_triv _) _
  have h0 : ∀ (Y : Over S) (a b : Y ⟶ 𝟙_ (Over S)), evc hs a b = 0 := fun _ _ _ ↦ by
    rw [evc_swap (LB.isLB_triv _)]; exact map_zero _
  refine ⟨hs, (isAdditive_iff hs).2 fun _ _ _ _ ↦ by simp only [h0, add_zero],
    (triv_ev_iff hs _ _).2 (h0 _ _ _), fun T M hM ha ↦ ⟨toUnit T, ?_, fun _ _ ↦ toUnit_unique _ _⟩⟩
  refine (cls_eq_iff hM (pull_isLB hs _)).1 ?_
  have e := ha.evc_one hM (snd (𝟙_ (Over S)) T)
  rw [toUnit_unique 1 (fst _ T), evc, lift_fst_snd, Over.id_left, CechPic.pull_id] at e
  rw [e, cls_ev hs, h0]

theorem elliptic_dual (H : DualAbelianScheme) {R : Type} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic] :
    ∃ (B : Over (Sp R)) (_ : GrpObj B) (P : LB ((WeierstrassCurve.ellPolAV W).A ⊗ B).left), IsAbelianScheme B ∧
      SmoothOfRelativeDimension 1 B.hom ∧ IsPerfect _ B P := by
  obtain ⟨B, _, P, hB, hg, h, h'⟩ := H _ _ (WeierstrassCurve.ellPolAV W).isAb
  exact ⟨B, _, P, hB, hg 1 (WeierstrassCurve.ellPolAV W).smoothDim, h.isPerfect h'⟩

end Dual

section Crystal

theorem h2_eq_zero_of_isInitial {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {T₀ : C}
    (h : Limits.IsInitial T₀) (c : CatCoh.H2 F) : c = 0 := by
  obtain ⟨z, rfl⟩ := CatCoh.H2.mk_surjective F c
  refine CatCoh.H2.mk_eq_zero.2 ⟨fun T T' φ ↦ z.1 T₀ T T' (h.to T) φ, ?_⟩
  funext T T' T'' φ ψ
  have := z.2 (h.to T) φ ψ
  rw [h.to_comp] at this
  rw [d1_apply]
  linear_combination this

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {κ : DividedPowers I} {π : R →+* R₀}

def baseThick (hκ : IsNilDP κ) (hπ : Function.Surjective π) (hI : RingHom.ker π = I) : Thick κ (spMap π) where
  B := R
  J := I
  δ := κ
  nil := hκ
  dp := (DPMorphism.id κ).isDPMorphism
  B₀ := R₀
  π := π
  surj := hπ
  ker b := by rw [← hI]; rfl
  x := 𝟙 _
  w := Category.id_comp _

theorem nonempty_isInitial (hκ : IsNilDP κ) (hπ : Function.Surjective π) (hI : RingHom.ker π = I) :
    Nonempty (Limits.IsInitial (baseThick hκ hπ hI)) := by
  have ex : ∀ T : Thick κ (spMap π), Nonempty (baseThick hκ hπ hI ⟶ T) := fun T ↦ by
    obtain ⟨f, hf⟩ := Spec.map_surjective T.x
    have w := T.w
    rw [← hf, ← Spec.map_comp] at w
    have w' := congrArg CommRingCat.Hom.hom (Spec.map_injective w)
    exact ⟨⟨Algebra.ofId R T.B, f.hom, fun b ↦ RingHom.congr_fun w' b, T.dp, (Category.comp_id _).trans hf⟩⟩
  exact ⟨Limits.IsInitial.ofUniqueHom (fun T ↦ (ex T).some) fun T m ↦ Thick.hom_ext fun b ↦
    (m.φ.commutes b).trans ((ex T).some.φ.commutes b).symm⟩

theorem base_case (hκ : IsNilDP κ) (hπ : Function.Surjective π) (hI : RingHom.ker π = I)
    (m : IsMor (dp0 R) (spMap (RingHom.id R)) κ (spMap π) (RingHom.id R) (spMap π)) :
    Function.Bijective m.pull1 ∧ Function.Bijective m.pull2 := by
  obtain ⟨a⟩ := nonempty_isInitial hκ hπ hI
  obtain ⟨b⟩ := nonempty_isInitial (isDPNilpotent_bot R) (π := RingHom.id R) Function.surjective_id
    ((RingHom.injective_iff_ker_eq_bot _).1 Function.injective_id)
  exact ⟨⟨fun x y _ ↦ (H1.eq_zero_of_isInitial _ b x).trans (H1.eq_zero_of_isInitial _ b y).symm,
      fun y ↦ ⟨0, (map_zero _).trans (H1.eq_zero_of_isInitial _ a y).symm⟩⟩,
    ⟨fun x y _ ↦ (h2_eq_zero_of_isInitial _ b x).trans (h2_eq_zero_of_isInitial _ b y).symm,
      fun y ↦ ⟨0, (map_zero _).trans (h2_eq_zero_of_isInitial _ a y).symm⟩⟩⟩

theorem trivial_case {X : Scheme.{0}} (s : X ⟶ Sp R) (m : IsMor (dp0 R) s (dp0 R) s (RingHom.id R) (𝟙 X)) :
    Function.Bijective m.pull1 ∧ Function.Bijective m.pull2 :=
  ⟨by rw [show (m.pull1 : _ → _) = id from funext m.pullCohomologyOne_id]; exact Function.bijective_id,
    by rw [show (m.pull2 : _ → _) = id from funext m.pullCohomologyTwo_id]; exact Function.bijective_id⟩

theorem elliptic_crystal (H : CrystallineDeRham) (R : Type) [CommRing R] (W : WeierstrassCurve (DualNumber R))
    [W.IsElliptic] : ∃ (i : _) (m : IsMor (dp0 _) (WeierstrassCurve.ellPolAV W).A.hom (epsDP R)
      ((WeierstrassCurve.ellPolAV (W.map (TrivSqZeroExt.fstHom R R R).toRingHom)).A.hom ≫
        spMap (TrivSqZeroExt.fstHom R R R).toRingHom) (RingHom.id _) i),
      Function.Bijective m.pull1 ∧ Function.Bijective m.pull2 := by
  have h := GlobalTheory.WeierstrassCurve.isGrpPullback_ellPolAV W (TrivSqZeroExt.fstHom R R R).toRingHom rfl
  have := (WeierstrassCurve.ellPolAV W).isAb.smooth
  have := (WeierstrassCurve.ellPolAV W).isAb.proper
  exact ⟨_, IsMor.of_dividedPowersZeroIdeal _ (by rw [Cris.spMap_id, Category.comp_id]; exact h.1.w),
    H _ _ _ (isDPNilpotent_squareZero _) R _ (fun r ↦ ⟨TrivSqZeroExt.inl r, rfl⟩) rfl _ _ _ _ _ inferInstance inferInstance
      inferInstance h.1 _⟩

end Crystal

end GlobalTheory.Published.AbelianDualCrystal.Test
