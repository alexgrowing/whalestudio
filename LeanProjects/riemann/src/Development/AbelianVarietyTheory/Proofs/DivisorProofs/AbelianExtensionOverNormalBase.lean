import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobPullHomExtAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NearIsIsoOfIsProperOfFinitePresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDualOfIsPerfectOfAdditive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDualOfIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.DeRham GlobalTheory.DeRhamSheaf GlobalTheory.AbDual GlobalTheory.Cris GlobalTheory.AbDatum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.SelfDualSpread

section General

variable {S S' : Scheme.{0}}

theorem pull_evc_gen {A B : Over S} {A' B' : Over S'} {f : A'.left ⟶ A.left} {g : B'.left ⟶ B.left}
    {m : (A' ⊗ A').left ⟶ (A ⊗ A).left} {m' : (A' ⊗ B').left ⟶ (A ⊗ B).left}
    (m₁ : m' ≫ (fst A B).left = (fst A' B').left ≫ f) (m₂ : m' ≫ (snd A B).left = (snd A' B').left ≫ g)
    {Q : LB (A ⊗ B).left} (hQ : Q.IsLB) (hQ' : (Q.pull m').IsLB)
    (a b : A ⊗ A ⟶ A) (a' b' : A' ⊗ A' ⟶ A') (y : A ⟶ B) (y' : A' ⟶ B')
    (ha : m ≫ a.left = a'.left ≫ f) (hb : m ≫ b.left = b'.left ≫ f) (ey : f ≫ y.left = y'.left ≫ g) :
    CechPic.pull m (evc hQ a (b ≫ y)) = evc hQ' a' (b' ≫ y') := by
  rw [evc, evc, CechPic.cls_pull hQ, ← CechPic.pull_comp, ← CechPic.pull_comp]
  congr 2
  apply left_ext
  · rw [Category.assoc, Category.assoc, lift_left_fst, m₁, lift_left_fst_assoc, ha]
  · rw [Category.assoc, Category.assoc, lift_left_snd, m₂, lift_left_snd_assoc, Over.comp_left, Over.comp_left,
      ← Category.assoc, hb, Category.assoc, Category.assoc, ey]

end General

theorem exists_generic_iso (hD : GlobalTheory.Published.DualAbelianScheme) {K : Type} [Field K] (Q : Out.PolAV (Sp K))
    (hΛ : (abelian₂ Q.A Q.L).IsLB) {D : Over (Sp K)} [GrpObj D] {R : LB (Q.A ⊗ D).left} (hR : IsDual Q.A D R)
    (hR' : IsAdditive (swap R)) :
    ∃ x : Q.A ⟶ D, IsMonHom x ∧ IsIso x ∧ CechPic.cls (abelian₂ Q.A Q.L) hΛ = evc hR.isLB (fst Q.A Q.A) (snd Q.A Q.A ≫ x) := by
  have := Q.isAb.comm
  have e : ∀ (Y : Over (Sp K)) (a b : Y ⟶ Q.A), evc hΛ a b = CechPic.lam (CechPic.cls Q.L Q.isLB) a b := fun Y a b ↦ by
    rw [evc, show CechPic.cls _ hΛ = CechPic.lam (CechPic.cls Q.L Q.isLB) (fst Q.A Q.A) (snd Q.A Q.A) from
      CechPic.cls_cube_two Q.isLB _ _ hΛ, CechPic.pull_lam, lift_fst, lift_snd]
  have hd : IsDual Q.A Q.A (abelian₂ Q.A Q.L) := PerfectDual.isDual_of_isPerfect hD Q.A Q.A Q.isAb Q.isAb Q.smoothDim
    Q.smoothDim (isPerfect_lam Q.isLB Q.ktriv)
  have a₂ : IsAdditive (swap (abelian₂ Q.A Q.L)) := (BirigidLift.isAdditive_swap_iff hΛ).2 fun Y a b b' ↦ by
    rw [e, e, e, CechPic.lam_comm, CechPic.lam_comm _ a b, CechPic.lam_comm _ a b', ← e, ← e, ← e]
    exact (isAdditive_iff hΛ).1 hd.additive _ _ _ _
  obtain ⟨x, hx, ex⟩ := BirigidLift.exists_hom hR hR' hΛ hd.additive a₂
  exact ⟨x, hx, hd.isIso_of_cls hR ex, ex⟩

section Generic

variable {S : Scheme.{0}} [IsIntegral S] [AlgebraicGeometry.IsNoetherian S] {K : Type} [Field K] {η : Sp K ⟶ S}
  {A B : Over S} [GrpObj A] [GrpObj B] {A' B' : Over (Sp K)} [GrpObj A'] [GrpObj B'] {φ : A'.left ⟶ A.left}
  {ψ : B'.left ⟶ B.left}

omit [IsIntegral S] [AlgebraicGeometry.IsNoetherian S] in

theorem exists_res (hφ : IsGrpPullback A' A η φ) (hψ : IsGrpPullback B' B η ψ) (y : A ⟶ B) :
    ∃ y' : A' ⟶ B', φ ≫ y.left = y'.left ≫ ψ :=
  ⟨Over.homMk (hψ.1.lift (φ ≫ y.left) A'.hom (by rw [Category.assoc, Over.w y, hφ.1.w])) (hψ.1.lift_snd _ _ _),
    (hψ.1.lift_fst _ _ _).symm⟩

theorem lbIso_of_generic (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) (hη : IsGenericPointHom η)
    (hφ : IsGrpPullback A' A η φ) (hψ : IsGrpPullback B' B η ψ) {R : LB (A ⊗ B).left} (hR : IsDual A B R)
    {m' : (A' ⊗ B').left ⟶ (A ⊗ B).left} (m₁ : m' ≫ (fst A B).left = (fst A' B').left ≫ φ)
    (m₂ : m' ≫ (snd A B).left = (snd A' B').left ≫ ψ) (hR' : IsDual A' B' (R.pull m'))
    {m : (A' ⊗ A').left ⟶ (A ⊗ A).left} (l₁ : m ≫ (fst A A).left = (fst A' A').left ≫ φ)
    (l₂ : m ≫ (snd A A).left = (snd A' A').left ≫ φ) {M₁ M₂ : LB (A ⊗ A).left} (h₁ : M₁.IsLB) (h₂ : M₂.IsLB)
    (a₁ : IsAdditive M₁) (a₂ : IsAdditive M₂)
    (e : CechPic.pull m (CechPic.cls M₁ h₁) = CechPic.pull m (CechPic.cls M₂ h₂)) : LBIso M₁ M₂ := by
  obtain ⟨y₁, hy₁, -⟩ := hR.univ A M₁ h₁ a₁
  obtain ⟨y₂, hy₂, -⟩ := hR.univ A M₂ h₂ a₂
  have c₁ : CechPic.cls M₁ h₁ = evc hR.isLB (fst A A) (snd A A ≫ y₁) :=
    (CechPic.cls_eq_iff h₁ (pull_isLB hR.isLB _)).2 hy₁
  have c₂ : CechPic.cls M₂ h₂ = evc hR.isLB (fst A A) (snd A A ≫ y₂) :=
    (CechPic.cls_eq_iff h₂ (pull_isLB hR.isLB _)).2 hy₂
  obtain ⟨y₁', e₁⟩ := exists_res hφ hψ y₁
  obtain ⟨y₂', e₂⟩ := exists_res hφ hψ y₂
  have k := fun (y : A ⟶ B) (y' : A' ⟶ B') (ey : φ ≫ y.left = y'.left ≫ ψ) ↦
    pull_evc_gen m₁ m₂ hR.isLB hR'.isLB (fst A A) (snd A A) (fst A' A') (snd A' A') y y' l₁ l₂ ey
  have e' : y₁' = y₂' := BirigidLift.dual_ext hR' (by rw [← k _ _ e₁, ← k _ _ e₂, ← c₁, ← c₂, e])
  obtain ⟨_, _⟩ := hη.quasiCompact_and_dominant
  have := hA.smooth
  have := hB.proper
  have ey : y₁ = y₂ := ExtUnique.over_hom_ext_of_isPullback hφ.1 (by rw [e₁, e₂, e'])
  subst ey
  exact (CechPic.cls_eq_iff h₁ h₂).1 (c₁.trans c₂.symm)

end Generic

theorem exists_selfDual : GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.SemiAbelianHomExtension → ∀ (O : Type) [CommRing O] (c : O →+* O)
    (S : Scheme.{0}) [IsIntegral S] [AlgebraicGeometry.IsNoetherian S], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S →
    ∀ (K : Type) [Field K] (η : Sp K ⟶ S), GlobalTheory.IsGenericPointHom η →
    ∀ (A : Over S) [GrpObj A] (i : OAct O A), IsAbelianScheme A →
    ∀ (Q : Out.PolAV (Sp K)) (j : OAct O Q.A) (φ : Q.A.left ⟶ A.left), GlobalTheory.CurveRootGeometry.IsActPull j i η φ →
      GlobalTheory.CurveRootGeometry.IsRosati c Q j →
    ∃ P : LB (A ⊗ A).left, IsSelfDual c i P ∧ ∀ m : (Q.A ⊗ Q.A).left ⟶ (A ⊗ A).left,
      m ≫ (fst A A).left = (fst Q.A Q.A).left ≫ φ → m ≫ (snd A A).left = (snd Q.A Q.A).left ≫ φ →
      LBIso (P.pull m) (abelian₂ Q.A Q.L) := by
  intro hD hE O _ c S _ _ hS K _ η hη A _ i hA Q j φ hact hros
  obtain ⟨hφ, hj⟩ := hact
  have := Q.isAb.comm
  obtain ⟨B, _, R, hB, -, hR, hRs⟩ := hD S A hA
  have hψ := isGrpPullback_pullback B η
  obtain ⟨m', m₁, m₂⟩ := exists_prod_pullback hφ hψ
  have hR' : (R.pull m').IsLB := pull_isLB hR.isLB m'
  have dR' := hR.baseChange hφ hψ m₁ m₂ hR' ((CechPic.cls_eq_iff hR' hR').1 rfl)
  have aR' := (BirigidLift.additive_pull hφ hψ m₁ m₂ hR.isLB hR' ((CechPic.cls_eq_iff hR' hR').1 rfl)
    hR.additive hRs.additive).2
  have hΛ : (abelian₂ Q.A Q.L).IsLB := (isPerfect_lam Q.isLB Q.ktriv).isLB
  obtain ⟨x, hx, ix, ex⟩ := exists_generic_iso hD Q hΛ dR' aR'
  have : IsMonHom (asIso x).hom := hx
  obtain ⟨E, ⟨hE₁, hE₂⟩, -⟩ := hE.generic_existsUnique_iso_of_isGrpPullback hS hη
    (isSemiAbelian_of_isAbelianScheme A hA) (isSemiAbelian_of_isAbelianScheme B hB) hφ hψ (asIso x)
  replace hE₂ : φ ≫ E.hom.left = x.left ≫ pullback.fst B.hom η := hE₂.symm
  have hP : (ev R (fst A A) (snd A A ≫ E.hom)).IsLB := pull_isLB hR.isLB _
  obtain ⟨a₁, a₂⟩ := BirigidLift.additive_ev hR.isLB hR.additive hRs.additive E.hom
  have eΛ : ∀ (Y : Over (Sp K)) (a b : Y ⟶ Q.A), evc hΛ a b = CechPic.lam (CechPic.cls Q.L Q.isLB) a b :=
    fun Y a b ↦ by
      rw [evc, show CechPic.cls _ hΛ = CechPic.lam (CechPic.cls Q.L Q.isLB) (fst Q.A Q.A) (snd Q.A Q.A) from
        CechPic.cls_cube_two Q.isLB _ _ hΛ, CechPic.pull_lam, lift_fst, lift_snd]

  have key : ∀ (m : (Q.A ⊗ Q.A).left ⟶ (A ⊗ A).left) (a b : A ⊗ A ⟶ A) (a' b' : Q.A ⊗ Q.A ⟶ Q.A),
      m ≫ a.left = a'.left ≫ φ → m ≫ b.left = b'.left ≫ φ →
      CechPic.pull m (evc hP a b) = CechPic.lam (CechPic.cls Q.L Q.isLB) a' b' := fun m a b a' b' ha hb ↦ by
    rw [BirigidLift.evc_of_cls hR.isLB hP rfl, pull_evc_gen m₁ m₂ hR.isLB hR' a b a' b' E.hom x ha hb hE₂, ← eΛ,
      BirigidLift.evc_of_cls hR' hΛ ex]
  have c₀ : CechPic.cls _ hP = evc hP (fst A A) (snd A A) := by
    rw [evc, lift_fst_snd, Over.id_left, CechPic.pull_id]
  obtain ⟨m, l₁, l₂⟩ := exists_prod_pullback hφ hφ
  refine ⟨ev R (fst A A) (snd A A ≫ E.hom), ⟨isDual_of_iso S A A B _ R hR hP E.hom inferInstance hE₁
    ((CechPic.cls_eq_iff hP hP).1 rfl), ?_, fun a ↦ ?_⟩, fun n n₁ n₂ ↦ ?_⟩
  · refine lbIso_of_generic hA hB hη hφ hψ hR m₁ m₂ dR' l₁ l₂ (pull_isLB hP _) hP a₂ a₁ ?_
    rw [c₀, cls_ev hP, key m _ _ _ _ l₂ l₁, key m _ _ _ _ l₁ l₂, CechPic.lam_comm]
  · have := i.hom a
    have hM₁ := pull_isLB hP (lift (fst A A ≫ i.act a) (snd A A)).left
    have hM₂ := pull_isLB hP (lift (fst A A) (snd A A ≫ i.act (c a))).left
    refine lbIso_of_generic hA hB hη hφ hψ hR m₁ m₂ dR' l₁ l₂ hM₁ hM₂
      ((isAdditive_iff hM₁).2 fun Y u u' t ↦ ?_) ((isAdditive_iff hM₂).2 fun Y u u' t ↦ ?_) ?_
    · rw [evc_ev hP, evc_ev hP, evc_ev hP]
      simp only [lift_fst_assoc, lift_snd, MonObj.mul_comp]
      exact (isAdditive_iff hP).1 a₁ _ _ _ _
    · rw [evc_ev hP, evc_ev hP, evc_ev hP]
      simp only [lift_snd_assoc, lift_fst]
      exact (isAdditive_iff hP).1 a₁ _ _ _ _
    · rw [cls_ev hP, cls_ev hP, key m _ _ (fst Q.A Q.A ≫ j.act a) _ (by
          rw [Over.comp_left, Over.comp_left, ← Category.assoc, l₁, Category.assoc, Category.assoc, hj]) l₂,
        key m _ _ _ (snd Q.A Q.A ≫ j.act (c a)) l₁ (by
          rw [Over.comp_left, Over.comp_left, ← Category.assoc, l₂, Category.assoc, Category.assoc, hj])]
      exact EndOnTorsion.lam_rosati Q (hros a) _ _
  · refine (CechPic.cls_eq_iff (pull_isLB hP n) hΛ).1 ?_
    rw [CechPic.cls_pull hP, c₀, key n _ _ _ _ n₁ n₂]
    exact (CechPic.cls_cube_two Q.isLB _ _ hΛ).symm

end GlobalTheory.SelfDualSpread
