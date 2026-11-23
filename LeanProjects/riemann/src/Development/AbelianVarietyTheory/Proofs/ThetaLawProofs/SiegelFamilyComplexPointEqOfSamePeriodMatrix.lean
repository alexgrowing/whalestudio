import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsoOfSamePeriodMatrixLevelStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrePullbackPrincipalRingChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymplecticFormBasisChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.SiegelPointUnique
open GlobalTheory.SiegelPullComp

def TriplePB {J : Type} {S S' : Scheme.{0}} (A' : Over S') [GrpObj A'] (P' : LB (A' ⊗ A').left)
    (lev' : J → (𝟙_ (Over S') ⟶ A')) (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left)
    (lev : J → (𝟙_ (Over S) ⟶ A)) (f : S' ⟶ S) : Prop :=
  ∃ (φ : A'.left ⟶ A.left) (φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left),
    IsGrpPullback A' A f φ ∧ IsSquare φ φ₂ ∧ LBIso P' (P.pull φ₂) ∧
      ∀ a, (lev' a).left ≫ φ = f ≫ (lev a).left

variable {J : Type} {S S' S'' : Scheme.{0}} {A : Over S} [GrpObj A] {P : LB (A ⊗ A).left}
  {lev : J → (𝟙_ (Over S) ⟶ A)} {A' : Over S'} [GrpObj A'] {P' : LB (A' ⊗ A').left}
  {lev' : J → (𝟙_ (Over S') ⟶ A')} {A'' : Over S''} [GrpObj A''] {P'' : LB (A'' ⊗ A'').left}
  {lev'' : J → (𝟙_ (Over S'') ⟶ A'')} {f : S' ⟶ S} {f' : S'' ⟶ S'}

theorem TriplePB.comp (hP : P.IsLB) (hP' : P'.IsLB) (hP'' : P''.IsLB) (m : TriplePB A' P' lev' A P lev f)
    (m' : TriplePB A'' P'' lev'' A' P' lev' f') : TriplePB A'' P'' lev'' A P lev (f' ≫ f) := by
  obtain ⟨φ, φ₂, hφ, hs, hw, hl⟩ := m
  obtain ⟨ψ, ψ₂, hψ, hs', hw', hl'⟩ := m'
  refine ⟨ψ ≫ φ, ψ₂ ≫ φ₂, hψ.comp hφ, ⟨?_, ?_⟩, ?_, fun a => ?_⟩
  · rw [Category.assoc, hs.1, ← Category.assoc, hs'.1, Category.assoc]
  · rw [Category.assoc, hs.2, ← Category.assoc, hs'.2, Category.assoc]
  · exact (hw'.trans hP'' (pull_isLB hP' _) (pull_isLB (pull_isLB hP _) _) (iso_pull ψ₂ hw)).trans
      hP'' (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) (iso_pull_pull hP φ₂ ψ₂)
  · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ) (hl' a)).trans ((Category.assoc _ _ _).trans
      ((congrArg (f' ≫ ·) (hl a)).trans (Category.assoc _ _ _).symm)))

theorem TriplePB.cancel (hP : P.IsLB) (hP' : P'.IsLB) (hP'' : P''.IsLB) (m : TriplePB A' P' lev' A P lev f)
    (n : TriplePB A'' P'' lev'' A P lev (f' ≫ f)) : TriplePB A'' P'' lev'' A' P' lev' f' := by
  obtain ⟨φ, φ₂, hφ, hs, hw, hl⟩ := m
  obtain ⟨χ, χ₂, hχ, hs', hw', hl'⟩ := n
  have hp := hφ.1
  let F : A''.left ⟶ A'.left := hp.lift χ (A''.hom ≫ f') (by rw [hχ.1.w, Category.assoc])
  have hF : F ≫ φ = χ := hp.lift_fst _ _ _
  have hFw : F ≫ A'.hom = A''.hom ≫ f' := hp.lift_snd _ _ _
  let U : Over.mk ((A'' ⊗ A'').hom ≫ f') ⟶ A' ⊗ A' :=
    lift (pushPt hFw (fst A'' A'')) (pushPt hFw (snd A'' A''))
  let F₂ : (A'' ⊗ A'').left ⟶ (A' ⊗ A').left := U.left
  have h₁ : F₂ ≫ (fst A' A').left = (fst A'' A'').left ≫ F :=
    congrArg (fun q => q.left) (lift_fst (pushPt hFw (fst A'' A'')) (pushPt hFw (snd A'' A'')))
  have h₂ : F₂ ≫ (snd A' A').left = (snd A'' A'').left ≫ F :=
    congrArg (fun q => q.left) (lift_snd (pushPt hFw (fst A'' A'')) (pushPt hFw (snd A'' A'')))
  have h₃ : F₂ ≫ φ₂ = χ₂ := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst A A).left = _ ≫ (fst A A).left
      rw [Category.assoc, hs.1, ← Category.assoc, h₁, Category.assoc, hF, hs'.1]
    · show (_ ≫ _) ≫ (snd A A).left = _ ≫ (snd A A).left
      rw [Category.assoc, hs.2, ← Category.assoc, h₂, Category.assoc, hF, hs'.2]
  refine ⟨F, F₂, hφ.cancel (by rw [hF]; exact hχ) hFw, ⟨h₁, h₂⟩, ?_, fun a => ?_⟩
  · rw [← h₃] at hw'
    exact (hw'.trans hP'' (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _)
      (iso_pull_pull hP φ₂ F₂).symm).trans hP'' (pull_isLB (pull_isLB hP _) _) (pull_isLB hP' _)
      (iso_pull F₂ hw).symm
  · apply hp.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hF).trans ((hl' a).trans ((Category.assoc _ _ _).trans
        ((congrArg (f' ≫ ·) (hl a).symm).trans (Category.assoc _ _ _).symm))))
    · have a₁ : (lev'' a).left ≫ A''.hom = 𝟙 S'' := Over.w (lev'' a)
      have a₂ : (lev' a).left ≫ A'.hom = 𝟙 S' := Over.w (lev' a)
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hFw).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ f') a₁).trans ((Category.id_comp _).trans ((Category.comp_id _).symm.trans
          ((congrArg (f' ≫ ·) a₂.symm).trans (Category.assoc _ _ _).symm))))))

theorem eq_of_ptAt : Out.Laws → ThetaUnifAV → ∀ (h k : ℕ) (K : Type) [Field K] (ζ : K) (σ : K →+* ℂ) (F : SFam h k ζ), 1 ≤ h → 3 ≤ k → Odd k → σ ζ = Complex.exp (-(2 * Real.pi * Complex.I) / k) → ∀ (τ : Matrix (Fin h) (Fin h) ℂ) (p q : Sp ℂ ⟶ F.X), p ≫ F.s = spMap σ → q ≫ F.s = spMap σ → PtAt F.univ p τ → PtAt F.univ q τ → p = q := by
  intro hL hU h k K _ ζ σ F _ _ _ _ τ p q hp hq ⟨P, lev, φ, hper, ⟨hφ, _, φ₂, hs, hw⟩, hl⟩
    ⟨P', lev', φ', hper', ⟨hφ', _, φ₂', hs', hw'⟩, hl'⟩
  obtain ⟨c, hc⟩ := (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange h k K K ζ ζ (RingHom.id K) _ _ F.s (p ≫ F.s) p rfl
    (by rw [show spMap (RingHom.id K) = 𝟙 (Sp K) from Spec.map_id _, Category.comp_id])).1 F.univ
  obtain ⟨e, he, ⟨e₂, hes, hew⟩, hel⟩ := GlobalTheory.T.exists_iso_of_same_periodMatrix_level hL hU h k τ P' P lev' lev hper' hper
  have l : (abelian₂ P.A P.L).IsLB := LB.isLB_linComb P.isLB _ _
  have l' : (abelian₂ P'.A P'.L).IsLB := LB.isLB_linComb P'.isLB _ _
  have m : TriplePB P.A (abelian₂ P.A P.L) lev F.univ.A F.univ.P F.univ.lev p := ⟨φ, φ₂, hφ, hs, hw, hl⟩
  have m' : TriplePB P'.A (abelian₂ P'.A P'.L) lev' F.univ.A F.univ.P F.univ.lev q := ⟨φ', φ₂', hφ', hs', hw', hl'⟩
  have n : TriplePB c.A c.P c.lev F.univ.A F.univ.P F.univ.lev (𝟙 _ ≫ p) := by
    rw [Category.id_comp]; exact hc
  have i : TriplePB P.A (abelian₂ P.A P.L) lev P'.A (abelian₂ P'.A P'.L) lev' (𝟙 _) :=
    ⟨e.hom.left, e₂, Geo.Tor.isGrpPullback_of_iso e, hes, hew, fun a =>
      (congrArg (fun t => t.left) (hel a)).trans (Category.id_comp _).symm⟩
  have r := m'.comp F.univ.isLB l' c.isLB (i.comp l' l c.isLB (m.cancel F.univ.isLB l c.isLB n))
  rw [Category.id_comp, Category.id_comp] at r
  exact F.inj ℂ p q _ c (hp.trans hq.symm) hc r

end GlobalTheory.SiegelPointUnique
end
