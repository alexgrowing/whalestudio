import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGrpPullbackOfLoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleDivIffIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullInvSymmIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.SymDiv

theorem exists_ampleDiv_symm : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsIntegral A.left], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → RelAmple A L → ∃ D : CartierDiv A.left, AmpleDiv D ∧ LBIso ((toLB D).pull (GrpObj.inv : A ⟶ A).left) (toLB D) := by
  intro R _ A _ _ hA L hL hamp
  classical
  have hprop : IsProper A.hom := hA.proper
  set σ := (GrpObj.inv : A ⟶ A).left with hσ
  have hii : (GrpObj.inv : A ⟶ A) ≫ (GrpObj.inv : A ⟶ A) = 𝟙 A := by
    have h := IsIso.hom_inv_id (GrpObj.inv : A ⟶ A)
    rwa [GrpObj.inv_inv] at h
  have hii' : σ ≫ σ = 𝟙 A.left := by
    rw [hσ, ← Over.comp_left, hii, Over.id_left]
  have : IsIso σ := ⟨⟨σ, hii', hii'⟩⟩
  set L' := LB.LinComb L (K := Fin 2) ![𝟙 A.left, σ] ![1, 1] with hL'def
  have hL' : L'.IsLB := LB.isLB_linComb hL (K := Fin 2) ![𝟙 A.left, σ] ![1, 1]
  have hamL : IsAmpleLB L := (relAmple_iff_isAmpleLB_of_isAffine A hL).1 hamp
  have hamσ : IsAmpleLB (L.pull σ) := hamL.pull_of_isAffineHom σ
  have hamL' : IsAmpleLB L' := by
    refine hamL.tensor hamσ hL' ?_
    have hM := pull_isLB hL σ
    have hD1 := LB.isLB_div hL' hL
    have hD2 := LB.isLB_div hD1 hM
    refine (CechPic.cls_eq_zero_iff hD2).1 ?_
    rw [CechPic.cls_div hD1 hM, CechPic.cls_div hL' hL, CechPic.cls_linComb hL _ _ hL', CechPic.cls_pull hL σ hM]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_zsmul,
      CechPic.pull_id]
    abel
  have : CompactSpace A.left := hamL'.compactSpace
  obtain ⟨i₀, h₀⟩ := exists_chart hL' (genericPoint A.left)
  refine ⟨ofLB hL' i₀ h₀, ?_, ?_⟩
  · have e : LBIso L' (toLB (ofLB hL' i₀ h₀)) := (presents_ofLB hL' i₀ h₀).lbIso (presents_toLB _)
    have hT := isLB_toLB (ofLB hL' i₀ h₀)
    exact (ampleDiv_iff_isAmpleLB _ _).2 (hamL'.of_lbIso hT e.symm)
  · have e : LBIso L' (toLB (ofLB hL' i₀ h₀)) := (presents_ofLB hL' i₀ h₀).lbIso (presents_toLB _)
    have hT := isLB_toLB (ofLB hL' i₀ h₀)
    have hs : LBIso (L'.pull σ) L' := GlobalTheory.SymLB.pull_inv_symm_iso _ A L hL
    have e₁ : LBIso ((toLB (ofLB hL' i₀ h₀)).pull σ) (L'.pull σ) := GlobalTheory.FamRep.lbIso_pull e.symm σ
    exact LBIso.trans (pull_isLB hT σ) hL' hT (LBIso.trans (pull_isLB hT σ) (pull_isLB hL' σ) hL' e₁ hs) e

end GlobalTheory.SymDiv
