import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.BlowupAmpleMinusExceptionalStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.DivisorAgreementOnIsomorphismStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.EffectiveMultipleDominatesStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsAmpleTensorAmplePowProjective
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArithmeticNefModelOfAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModificationLineBundleGlobalSectionsDimPullEq
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.AmpleUpstairs

open GlobalTheory.Cartier.CartierDiv in

theorem supp_neg_le {X : Scheme.{0}} [IsIntegral X] (D : GlobalTheory.Cartier.CartierDiv X) : (-D).supp ≤ D.supp := by
  intro x hx
  obtain ⟨g, hg⟩ := D.exists_isEqn x
  rw [hg.neg.mem_supp_iff] at hx
  rw [hg.mem_supp_iff]
  intro hu
  apply hx
  rw [Units.val_inv_eq_inv_val]
  exact hu.inv

open GlobalTheory.Cartier.CartierDiv in

theorem supp_nsmul_le {X : Scheme.{0}} [IsIntegral X] (D : GlobalTheory.Cartier.CartierDiv X) (m : ℕ) :
    (m • D).supp ≤ D.supp := by
  intro x hx
  obtain ⟨g, hg⟩ := D.exists_isEqn x
  rw [(hg.nsmul m).mem_supp_iff] at hx
  rw [hg.mem_supp_iff]
  intro hu
  apply hx
  rw [Units.val_pow_eq_pow_val]
  have key : ∀ j : ℕ, UnitAt x ((g : X.functionField) ^ j) := by
    intro j
    induction j with
    | zero => simpa using unitAt_one x
    | succ j ih => rw [pow_succ]; exact ih.mul hu
  exact key m

end GlobalTheory.AmpleUpstairs

namespace GlobalTheory

open GlobalTheory.AmpleUpstairs in

theorem exists_ample_pull_sub_eff : ∀ (k : Type) [Field k] [CharZero k] (Y₀ Y₁ : Scheme.{0}) [IsIntegral Y₀] [IsIntegral Y₁] [IsLocallyNoetherian Y₀] [IsLocallyNoetherian Y₁] (q : Y₀ ⟶ Sp k) (n : ℕ) (t : Y₁ ⟶ Y₀) [IsDominant t] [SmoothOfRelativeDimension n q] [SmoothOfRelativeDimension n (t ≫ q)], IsProjOver q → IsProjOver (t ≫ q) → ∀ I : Y₀.IdealSheafData, IsIso (t ∣_ I.support.compl) → FinalTheorems.EffCartier (I.comap t) → ∀ (A : LB Y₀) (hA : IsAmpleLB A), ∃ (c : ℕ) (E : CartierDiv Y₁) (A₁ : LB Y₁) (hA₁ : IsAmpleLB A₁), 0 < c ∧ E.Eff ∧ E.supp ≤ (I.comap t).support ∧ c • CechPic.pull t (cls A hA.isLB) = cls A₁ hA₁.isLB + toPic E := by
  intro k _ _ Y₀ Y₁ _ _ _ _ q n t _ _ _ hq ht I hiso hI A hA
  obtain ⟨-, L₁, hL₁⟩ := isProper_and_exists_isAmpleLB_of_isProjOver ht
  haveI : CompactSpace Y₁ := hL₁.compactSpace
  haveI : CompactSpace Y₀ := hA.compactSpace
  haveI : IsNoetherian Y₀ := {}
  haveI : Smooth (t ≫ q) := SmoothOfRelativeDimension.smooth n _
  haveI : GlobalTheory.IsNormalScheme Y₁ := GlobalTheory.ModifSections.isNormalScheme_of_smooth (t ≫ q)
  obtain ⟨H, hH⟩ := toPic_surjective (cls L₁ hL₁.isLB)
  obtain ⟨H₀, hH₀⟩ := GlobalTheory.T.divisor_agreement_on_isomorphism k Y₀ Y₁ q n t ht I.support.compl hiso H
  obtain ⟨E₀, hE₀, hsE₀, hgen⟩ := GlobalTheory.T.blowup_ample_minus_exceptional Y₀ Y₁ t I hI A hA
  have hD : (H - pullCart t H₀).supp ≤ E₀.supp := by
    intro y hy
    rw [hsE₀, Scheme.IdealSheafData.support_comap]
    by_contra h
    exact hH₀ y h hy
  obtain ⟨e, he⟩ := GlobalTheory.T.effective_multiple_dominates Y₁ (H - pullCart t H₀) E₀ hE₀ hD
  obtain ⟨c₁, hc₁, hc₁'⟩ :=
    ((hA.eventually_isGenerated_tens_lbPow (isLB_toLB (-H₀))).and (eventually_ge_atTop 1)).exists
  obtain ⟨c₂, hc₂⟩ := hgen.exists
  obtain ⟨P, hP, hPc⟩ := cls_surj (c₂ • CechPic.pull t (cls A hA.isLB) - toPic E₀)
  have gP := hc₂ P hP hPc
  have g₁ := hc₁.pull t
  have gM := AmpleModelPos.isGenerated_tens g₁ (gP.pow e)
  have hA₁L := isLB_tens hL₁.isLB gM.isLB
  have hA₁ : IsAmpleLB (tens L₁ (tens ((tens (toLB (-H₀)) (lbPow A c₁)).pull t) (lbPow P e))) := by
    refine hL₁.tensor_isGenerated gM hA₁L ((cls_eq_zero_iff (LB.isLB_div (LB.isLB_div hA₁L hL₁.isLB) gM.isLB)).1 ?_)
    rw [cls_div (LB.isLB_div hA₁L hL₁.isLB) gM.isLB, cls_div hA₁L hL₁.isLB, cls_tens hL₁.isLB gM.isLB]
    abel
  refine ⟨c₁ + e * c₂, e • E₀ - (H - pullCart t H₀), _, hA₁, by omega, he, ?_, ?_⟩
  · rw [sub_eq_add_neg]
    refine (GlobalTheory.Cartier.CartierDiv.supp_add_le _ _).trans (sup_le ((supp_nsmul_le _ _).trans hsE₀.le) ?_)
    exact (supp_neg_le _).trans (hD.trans hsE₀.le)
  · rw [cls_tens hL₁.isLB gM.isLB, cls_tens g₁.isLB (gP.pow e).isLB,
      cls_lbPow hP e, hPc, cls_pull (isLB_tens (isLB_toLB (-H₀)) (isLB_lbPow hA.isLB c₁)) t,
      cls_tens (isLB_toLB (-H₀)) (isLB_lbPow hA.isLB c₁), cls_lbPow hA.isLB c₁, ← toPic_apply,
      map_sub, map_nsmul, map_sub, toPic_pullCart, hH, map_add, map_neg, map_nsmul, add_smul, mul_smul]
    simp only [map_neg, smul_sub]
    abel

end GlobalTheory
