import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModModT
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedInnerProductDataDefiniteBottomLargeGri
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdEulerFactorOfRamified
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveHeckeLFunctionInvOfTrivialOnMaxReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaDivBetaRamifiedAtLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialHeckeLFunctionSquareEqPrimitive
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

noncomputable section

namespace GlobalTheory.NuOffPair

theorem main : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → D.host.F = maximalRealSubfield D.host.E →
  ∀ (G : GridData L sc) (t : T) (i j : Fin D.R.m) (χ : (AE D)ˣ →* Circle), ChrEq χ (nuH G t i j) →
    GlobalTheory.LFun.UnrOff χ ((sfB G t : Finset (FinPl D)) : Set (FinPl D)) ∧
    ∀ Λ : ℂ → ℂ, GlobalTheory.CMVal.IsHeckeL (nuH G t i j) Λ → ∀ s : ℂ,
      GlobalTheory.Cont.HolValueAt (GlobalTheory.LFun.charL χ⁻¹ ((sfB G t : Finset (FinPl D)) : Set (FinPl D))) s (Λ s) := by
  intro D T L sc μ₀ hL hF G t i j χ hχ
  classical
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have hm : 1 ≤ D.R.m - (i : ℕ) ∧ D.R.m - (i : ℕ) ≤ D.R.m := ⟨by omega, by omega⟩
  have hunr : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∉ sfB G t → (nuH G t i j).UnrAt w := by
    intro w hw
    have hv : w.under (𝓞 D.host.F) ∉ G.pl.S0 := fun h => hw (GlobalTheory.BottomIPData.mem_bottomPairFinitePlacesBelow_of_mem_exceptional G t h)
    have hQ : ∀ P ∈ L.Q t, P.under (𝓞 D.host.F) ≠ w.under (𝓞 D.host.F) := fun P hP e =>
      hw (e ▸ GlobalTheory.BottomIPData.under_mem_sfB G t (by unfold locPl; exact Finset.mem_union_right _ hP))
    have hchi : (G.ch.chiH (D.R.m - i)).UnrAt w := G.ch.unr _ hm.1 hm.2 w hv
    have hmu : (L.C.mu0 j).UnrAt w := (L.C.isMu0 j).unr _ fun k hk => hv (by
      have h : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (w.under (𝓞 D.host.F)).asIdeal := by
        show algebraMap _ (𝓞 D.host.E) _ ∈ w.asIdeal
        rw [map_natCast]; exact hk
      refine G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 ?_))
      fin_cases k
      · exact Or.inl h
      · exact Or.inr (Or.inl h))
    have hxi : (L.xiH t).UnrAt w := by
      by_contra hn
      rcases (hL.Q_ram t w).1 hn with hq | ⟨P', hq, hc⟩
      · exact hQ w hq rfl
      · exact hQ P' hq (GlobalTheory.BotTripleUnr.under_eq_of_isConjPl hc)
    rw [nuH, div_eq_mul_inv]
    exact (hmu.mul hxi).mul hchi.inv
  have hram : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∈ sfB G t → ¬ (nuH G t i j).UnrAt w := by
    intro w hw
    by_cases h0 : w.under (𝓞 D.host.F) ∈ G.pl.S0
    · exact GlobalTheory.SqStep.nuH_not_unrAt_above hL G t i j w h0
    · unfold GlobalTheory.BottomIPData.sfB at hw
      obtain ⟨P, hP, hPw⟩ := Finset.mem_image.1 hw
      have hP' : P ∈ L.Q t := by
        unfold locPl GlobalTheory.ChiGrid.Places.W0 at hP
        rcases Finset.mem_union.1 hP with h | h
        · exfalso
          obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
          apply h0
          rw [← hPw, G.pl.under_w hv]
          exact hv
        · exact h
      have := GlobalTheory.TwistRam.not_unrAt_alpha_div_beta hL t i j w P hP' hPw h0
      have e0 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j = G.nu t i (j + 1) :=
        mul_div_mul_right_eq_div _ _ _
      rwa [e0, GlobalTheory.LFun.unrAt_iff_of_chrEq (GlobalTheory.FunObj.SqNum.chrEq_nu G t i j hL)] at this
  refine ⟨fun w hw => (GlobalTheory.LFun.unrAt_iff_of_chrEq hχ w).2 (hunr w ?_), fun Λ hΛ s => ?_⟩
  · exact hw
  have hT : GlobalTheory.CMVal.TrivOnF (nuH G t i j) := by
    have h := ((L.C.isMu0 j).triv.mul (hL.xi_triv t)).mul (G.ch.triv _ hm.1 hm.2).inv
    rw [nuH, div_eq_mul_inv]
    exact h
  have hu : ∀ w, GlobalTheory.LFun.UnrAt χ⁻¹ w ↔ (nuH G t i j)⁻¹.UnrAt w := fun w => by
    rw [GlobalTheory.UnrCharZeta.unrAt_inv, ← GlobalTheory.LFun.unrAt_iff_of_chrEq hχ w]
    exact ⟨fun h => inv_inv χ ▸ h.inv, fun h => h.inv⟩
  have hfam : GlobalTheory.LFun.charFam χ⁻¹ = GlobalTheory.LFun.heckeFam (nuH G t i j)⁻¹ := funext fun w => by
    by_cases h : (nuH G t i j)⁻¹.UnrAt w
    · rw [GlobalTheory.LFun.heckeFam_of_unrAt h, GlobalTheory.LFun.charFam, if_pos ((hu w).2 h), GlobalTheory.LFun.val_inv,
        GlobalTheory.LFun.val_eq_of_chrEq hχ, GlobalTheory.UnrCharZeta.val_inv]
    · rw [GlobalTheory.LFun.heckeFam_of_not_unrAt h, GlobalTheory.LFun.charFam, if_neg (mt (hu w).1 h)]
  have hΛ' := GlobalTheory.CMVal.isHeckeL_inv_of_trivOnF D.host.E (nuH G t i j) Λ hT hΛ
  have hr' : ∀ w ∈ GlobalTheory.LFun.above D.host.E ((sfB G t : Finset (FinPl D)) : Set (FinPl D)),
      ¬ (nuH G t i j)⁻¹.UnrAt w := fun w hw h =>
    hram w hw ((GlobalTheory.UnrCharZeta.unrAt_inv _ w).1 h)
  have heq : GlobalTheory.Cont.EqRight Λ (GlobalTheory.LFun.charL χ⁻¹ ((sfB G t : Finset (FinPl D)) : Set (FinPl D))) := ⟨1, fun z hz => by
    change Λ z = GlobalTheory.LFun.eulerProd _ (GlobalTheory.LFun.charFam χ⁻¹) z
    rw [hfam]
    exact (GlobalTheory.SqStep.heckeL_eq_of_ram hr' hΛ' hz).symm⟩
  exact (GlobalTheory.Cont.holValueAt_self (σ := s.re - 1) (fun z _ => hΛ.1.analyticAt z) (by linarith)).congr heq

end GlobalTheory.NuOffPair
