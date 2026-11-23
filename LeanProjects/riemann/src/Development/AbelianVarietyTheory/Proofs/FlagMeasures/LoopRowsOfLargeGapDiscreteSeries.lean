import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLandSt
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TheoremSRecursion
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypFam
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.RowsDef
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopRowSF
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopLocPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.GapClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LoopRowBoundsAlongFamilyLargeGapsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabiliserCovolumeRelevantTermLeHeightPowStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeUnipotentIntegralNormalisedHaar
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalBesselJFactorAllWordsOfGapStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RMeasExAll
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoefWeightedLocUncond
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermRepUnram

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.ThmSOwn

noncomputable section

namespace GlobalTheory.LoopRowsCloseGap

section PartB

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.LoopLoc

variable {D : D7}

variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in

theorem wuBessel_ofW {X : HidaSetting D} {θ : ℝ} (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D)
    (hBW : Formalism.L2.SG.LocWSOf.BesselOfW) (C : Choice X θ) : WuBessel C :=
  Formalism.L2.SG.Pf.wuBesselOfLoc_all C hG hBW
    (Formalism.L2.SG.Pf.LocF.locFactor_holds hG C) (fun τ => Formalism.L2.SG.Pf.dsTr C τ) (fun τ => Formalism.L2.SG.Pf.haarTr C τ)
    (fun u τ => Formalism.L2.SG.Pf.colsTypeTr C u τ)

variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] in

def loopLocDatOfW (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) (hT : Formalism.BasicNotions.dsigTie D)
    (hBW : Formalism.L2.SG.LocWSOf.BesselOfW) {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) {large₂ : SizeData₂ D} {C1 : ℝ}
    (hwin : normWin D large₂ C1 θ) (u u' : D.what₂.Word) : Formalism.L2.SG.LoopTieOf.LoopLocDat D large₂ u u' C1 where
  θ := θ
  θ_win := hwin
  W τ := locW C u u' τ
  goodW τ := goodW_of C u u' τ (Formalism.L2.SG.Pf.colsTypeTr C u τ) (Formalism.L2.SG.Pf.colsTypeTr C u' τ)
    (Formalism.L2.SG.Pf.zTr C u τ) (Formalism.L2.SG.Pf.zTr C u' τ) (Formalism.L2.SG.Pf.haarTr C τ)
  A τ := locS (wuBessel_ofW hG hBW C) u u' τ
  goodS τ := goodS_of (wuBessel_ofW hG hBW C) u u' τ
    (Formalism.L2.SG.Pf.goodSRest_all hG hT (wuBessel_ofW hG hBW C) u u' τ)
  deg_eq τ := deg_eq (wuBessel_ofW hG hBW C) u u' τ

end PartB

section Sel

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf Formalism.L2.SG.LoopsFinal Formalism.FourierDecayAlt
  Formalism.L2.SG.ThmSOwn Formalism.L2.SG.LoopsTies Formalism.L2.SG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {𝒞 : FamClass} (sel : SSel 𝒞)

variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] in

def BGW (hBW : Formalism.L2.SG.LocWSOf.BesselOfW) (C1f : List ℝ → ℝ) (hC1 : ∀ l, 0 ≤ C1f l) :
    ∀ {eps : ℝ} (Fm : FamP eps) (hc : CG 𝒞 Fm) x (_ : (Fm.raise (yR (selG sel) yFG Fm hc)).x1 < x) (i : Fm.Ix x)
      (u u' : (Fm.D x i).what₂.Word), LoopLocDat (Fm.D x i) (Fm.L x i) u u' (C1f Fm.cOut) :=
  fun Fm hc x hx i u u' => loopLocDatOfW
    (gap_of hc (hyR (selG sel) yFG hx) i) (Fm.ties x i).dsig_tie hBW
    (CX ((selG sel Fm hc).2 x (raise_lt hx) (h0R (selG sel) yFG hx) i).X u)
    (Formalism.L2.SG.Pf.LoopBTheta.normWin_one (Fm.L x i) (hC1 _)) u u'

variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in

def MGW (hFX : Formalism.L2.SG.PoincareAmplitudeLowerBounds.FinXC) (hWu : Formalism.L2.SG.Pf.WuDecayOfGap) (hBW : Formalism.L2.SG.LocWSOf.BesselOfW)
    (hRM : RMeasExAll) (hJF : JFactNAll) (hCF : Formalism.L2.SG.Pf.LoopBCovN.CovNFormula) :
    ∀ {eps : ℝ} (Fm : FamP eps) (hc : CG 𝒞 Fm) x (hx : (Fm.raise (yR (selG sel) yFG Fm hc)).x1 < x) (i : Fm.Ix x)
      (u u' : (Fm.D x i).what₂.Word),
      LoopTermDat (Fm.D x i) (Fm.L x i) (AtR (selG sel) yFG (hyFG sel hFX hWu) Fm hc x hx i) u u' ((fun _ => 1) Fm.cOut)
        (BGW sel hBW (fun _ => 1) (fun _ => zero_le_one) Fm hc x hx i u u') :=
  fun Fm hc x hx i u u' =>
    LoopTerm.loopTermOfN (wOf ((selG sel Fm hc).2 x (raise_lt hx) (h0R (selG sel) yFG hx) i).X)
      (((selG sel Fm hc).2 x (raise_lt hx) (h0R (selG sel) yFG hx) i).hI
        (hyFG sel hFX hWu Fm hc x (raise_lt hx) (h0R (selG sel) yFG hx) (hyR (selG sel) yFG hx) i).1)
      (hOf _ _ _ _) (aOfW _ _ _ _ (hyFG sel hFX hWu Fm hc x (raise_lt hx) (h0R (selG sel) yFG hx) (hyR (selG sel) yFG hx) i).2)
      (hvOfW _ _ _ _ (hyFG sel hFX hWu Fm hc x (raise_lt hx) (h0R (selG sel) yFG hx) (hyR (selG sel) yFG hx) i).2)
      (Fm.L x i) 1 (CX ((selG sel Fm hc).2 x (raise_lt hx) (h0R (selG sel) yFG hx) i).X u)
      (wuBessel_ofW (gap_of hc (hyR (selG sel) yFG hx) i) hBW _) u u'
      (Formalism.L2.SG.Pf.LoopBTheta.normWin_one (Fm.L x i) zero_le_one)
      (BGW sel hBW (fun _ => 1) (fun _ => zero_le_one) Fm hc x hx i u u').goodW
      (BGW sel hBW (fun _ => 1) (fun _ => zero_le_one) Fm hc x hx i u u').goodS
      (hRM _ _ _ _ _ _ u u' (BGW sel hBW (fun _ => 1) (fun _ => zero_le_one) Fm hc x hx i u u').goodW)
      (Formalism.L2.SG.Pf.LoopBPin.pinAll_holds u u') (Formalism.L2.SG.Pf.LoopBPin.covolPos_holds u u')
      (hJF _ _ _ _ _ _ _ u u' (gap_of hc (hyR (selG sel) yFG hx) i))
      (Formalism.L2.SG.Pf.LoopBCovN.covN_pos hCF one_pos _ u u')
      (Formalism.L2.SG.Pf.LoopBCovN.covWinN_sizes hCF _ (Fm.L x i) (Fm.sizes x (raise_lt hx) i) (by norm_num) u u')
      (Formalism.L2.SG.Pf.LoopBTheta.normWin_one (Fm.L x i) zero_le_one)

end Sel

open Formalism.L2.SG.LoopsTies

theorem sC'_mem_cLast {eps : ℝ} (Fm : FamP eps) : sC' Fm ∈ Fm.cLast := by
  unfold FamP.cLast sC'; simp

theorem le_sCl_of {eps : ℝ} (Fm : FamP eps) {t : ℝ} (h : ∀ c ∈ Fm.cLast, t ≤ c) : t ≤ sCl Fm := by
  unfold sCl
  refine le_min (h _ (by unfold FamP.cLast; simp)) (le_min (h _ (by unfold FamP.cLast; simp))
    (le_min (h _ (by unfold FamP.cLast; simp)) (le_min (h _ (by unfold FamP.cLast; simp))
      (le_min (h _ (by unfold FamP.cLast; simp)) (h _ (by unfold FamP.cLast; simp))))))

theorem loop_rows_closed_gap : GlobalTheory.GapIn.Hyp → Formalism.L2.SG.LocWSOf.BesselOfW → BpJoin.ThmBpDS →
    Formalism.L2.SG.Pf.WuDecayOfGap → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (𝒞 : FamClass) (sel : SSel 𝒞),
    (∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → TuSize Fm) →
    (Closed 𝒞 fun Fm _ => PX.RanksF Fm 3 (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu) → LoopRowS 3 𝒞 sel := by
  intro hH hBW hBp hWu hRF 𝒞 sel hT hRk
  have hGap := Formalism.L2.SG.GapClosed.gapEv_closed_of 𝒞 hT
  haveI : Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram := ⟨GlobalTheory.hermRepUnram⟩
  haveI : Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc := ⟨GlobalTheory.Sloc.CoefWeighted.coefWeightedLoc_uncond⟩
  haveI : Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow := ⟨hH.1.1.1⟩
  haveI : Fact Formalism.FourierDecayAlt.ThreeDimData.DecInf := ⟨hH.1.1.2.1⟩
  have hFX : Formalism.L2.SG.PoincareAmplitudeLowerBounds.FinXC := Formalism.L2.SG.Pf.finXC_of hWu hRF
  have hRM : RMeasExAll := GlobalTheory.RMeasAll.rMeasEx_all
  have hJF : JFactNAll := GlobalTheory.T.localBesselJFactor_all_words_of_gap
  have hCF : Formalism.L2.SG.Pf.LoopBCovN.CovNFormula := GlobalTheory.CovNFormulaPf.main
  choose C₀F thrF hR using GlobalTheory.T.loopRowBounds_along_family_largeGaps Formalism.HermitianLattices.Ext.L3.siegelMassRatio hH hBp
  choose cVF hcV using GlobalTheory.T.stabiliserCovolume_relevantTerm_le_heightPow
  have hForm : Closed 𝒞 fun Fm _ => OwnEv Fm fun C' Cl x i =>
      Cnt.Hyp0 (Fm.D x i) (Fm.L x i) C' Cl (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3 →
        ∀ u, UnitaryVolumeMass.FormAt (Fm.D x i) u := by
    obtain ⟨e, he, H⟩ := hRk
    refine ⟨e, he, fun eps h1 h2 => ?_⟩
    obtain ⟨K, hK⟩ := H eps h1 h2
    let K4 : Formalism.MainNotions.TransportedAlt := ⟨0, fun _ => 0, fun _ => 0,
      fun l => thrF (l.getD 6 0 + 1) (1 / 4) 3 (1 / 2) (l.getD 13 0) 3 0 1 0 (l.getD 17 0)⟩
    refine ⟨K.sup K4, fun Fm CH hc hL => ?_⟩
    obtain ⟨hL1, hL4⟩ := (Fm.large_sup _ _ CH).1 hL
    have hthr : ∀ c ∈ Fm.cLast, thrF (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3 0 1 0 Fm.CGam ≤ c := by
      intro c hc0
      have h := hL4.2.2.2 c hc0
      simp only [K4] at h
      rwa [constant_list_cylinder, constant_list_trace, constant_list_gamma] at h
    exact (hR _ _ _ _ _ _ _ _ _ _ eps Fm rfl (hthr _ (sC'_mem_cLast Fm)) (le_sCl_of Fm hthr)
      (hK Fm CH hc hL1)).1
  refine loopRowS_of_sub sel 3 hGap ?_
  let C₀f : (List ℝ → ℝ) → List ℝ → ℝ := fun aF l =>
    C₀F (l.getD 6 0 + 1) (1 / 4) 3 (1 / 2) (l.getD 13 0) 3 (aF (l.take 16)) 1
      (cVF (l.getD 6 0 + 1) (1 / 4) 3 (1 / 2) (l.getD 13 0) 3 (aF (l.take 16))) (l.getD 17 0)
  refine loopRowS_of_raised 3 (selG sel) yFG (hyFG sel hFX hWu) (fun _ => 1) C₀f
    (YtR (selG sel) yFG (hyFG sel hFX hWu) (fun _ => 1) (BGW sel hBW (fun _ => 1) (fun _ => zero_le_one))
      (MGW sel hFX hWu hBW hRM hJF hCF)) ?_ (closed_sub (fun _ h => h.1) hForm)
  intro aF
  obtain ⟨e, he, H⟩ := closed_sub (𝒞' := CG 𝒞) (fun _ h => h.1) hRk
  refine ⟨e, he, fun eps h1 h2 => ?_⟩
  obtain ⟨K, hK⟩ := H eps h1 h2
  let K4 : Formalism.MainNotions.TransportedAlt := ⟨0, fun _ => 0, fun _ => 0, fun l =>
    max (thrF (l.getD 6 0 + 1) (1 / 4) 3 (1 / 2) (l.getD 13 0) 3 (aF (l.take 16)) 1
      (cVF (l.getD 6 0 + 1) (1 / 4) 3 (1 / 2) (l.getD 13 0) 3 (aF (l.take 16))) (l.getD 17 0)) 1⟩
  refine ⟨K.sup K4, fun Fm CH hc hL hc' C hC => ?_⟩
  obtain ⟨hL1, hL4⟩ := (Fm.large_sup _ _ CH).1 hL
  have hthr : ∀ c ∈ Fm.cLast, max (thrF (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3 (aF Fm.cOut) 1
      (cVF (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3 (aF Fm.cOut)) Fm.CGam) 1 ≤ c := by
    intro c hc0
    have h := hL4.2.2.2 c hc0
    simp only [K4] at h
    rwa [constant_list_cylinder, constant_list_trace, cOut_take, constant_list_gamma] at h
  have hC' : C₀F (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3 (aF Fm.cOut) 1
      (cVF (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3 (aF Fm.cOut)) Fm.CGam ≤ C := by
    simp only [C₀f] at hC
    rwa [constant_list_cylinder, constant_list_trace, cOut_take, constant_list_gamma] at hC
  have hCl1 : 1 ≤ sCl Fm := le_sCl_of Fm fun c hc => (le_max_right _ _).trans (hthr c hc)
  refine (hR (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3 (aF Fm.cOut) 1
      (cVF (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3 (aF Fm.cOut)) Fm.CGam eps
      (Fm.raise (yR (selG sel) yFG Fm hc')) rfl
      ((le_max_left _ _).trans (hthr _ (sC'_mem_cLast Fm)))
      (le_sCl_of Fm fun c hc => (le_max_left _ _).trans (hthr c hc)) (hK Fm CH hc hL1)).2
    (AtR (selG sel) yFG (hyFG sel hFX hWu) Fm hc')
    (YtR (selG sel) yFG (hyFG sel hFX hWu) (fun _ => 1) (BGW sel hBW (fun _ => 1) (fun _ => zero_le_one))
      (MGW sel hFX hWu hBW hRM hJF hCF) Fm hc')
    (tiesR (selG sel) yFG (hyFG sel hFX hWu) (fun _ => 1) (BGW sel hBW (fun _ => 1) (fun _ => zero_le_one))
      (MGW sel hFX hWu hBW hRM hJF hCF) Fm hc').1
    (tiesR (selG sel) yFG (hyFG sel hFX hWu) (fun _ => 1) (BGW sel hBW (fun _ => 1) (fun _ => zero_le_one))
      (MGW sel hFX hWu hBW hRM hJF hCF) Fm hc').2
    (fun x i => _root_.beta_l_unique (Fm.D x i)) ?_ C hC'
  refine ⟨0, fun x _ i hx u u' hH t hG hr => ?_⟩
  exact hcV (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3 (aF Fm.cOut) (Fm.D x i)
    ((selG sel Fm hc').2 x (raise_lt hx) (h0R (selG sel) yFG hx) i).X
    ((selG sel Fm hc').2 x (raise_lt hx) (h0R (selG sel) yFG hx) i).Y
    (hyFG sel hFX hWu Fm hc' x (raise_lt hx) (h0R (selG sel) yFG hx) (hyR (selG sel) yFG hx) i).1
    (((selG sel Fm hc').2 x (raise_lt hx) (h0R (selG sel) yFG hx) i).hI
      (hyFG sel hFX hWu Fm hc' x (raise_lt hx) (h0R (selG sel) yFG hx) (hyR (selG sel) yFG hx) i).1)
    (wOf ((selG sel Fm hc').2 x (raise_lt hx) (h0R (selG sel) yFG hx) i).X)
    (hOf _ _ _ _)
    (aOfW _ _ _ _ (hyFG sel hFX hWu Fm hc' x (raise_lt hx) (h0R (selG sel) yFG hx) (hyR (selG sel) yFG hx) i).2)
    (hvOfW _ _ _ _ (hyFG sel hFX hWu Fm hc' x (raise_lt hx) (h0R (selG sel) yFG hx) (hyR (selG sel) yFG hx) i).2)
    (Fm.L x i) u u' _ _ hCl1 hH t hG hr

end GlobalTheory.LoopRowsCloseGap

end
