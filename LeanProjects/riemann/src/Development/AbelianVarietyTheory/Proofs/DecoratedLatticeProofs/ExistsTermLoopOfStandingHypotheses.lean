import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CollSBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopEvaluationThresholdZero
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DegenerateConstant
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyStatementOfItemsFourSeven
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.SBridge
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DiscreteSeriesDegreeBound
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.FamilyStatementOfAbsAndVandermonde
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.GammaRangeOfSizeHypotheses
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.DiagSmall
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FinrankLeRankOnAdd
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ToGlob0
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ExpQuarterMulExpQuarterLeTwo
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BesselFormsTrivialNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.AutomorphicFormsFiniteUnitaryIff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Formalism.PeriodIntegrals.BesselMapUniq
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CorankOneIsEquivalenceOnRow
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DiagCLC
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FinXClosed
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.StepLocGenPinnedGP
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqNml
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.StepAnalyticConstantsP
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataChoiceLeaves
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AmpUnifPOf
import Formalism.SharpRestriction.CuspSpanNormBounds.WeightedUniformRotatedOfExpansion
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ThmBChain
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopRowSB
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBCovN
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBTheta
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.IsLowUnitHBaseVector
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BesselOfWPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocFactorAll
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RMeasExAll
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeUnipotentIntegralNormalisedHaarStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalBesselJFactorAllWordsOfGapStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselMultiplicityOneLargeGapAndWhittakerBessel
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoefWeightedLocUncond
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InstFactDecLow
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabiliserCovolumeRelevantTermLeHeightPowStatement
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Core.Deg.exists_termLoop_of_standingHypotheses : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (u : D.what₂.Word) (C' Cl Cg cb Cu cT CT : ℝ), 29 ≤ C' → 72 ≤ Cl → Ties D → StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT → ConcTie X Y → ∃ (W : WittDat X) (H : TieHyp W hI) (Am : AmpDat X) (hV : PvalForm W hI Am) (Z : LoopTie D large₂ (termTieOf W hI H Am hV) u u 1), TieAt hF hI large₂ u (termTieOf W hI H Am hV) Z ∧ ∀ t, Z.volR t = Formalism.L2.SG.LoopTerm.volRC hI t := by
  intro D large₂ X Y hF hI u C' Cl Cg cb Cu cT CT hC' hCl hT hS hCT
  haveI : Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow := ⟨GlobalTheory.DecTransport.decLow_main⟩
  haveI : Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc := ⟨GlobalTheory.Sloc.CoefWeighted.coefWeightedLoc_uncond⟩
  have hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D := Formalism.L2.SG.ThmSOwn.gap_hypothesis_of_hypotheses hS (by linarith) hC'
  have hWD : Formalism.L2.SG.WuDecay.WuDecay X := hCT.2.2.2.2.1
  haveI : Nonempty D.what₂.Word := ⟨u⟩
  obtain ⟨C⟩ := Formalism.L2.SG.Pf.choiceExists X 1 one_pos
  have hB : Formalism.L2.SG.LocWSOf.WuBessel C := Formalism.L2.SG.Pf.wuBesselOfLoc_all C hG GlobalTheory.uniqGap_and_besselOfW.2
    (Formalism.L2.SG.Pf.LocF.locFactor_holds hG C) (fun τ => Formalism.L2.SG.Pf.dsTr C τ) (fun τ => Formalism.L2.SG.Pf.haarTr C τ)
    (fun w τ => Formalism.L2.SG.Pf.colsTypeTr C w τ)
  have hW : ∀ τ, GoodW D τ u u 1 (Formalism.L2.SG.LocWSOf.locW C u u τ) := fun τ =>
    Formalism.L2.SG.LocWSOf.goodW_of C u u τ (Formalism.L2.SG.Pf.colsTypeTr C u τ) (Formalism.L2.SG.Pf.colsTypeTr C u τ)
      (Formalism.L2.SG.Pf.zTr C u τ) (Formalism.L2.SG.Pf.zTr C u τ) (Formalism.L2.SG.Pf.haarTr C τ)
  have hSS : ∀ τ, GoodS D (lamD D τ) (Formalism.L2.SG.LocWSOf.locS hB u u τ) := fun τ =>
    Formalism.L2.SG.LocWSOf.goodS_of hB u u τ (Formalism.L2.SG.Pf.goodSRest_all hG hT.dsig_tie hB u u τ)
  have hwin : normWin D large₂ 1 1 := Formalism.L2.SG.Pf.LoopBTheta.normWin_one large₂ zero_le_one
  have hCF : Formalism.L2.SG.Pf.LoopBCovN.CovNFormula := GlobalTheory.T.covolume_unipotentIntegral_normalisedHaar
  have hup : Formalism.L2.SG.Pf.LoopBCovN.eN D * Real.log (2 * D.host.v) ≤
      1 * (D.R.m : ℝ) ^ 2 * Real.log large₂.sc.b := by
    have h2v : 2 * D.host.v = D.host.rdE := by unfold Formalism.BasicNotions.Host.v; ring
    have hrd : Real.log D.host.rdE ≤ large₂.sc.L / Cl := hS.2.2.2.2.2.2.2.2.2.2.1
    have hv0 : 0 ≤ Real.log (2 * D.host.v) := Real.log_nonneg (Formalism.L2.SG.Pf.LoopBCovN.rdE_ge_one D)
    have he := Formalism.L2.SG.Pf.LoopBCovN.eN_le D
    have he0 : 0 ≤ Formalism.L2.SG.Pf.LoopBCovN.eN D := by unfold Formalism.L2.SG.Pf.LoopBCovN.eN; positivity
    rw [Formalism.MainNotions.S.log_scb large₂, h2v]
    rw [h2v] at hv0
    have hCl0 : (0 : ℝ) < Cl := by linarith
    have hL0 : 0 ≤ large₂.sc.L := by
      by_contra hneg
      push_neg at hneg
      have : large₂.sc.L / Cl < 0 := div_neg_of_neg_of_pos hneg hCl0
      linarith
    have h72 : large₂.sc.L / Cl ≤ large₂.sc.L / 72 := div_le_div_of_nonneg_left hL0 (by norm_num) hCl
    have hm0 : 0 ≤ (D.R.m : ℝ) ^ 2 := sq_nonneg _
    calc Formalism.L2.SG.Pf.LoopBCovN.eN D * Real.log D.host.rdE ≤ ((D.R.m : ℝ) ^ 2 / 2) * (large₂.sc.L / 72) :=
          mul_le_mul he (hrd.trans h72) hv0 (by positivity)
      _ ≤ 1 * (D.R.m : ℝ) ^ 2 * large₂.sc.L := by nlinarith
  have hFE := Formalism.L2.SG.LoopsFinal.frameEqvInj_of (Formalism.L2.SG.LoopsTies.wOf X) hI (Formalism.L2.SG.LoopsTies.hOf X Y hF hI)
    (Formalism.L2.SG.LoopsTies.aOfW X Y hF hI hWD) (Formalism.L2.SG.LoopsTies.hvOfW X Y hF hI hWD)
    (Formalism.L2.SG.Pf.LoopBFrame.frameChangeC_holds _ _ _ hF hI _) u u
  have hti := Formalism.L2.SG.LoopsTies.tiesAt X Y hF hI hWD u u
  refine ⟨Formalism.L2.SG.LoopsTies.wOf X, Formalism.L2.SG.LoopsTies.hOf X Y hF hI, Formalism.L2.SG.LoopsTies.aOfW X Y hF hI hWD,
    Formalism.L2.SG.LoopsTies.hvOfW X Y hF hI hWD,
    Formalism.L2.SG.LoopTieOf.loopTieOfParts
      (Formalism.L2.SG.LoopTieOf.loopRowsOf (Formalism.L2.SG.LoopsTies.wOf X) hI (Formalism.L2.SG.LoopsTies.hOf X Y hF hI)
        (Formalism.L2.SG.LoopsTies.aOfW X Y hF hI hWD) (Formalism.L2.SG.LoopsTies.hvOfW X Y hF hI hWD)
        (Formalism.L2.SG.Pf.WittFlags.RowRepsIso_holds D) u u hFE)
      (Formalism.L2.SG.LoopTerm.locB large₂ 1 C hB u u hwin hW hSS)
      (Formalism.L2.SG.LoopTerm.loopTermOfN (Formalism.L2.SG.LoopsTies.wOf X) hI (Formalism.L2.SG.LoopsTies.hOf X Y hF hI)
        (Formalism.L2.SG.LoopsTies.aOfW X Y hF hI hWD) (Formalism.L2.SG.LoopsTies.hvOfW X Y hF hI hWD) large₂ 1 C hB u u hwin hW hSS
        (GlobalTheory.RMeasAll.rMeasEx_all D X Y hF hI C u u hW)
        (Formalism.L2.SG.Pf.LoopBPin.pinAll_holds u u) (Formalism.L2.SG.Pf.LoopBPin.covolPos_holds u u)
        (GlobalTheory.T.localBesselJFactor_all_words_of_gap D X Y hF hI C hB u u hG)
        (Formalism.L2.SG.Pf.LoopBCovN.covN_pos hCF one_pos C u u)
        (Formalism.L2.SG.Pf.LoopBCovN.covWinN_of hCF C large₂ zero_le_one hup u u) hwin), ?_, fun t => rfl⟩
  exact ⟨Formalism.L2.SG.LoopsFinal.jtPin_of _ hI _ _ _ (Formalism.L2.SG.Pf.FibreCounting.AmpFibreConst_holds Y),
    Formalism.L2.SG.Pf.WittFlags.WRowPin_holds hF hI _ _ _ _,
    Formalism.L2.SG.Pf.FibreCounting.FibreCount_holds Y,
    Formalism.MainNotions.BridgeLemma₂.rows_TermPtsTie_of _ (Formalism.MainNotions.BridgeLemma₂.rows_rdE_pos D) hti.1,
    hti.2.1, hti.2.2, fun t t' hL hE => hFE t t' hL hE⟩

namespace GlobalTheory.Core.Deg

theorem tieOn_singleton_uncond : ∀ c : ℝ, TieOn {c} := by
  intro c Cg cb Cu cT CT
  obtain ⟨C, hCv⟩ := GlobalTheory.T.stabiliserCovolume_relevantTerm_le_heightPow Cg cb Cu cT CT c 1
  refine ⟨C, 72, ?_⟩
  intro C0 hC0 C' Cl hC' hCl D large₂ X Y hF hI u hT hH hCT
  have hC0' : C0 = c := hC0
  subst hC0'
  obtain ⟨W, H, Am, hV, Z, hTie, hvol⟩ :=
    exists_termLoop_of_standingHypotheses D large₂ X Y hF hI u C' Cl Cg cb Cu cT CT (by linarith) hCl hT hH.1 hCT
  refine ⟨_, Z, hTie, ?_⟩
  intro hHyp t hG hr
  rw [hvol t]
  exact hCv D X Y hF hI W H Am hV large₂ u u C' Cl (by linarith) hHyp t hG hr

end GlobalTheory.Core.Deg
