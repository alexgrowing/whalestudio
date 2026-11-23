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
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HypOfUniqGap
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselMultiplicityOneLargeGapAndWhittakerBessel
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneBesselTorusTranslatesLargeGap
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselPointwiseBoundAtLargeGaps
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeEqBesselFunctionLargeGaps
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesCoefPointwiseBoundUnconditional
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ElementarySizeBoundsOfSizeHypotheses
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormSqLeadMinorTurnP
import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceExpansion
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.StandardHypothesesOfScaleHyp
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg

theorem ptWide_at_record_gap : ∀ Cg cb Cu cT CT C0 : ℝ, ∃ C : ℝ, ∀ Cn : ℝ, ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), thr ≤ C' → thr ≤ Cl → Ties D → Formalism.L2.SG.RowsConc.TFrameAt D → VanishingOnXAndXPlusBranching.adm1 D large₂ C' Cl Cg cb Cu cT CT C0 Cn 1 C := by
  intro Cg cb Cu cT CT C0
  have hDB : GlobalTheory.GapIn.Hyp := GlobalTheory.GapIn.hyp_of_uniqGap GlobalTheory.uniqGap_and_besselOfW.1
  have hBp : BpJoin.ThmBpDS := GlobalTheory.discreteSeriesCoef_pointwiseBound
  obtain ⟨Cgf, hOB⟩ := GlobalTheory.AmpTKGapOne.oneBesselTor_of_gapHyp hDB
  obtain ⟨Cf, hCf, hFrm⟩ := GlobalTheory.FrameTurn.frameChange_of_frames 1 Cgf 2 zero_le_one (by norm_num)
  obtain ⟨Cb, Cg₀, hB⟩ := GlobalTheory.bp_forms_of_gapIn_thmBpDS hDB hBp 1
  obtain ⟨Ca, hCa, hAmp⟩ := GlobalTheory.AmpBesselGap.ampIsBessel hDB Cg cb Cu cT CT C0 1
  refine ⟨max (Ca + max (max 2 Cu) (max CT (1 / 8 + 2 * Cg)) * (Cf + max Cb 0 + Cf * max Cb 0)) (max Cb 0),
    fun Cn => ?_⟩
  obtain ⟨m₀, hm₀⟩ := hAmp Cn
  obtain ⟨Cs₀, hCs₀⟩ := hFrm Cn
  obtain ⟨thr, hthr⟩ := GlobalTheory.Core.Deg.elementary_size_bounds_of_size_hypotheses (max m₀ (max (128 * |max Cg₀ Cs₀|) (200 * |Cn|)))
  refine ⟨thr, fun D large₂ C' Cl hC' hCl hTies hTF => ?_⟩
  intro hH
  obtain ⟨h1000, -, hM, -, hrd, -⟩ := hthr D large₂ C' Cl Cg cb Cu cT CT hC' hCl hH.1
  have hβ2 : (2 : ℝ) ≤ max (max 2 Cu) (max CT (1 / 8 + 2 * Cg)) := le_trans (le_max_left _ _) (le_max_left _ _)
  have hStd : Bridge.StdOfHyp D large₂ C' Cl Cg cb Cu cT CT C0 1 (max Cg₀ Cs₀) (200 * |Cn|)
      (max (max 2 Cu) (max CT (1 / 8 + 2 * Cg))) :=
    stdOfHyp_rec D large₂ C' Cl Cg cb Cu cT CT C0 1 (max Cg₀ Cs₀) (200 * |Cn|) _ (by linarith) zero_le_one hβ2
      (le_trans (le_max_right _ _) (le_max_left _ _))
      (by rw [mul_one]; exact le_trans (le_max_left _ _) (le_max_right _ _))
      (by rw [mul_one]; exact le_trans (le_max_right _ _) (le_max_right _ _))
      (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hM)
      (by
        rw [abs_of_nonneg (by positivity)]
        exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hM)
  have h47 : OnePlaceEstimates.UniformityTheoremBPrime D 1 Cn (max Cg₀ Cs₀) (200 * |Cn|) (max Cb 0) :=
    OnePlaceEstimates.upper_bound_mono_constant D zero_lt_one (le_max_left _ _)
      ((hB (max Cg₀ Cs₀) (le_max_left _ _)).2.2 D Cn (200 * |Cn|)
        (mul_le_mul_of_nonneg_left (le_abs_self Cn) (by norm_num)))
  have hFr : Bridge.FrameChange D 1 (max Cg₀ Cs₀) Cn Cf :=
    hCs₀ (max Cg₀ Cs₀) (le_max_right _ _) D (Formalism.MainNotions.OnePlaceExpansion.frame_bound_of_bessel_torus D Cgf 2 le_rfl (hOB D))
  exact AuxiliaryNormPrimes.plancherelBoundOneParameter_of_uniformity D large₂ C' Cl Cg cb Cu cT CT C0 Cn 1 Ca 1 Cf (max Cg₀ Cs₀) (200 * |Cn|) _ (max Cb 0) _
    (hm₀ D large₂ C' Cl h1000 hrd (le_trans (le_max_left _ _) hM) hTies.cdScale_tie) hFr hStd (fun _ => hTF) h47
    (by linarith) (le_max_right _ _) hCa hCf (le_max_left _ _) (le_max_right _ _) hH

end GlobalTheory.Core.Deg
