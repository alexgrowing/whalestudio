import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.SBridge
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceExpansion
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.StandardHypothesesOfScaleHyp
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.MinkowskiDividesFactorialOfBound
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyCriticalLevelLowerBound
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CriticalLevelLowOfRefined
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.DegreeRatioFormulaStatement
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyFormalDegreeLowerBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypFam
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeEqBesselFunctionLargeGapsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneBesselTorusTranslatesLargeGapStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselPointwiseBoundAtLargeGapsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormSqLeadMinorTurnP
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SizesLargeOfPowerBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

open MeasureTheory NumberField Formalism.FourierDecayAlt Finset

namespace GlobalTheory.UnifPTGap

open Formalism.MainNotions.BridgeLemma

theorem tFrame_of_dsig (hM : Formalism.HermitianLatticesTheory.SiegelMassRatio) (hDs : Formalism.L2.SG.Pf.SzHypFD.DsigHC)
    {eps : ℝ} (Fm : FamP eps) (h40 : 40 ≤ sCl Fm) {C0 Cg cb Cu cT CT : ℝ}
    (hR : PX.RanksF Fm C0 Cg cb Cu cT CT) : PX.TFrame Fm Cg cb Cu cT CT C0 := by
  haveI : Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC := ⟨hDs⟩
  exact level_frame_of_sizes Fm Cg cb Cu cT CT C0 1 (by linarith)
    (level_formula_family Fm C0 Cg cb Cu cT CT (fun x i => mass_ratio_of_siegel_cm_unramified hM (Fm.D x i)) (mass_two_bound_family_holds Fm) hR)
    (Formalism.L2.SG.Pf.SzHypFam.localSplitExponents_of_forty_le_sCl Fm h40 C0 Cg cb Cu cT CT)

theorem uniformPT_gap : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS →
    ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ C thr : ℝ, ∀ (eps : ℝ) (Fm : FamP eps),
    thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → ∀ Cn, (OwnEv Fm fun C' Cl x i =>
      VanishingOnXAndXPlusBranching.adm1 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 C) := by
  intro hM hH hBp Cg cb Cu cT CT C0 C1
  set Cβ : ℝ := max 2 (max Cu (max CT (1 / 8 + 2 * Cg))) with hCβ
  have hβ2 : 2 ≤ Cβ := le_max_left _ _
  have hu : Cu ≤ Cβ := (le_max_left _ _).trans (le_max_right _ _)
  have hT : CT ≤ Cβ * 1 := by rw [mul_one]; exact ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hg : 1 / 8 + 2 * Cg ≤ Cβ * 1 := by
    rw [mul_one]; exact ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  obtain ⟨Cb, Cg₀, hBP⟩ := (GlobalTheory.T.besselPointwiseBound_at_largeGaps hH hBp 1).imp fun _ h => h.imp fun _ h Cg hCg => (h Cg hCg).2.2
  obtain ⟨Cgf, hOB⟩ := GlobalTheory.T.oneBessel_torusTranslates_largeGap hH
  obtain ⟨Cf, hCf, hFrm⟩ := GlobalTheory.FrameTurn.frameChange_of_frames 1 Cgf 2 zero_le_one (by norm_num)
  obtain ⟨Ca, hCa, hAmp⟩ := GlobalTheory.T.amplitude_eq_besselFunction_largeGaps hH Cg cb Cu cT CT C0 C1
  refine ⟨max (Ca + Cβ * (Cf + max Cb 0 + Cf * max Cb 0)) (max Cb 0), 1000, fun eps Fm _ hl hR Cn => ?_⟩
  obtain ⟨m₀, hA⟩ := hAmp Cn
  obtain ⟨x0, hx0⟩ := GlobalTheory.family_sizes_eventually_large eps Fm m₀
  have hAmpF : OwnEv Fm fun C' Cl x i => Bridge.AmpIsBessel (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 Ca :=
    ⟨x0, fun x hx i => hA (Fm.D x i) (Fm.L x i) _ _ hl (hx0 x hx i).2.2.2.2.1 (hx0 x hx i).2.1
      (Fm.ties x i).cdScale_tie⟩
  obtain ⟨a', hFr⟩ := hFrm Cn
  have hStd := Formalism.MainNotions.BridgeLemma.stdHypS_of Fm Cg cb Cu cT CT C0 1 Cβ (by linarith) zero_le_one hβ2 hu hT hg
    (max Cg₀ a') (200 * Cn)
  have hTF := tFrame_of_dsig hM hH.2.2.2 Fm (by linarith) hR
  exact Formalism.MainNotions.S.OwnEv.mono (fun C' Cl x i H =>
    AuxiliaryNormPrimes.plancherelBoundOneParameter_of_uniformity _ _ _ _ _ _ _ _ _ _ Cn C1 Ca 1 Cf (max Cg₀ a') (200 * Cn) Cβ (max Cb 0) _ H.1.1
      (hFr _ (le_max_right _ _) _ (Formalism.MainNotions.OnePlaceExpansion.frame_bound_of_bessel_torus _ Cgf 2 le_rfl (hOB _)))
      H.1.2 H.2
      (OnePlaceEstimates.upper_bound_mono_constant _ one_pos (le_max_left _ _) (hBP _ (le_max_left _ _) _ Cn (200 * Cn) le_rfl))
      (by linarith) (le_max_right _ _) hCa hCf (le_max_left _ _) (le_max_right _ _)) ((hAmpF.and hStd).and hTF)

end GlobalTheory.UnifPTGap
