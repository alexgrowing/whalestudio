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
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyStatementOfItemsFourSeven
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmpBoundsUniformOfInputs
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UniformAmplitudeBoundWideRangeLargeGapStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AbsAllAlongFamilyGap
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DegIAlongFamily
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PtDlAlongFamilyGap
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TcritLowAlongFamilyGap
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeNormDegreeAlongFamilyOfKFiniteIdentity
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SchurAlongFamily
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdSubEqProdFactorial
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsWordLetters
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.GapAmpUniform

theorem weyl_fam_gap : ∀ (eps : ℝ) (Fm : FamP eps), VanishingOnXAndXPlusBranching.FamilyTwelfthHypothesis Fm := by
  intro eps Fm x i τ w H _ _ z π hπ
  obtain ⟨g, -, hg⟩ := hπ
  exact (GlobalTheory.WeylDimU.weyl_dimension _ _ (GlobalTheory.CritLevel.isHCParam_uS (Fm.D x i) w τ)).1 H _ hg

theorem amplitude_bounds_uniform_gap : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS → ∀ Cg cb Cu cT CT C0 A C1 : ℝ, ∃ C C2 Ch thr : ℝ, 0 ≤ C ∧ 0 ≤ Ch ∧ ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → ∀ Cpr : ℝ, ∀ δ > 0, (OwnEv Fm fun C' Cl x i => VanishingOnXAndXPlus.AmplitudeBoundsConjunction (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 A C1 Cpr C C2 Ch δ) := by
  intro hM hH hB Cg cb Cu cT CT C0 A C1
  obtain ⟨CPT, t1, hPT⟩ := GlobalTheory.T.uniform_amplitude_bound_wide_range_large_gap hM hH hB Cg cb Cu cT CT C0 C1
  obtain ⟨CDl, t2, hDl⟩ := GlobalTheory.FamDlGap.ptDl_along_family_gap hM hH hB Cg cb Cu cT CT C0 C1
  obtain ⟨t3, h5⟩ := GlobalTheory.CritLevelGap.tcritLow_along_family_gap hM hH hB Cg cb Cu cT CT C0
  obtain ⟨t4, h9⟩ := GlobalTheory.AmpFamGap.amplitudeNormDegree_along_family_largeGaps hM hH hB Cg cb Cu cT CT C0 C1
  obtain ⟨hilbertNinetyConstant, t5, hilbertNinetyConstant_pos, hDeg⟩ := GlobalTheory.DegStepG.degI_along_family hM hH hB Cg cb Cu cT CT C0 C1
  obtain ⟨Ca, t6, hCa, hAC⟩ := GlobalTheory.GapUAmp.abs_all_along_family_gap hM hH hB Cg cb Cu cT CT C0 A C1
  obtain ⟨CS, t8, hS⟩ := GlobalTheory.GapAmp.schur_along_family hM hH hB Cg cb Cu cT CT C0 C1
  obtain ⟨C, C2, Ch, hC, hCh, H⟩ := GlobalTheory.ampBounds_uniform_of_inputs Cg cb Cu cT CT C0 A C1 CPT CDl hilbertNinetyConstant Ca CS hilbertNinetyConstant_pos hCa
  refine ⟨C, C2, Ch, max t1 (max t2 (max t3 (max t4 (max t5 (max t6 t8))))), hC, hCh, ?_⟩
  intro eps Fm h1 h2 hR Cpr δ hδ
  exact H eps Fm
    (hPT eps Fm ((le_max_left _ _).trans h1) ((le_max_left _ _).trans h2) hR)
    (hDl eps Fm (by simp at h1 ⊢; tauto) (by simp at h2 ⊢; tauto) hR)
    (h5 eps Fm (by simp at h1 ⊢; tauto) (by simp at h2 ⊢; tauto) hR)
    (h9 eps Fm (by simp at h1 ⊢; tauto) (by simp at h2 ⊢; tauto) hR)
    (hDeg eps Fm (by simp at h1 ⊢; tauto) (by simp at h2 ⊢; tauto) hR)
    (hAC eps Fm (by simp at h1 ⊢; tauto) (by simp at h2 ⊢; tauto) hR).1
    (hAC eps Fm (by simp at h1 ⊢; tauto) (by simp at h2 ⊢; tauto) hR).2
    (hS eps Fm (by simp at h1 ⊢; tauto) (by simp at h2 ⊢; tauto) hR)
    (weyl_fam_gap eps Fm) Cpr δ hδ

end GlobalTheory.GapAmpUniform
