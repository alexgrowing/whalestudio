import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Mathlib
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
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneLeFoldrMax
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantLengthMomentsAmplitudesLargeGapStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SizesLargeOfPowerBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

noncomputable section
open GlobalTheory.Amp

namespace GlobalTheory.GapUAmp

theorem abs_all_along_family_gap : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS → ∀ Cg cb Cu cT CT C0 A C1 : ℝ, ∃ C thr : ℝ, 0 ≤ C ∧ ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → (∀ Cn : ℝ, OwnEv Fm fun C' Cl x i => Formalism.MainNotions.BridgeLemma.AbsAllParameters (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 A C1 Cn C) ∧ (OwnEv Fm fun C' Cl x i => VanishingOnXAndXPlusBranching.PrimeSumLogBound (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 A C1) := by
  intro _ hH _ Cg cb Cu cT CT C0 A C1
  obtain ⟨CMo, hMo⟩ := GlobalTheory.T.majorantLength_moments_amplitudes_largeGap hH Cg cb Cu cT CT C0 C1 25
  obtain ⟨C₀, hAbs⟩ := GlobalTheory.Amp.AbsRange.abs_range Cg cb Cu cT CT C0 C1 CMo
  obtain ⟨m₁, hAbs'⟩ := hAbs (max C₀ 0) (le_max_left _ _)
  refine ⟨max C₀ 0, 1000, le_max_right _ _, ?_⟩
  intro eps Fm _ hCl _
  have key : ∀ Cn : ℝ, OwnEv Fm fun C' Cl x i =>
      ABSr (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 (max C₀ 0) := by
    intro Cn
    obtain ⟨m₂, hM⟩ := hMo Cn
    obtain ⟨x0, hx0⟩ := GlobalTheory.family_sizes_eventually_large eps Fm (max (max m₁ m₂) 1)
    refine ⟨x0, fun x hx i => ?_⟩
    obtain ⟨-, hm, -, -, hrd, -⟩ := hx0 x hx i
    have hm1 : (1 : ℝ) ≤ ((Fm.D x i).R.m : ℝ) := le_trans (le_max_right _ _) hm
    have hB : ∀ m₀, m₀ ≤ max (max m₁ m₂) 1 → Big (Fm.D x i) (Fm.L x i) (sCl Fm) m₀ :=
      fun m₀ h => ⟨hrd, by nlinarith, le_trans h hm⟩
    exact hAbs' Cn _ _ _ _ (hB _ (le_trans (le_max_left _ _) (le_max_left _ _)))
      (hM _ _ _ _ hCl (hB _ (le_trans (le_max_right _ _) (le_max_left _ _))))
  refine ⟨fun Cn => (key Cn).mono ?_, (key 0).mono ?_⟩
  · intro C' Cl x i h τ w w' hTT θ hθ W hW lam' hl S hS γ p hp θ' hθ' νR hR hHyp hD
    have h0 : HypZ (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 := by
      unfold Formalism.MainNotions.S.Cnt.Hyp at hHyp; exact hHyp.1
    exact (h h0 τ w w' hTT θ hθ W hW lam' hl S hS γ p hp θ' hθ' νR hR hD).2
  · intro C' Cl x i h τ w w' hTT θ hθ W hW S hS _ γ p hp θ' hθ' νR hR hHyp hD
    have h0 : HypZ (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 := by
      unfold Formalism.MainNotions.S.Cnt.Hyp at hHyp; exact hHyp.1
    exact (h h0 τ w w' hTT θ hθ W hW (lamD _ τ) (by simp [l1dist]) S hS γ p hp θ' hθ' νR hR hD).1

end GlobalTheory.GapUAmp
