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
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableBcWeight
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselMapMultipleIsometryLargeGapStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeMultOneDecayOfLargeGapHypothesesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableEmbeddingLmul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SizesLargeOfPowerBounds

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.GapAmp

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants in

theorem bessel_schur_gap (hH : GlobalTheory.GapIn.Hyp) (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ)
    (hCl : 1000 ≤ Cl) : BSch D large₂ C' Cl Cg cb Cu cT CT C0 := by
  intro hZ
  have hv1 : 1 ≤ D.host.v := hZ.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine GlobalTheory.T.besselMap_multipleIsometry_largeGap hH D large₂ C' Cl Cg cb Cu cT CT C0 hCl
    (fun _ _ _ _ _ h => GlobalTheory.BesselSchur.theta_pos D (by linarith) h) (fun w => ?_) hZ
  unfold Tr
  exact_mod_cast (D.mem w).A.T_prime.pos

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S in

theorem schur_along_family : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS →
    ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ C thr : ℝ, ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm →
      PX.RanksF Fm C0 Cg cb Cu cT CT →
        OwnEv Fm fun C' Cl x i => VanishingOnXAndXPlusBranching.adm11 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 C1 C := by
  intro _ hH _ Cg cb Cu cT CT C0 C1
  obtain ⟨C₀, hC⟩ := GlobalTheory.Amp.schurSt_of_big_tie Cg cb Cu cT CT C0 C1
  obtain ⟨m₀, hm⟩ := hC C₀ le_rfl
  obtain ⟨m₁, hL⟩ := GlobalTheory.T.amplitudeMultOneDecay_of_largeGapHypotheses hH Cg cb Cu cT CT C0
  refine ⟨C₀, 1000, fun eps Fm _ h2 _ => ?_⟩
  obtain ⟨x0, hx⟩ := GlobalTheory.family_sizes_eventually_large eps Fm (max (max m₀ m₁) 1)
  refine ⟨x0, fun x hxx i => ?_⟩
  obtain ⟨-, hmM, -, -, hrd, -⟩ := hx x hxx i
  have hm1 : (1 : ℝ) ≤ ((Fm.D x i).R.m : ℝ) := le_trans (le_max_right _ _) hmM
  have hCm : 1 ≤ sCl Fm * ((Fm.D x i).R.m : ℝ) := by nlinarith
  have hBig : ∀ m' : ℝ, m' ≤ max (max m₀ m₁) 1 → GlobalTheory.Amp.Big (Fm.D x i) (Fm.L x i) (sCl Fm) m' :=
    fun m' hm' => ⟨hrd, hCm, le_trans hm' hmM⟩
  exact hm (Fm.D x i) (Fm.L x i) (sC' Fm) (sCl Fm)
    (hBig m₀ (le_trans (le_max_left _ _) (le_max_left _ _))) (Fm.ties x i).cdScale_tie
    (bessel_schur_gap hH _ _ _ _ _ _ _ _ _ _ h2)
    (hL _ _ _ _ (hBig m₁ (le_trans (le_max_right _ _) (le_max_left _ _))))

end GlobalTheory.GapAmp
