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
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.FamilyStatementOfAbsAndVandermonde
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SizesLargeOfPowerBounds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormalDegreeRatioEqHarishChandraRatioLargeGapStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GapNearPlaceParameterHalfNoncompactGapStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

noncomputable section

namespace GlobalTheory.DegStepG

theorem vandLine (hH : GlobalTheory.GapIn.Hyp) (Cn m₀ : ℝ)
    (hnear : ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), GlobalTheory.Amp.HypZ D large₂ C' Cl Cg cb Cu cT CT C0 →
      1000 ≤ Cl → m₀ ≤ D.R.m → ∀ (τ : D.what₂.Tau) (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ),
        l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 + D.R.r →
        Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) lam' ((D.R.r : ℝ) ^ 19 / 2) ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS ((D.R.r : ℝ) ^ 19 / 2))
    (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 C1 : ℝ) (hCl : 1000 ≤ Cl) (hm : m₀ ≤ D.R.m) :
    Formalism.MainNotions.BridgeLemma₂.deg_VandLine D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 := by
  intro hH0 τ w w' _ θ _ W _ lam' hl A hA I s hs A' hA'
  have hZ : GlobalTheory.Amp.HypZ D large₂ C' Cl Cg cb Cu cT CT C0 := hH0
  have hcard : (I.card : ℝ) ≤ D.R.r := by
    rw [← Formalism.MainNotions.BridgeLemma₂.deg_cast_r]
    have : I.card ≤ 2 * D.R.rS + D.R.k + 1 := by
      have := Finset.card_le_univ I
      rwa [Fintype.card_fin] at this
    exact_mod_cast this
  have hr0 : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
  have h1 : l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 + D.R.r := by linarith
  have h2 : l1dist (lam' + s • epsI I) (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 + D.R.r :=
    le_trans (Formalism.MainNotions.BridgeLemma.l1_distance_sign_step _ _ s hs I) (by linarith)
  obtain ⟨g1, gok⟩ := hnear D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl hm τ lam' h1
  obtain ⟨g2, _⟩ := hnear D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl hm τ _ h2
  exact GlobalTheory.T.formalDegree_ratio_eq_harishChandra_ratio_largeGap hH D W lam' (lam' + s • epsI I) A A' _ hA hA' g1 g2 gok

theorem degI_along_family : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS →
    ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ C thr : ℝ, 0 ≤ C ∧ ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm →
      PX.RanksF Fm C0 Cg cb Cu cT CT → ∀ Cn : ℝ,
        OwnEv Fm fun C' Cl x i => Formalism.MainNotions.BridgeLemma.DegreeRatioUnitShiftBound (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 C := by
  intro _ hH _ Cg cb Cu cT CT C0 C1
  refine ⟨1, 1000, zero_le_one, fun eps Fm _ hCl _ Cn => ?_⟩
  obtain ⟨m₀, hnear⟩ := GlobalTheory.T.gap_near_placeParameter_half_noncompactGap Cn
  obtain ⟨x0, hx0⟩ := GlobalTheory.family_sizes_eventually_large eps Fm m₀
  refine ⟨x0, fun x hx i => ?_⟩
  exact Formalism.MainNotions.BridgeLemma₂.degree_ratio_one_of_vandermonde _ _ _ _ _ _ _ _ _ _ _ _
    (vandLine hH Cn m₀ hnear (Fm.D x i) (Fm.L x i) _ _ _ _ _ _ _ _ _ hCl (hx0 x hx i).2.1)

end GlobalTheory.DegStepG
