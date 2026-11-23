import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DegenerateConstant
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyStatementOfItemsFourSeven
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.MinkowskiDividesFactorialOfBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsWordLetters
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsRawMassAndGenusMassStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowCountsUniformConstantsFamiliesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdmissibleFamilySatisfiesRowEstimatesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeBoundsUniformLargeGapFamiliesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TcritLowOfDsig
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma Formalism.MainNotions.BridgeLemma₂ Formalism.L2.SG.RowsU

noncomputable section

namespace GlobalTheory.LoopRowBoundsGap

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rows_along_family : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS → ∀ Cg cb Cu cT CT C0 A C1 cV CGam : ℝ, ∃ C₀ thr : ℝ, ∀ (eps : ℝ) (Fm : FamP eps), Fm.CGam = CGam → thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → (OwnEv Fm fun C' Cl x i => Cnt.Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 → ∀ u, UnitaryVolumeMass.FormAt (Fm.D x i) u) ∧ ∀ (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i)) (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word), LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1), rows_TiesF Fm C1 X Y → (∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word), wordPairTermInjective (X x hx i) (Y x hx i u u')) → (∀ x (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word), wordPairBetaLattice (Fm.D x i) u u') → (OwnEv Fm fun C' Cl x i => ∀ (hx : Fm.x1 < x) u u', VanishingOnXAndXPlus.TermVolumeSmallCellBound (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1 (Y x hx i u u') C' Cl Cg cb Cu cT CT C0 A cV) → ∀ C ≥ C₀, OwnEv Fm fun C' Cl x i => ∀ (hx : Fm.x1 < x) u u', Cnt.Hyp (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A → RowsND (X x hx i) (Y x hx i u u') C ∧ RowsDeg (X x hx i) (Y x hx i u u') C ∧ RowsOne (X x hx i) (Y x hx i u u') C := by
  intro hSMR hH hBp Cg cb Cu cT CT C0 A C1 cV CGam
  obtain ⟨c3, cH, cS, c4, thr1, HC⟩ := GlobalTheory.T.rowCounts_uniform_constants_families hSMR Cg cb Cu cT CT C0 A
  obtain ⟨Ca, C2, Ch, thr2, hCa, hCh, HA⟩ := GlobalTheory.T.amplitude_bounds_uniform_large_gap_families hSMR hH hBp Cg cb Cu cT CT C0 A C1
  let U : UC := ⟨c3, cH, cV, cS, c4, fun _ => Ca, fun _ => C2, fun _ => Ch⟩
  refine ⟨c0U CT A C0 CGam U, max 40 (max thr1 thr2), fun eps Fm hG hs hl hR => ?_⟩
  have hs1 : thr1 ≤ sC' Fm := (le_max_left _ _).trans ((le_max_right _ _).trans hs)
  have hl1 : thr1 ≤ sCl Fm := (le_max_left _ _).trans ((le_max_right _ _).trans hl)
  have hs2 : thr2 ≤ sC' Fm := (le_max_right _ _).trans ((le_max_right _ _).trans hs)
  have hl2 : thr2 ≤ sCl Fm := (le_max_right _ _).trans ((le_max_right _ _).trans hl)
  have h40 : 40 ≤ sCl Fm := (le_max_left _ _).trans hl
  have h3 : VanishingOnXAndXPlusMass.Conclusion3Family Fm := fun x _ i u => GlobalTheory.T.rows_raw_mass_and_genus_mass (Fm.D x i) u
  obtain ⟨a10a, a6, a7, a8, a10b, hform⟩ :=
    GlobalTheory.CritLevelGap.along_family hH.2.2.2 eps Fm Cg cb Cu cT CT C0 A h40 hR h3
  refine ⟨hform, fun X Y hT hTI hBL hVol C hC => ?_⟩
  obtain ⟨LocalHeightDeterminant, H27, H4, H21⟩ := HC eps Fm hs1 hl1
  have hU : UAdm Fm C1 X Y Cg cb Cu cT CT C0 A U :=
    ⟨LocalHeightDeterminant, H27, hVol, H4, H21, fun Cpr => ⟨hCh, hCa, fun δ hδ => HA eps Fm hs2 hl2 hR Cpr δ hδ⟩⟩
  exact GlobalTheory.T.admissible_family_satisfies_row_estimates eps Fm C1 X Y Cg cb Cu cT CT C0 A a10a a6 a7 a8 a10b hT hTI hBL U hU C (by rw [hG]; exact hC)

end GlobalTheory.LoopRowBoundsGap
