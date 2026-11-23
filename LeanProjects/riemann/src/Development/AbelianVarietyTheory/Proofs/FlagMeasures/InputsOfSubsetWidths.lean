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
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg

theorem inputs_of_subset_widths : ∀ S S' : Set ℝ, S ⊆ S' → (AmpOn S' → AmpOn S) ∧ (SmallOn S' → SmallOn S) ∧ (CntOn S' → CntOn S) ∧ (CountBoundOn S' → CountBoundOn S) ∧ (TieOn S' → TieOn S) := by
  intro S S' hSS
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h Cg cb Cu cT CT hb hT
    obtain ⟨C, C2, Ch, h1, h2, h3⟩ := h Cg cb Cu cT CT hb hT
    refine ⟨C, C2, Ch, h1, h2, fun Cpr δ hδ => ?_⟩
    obtain ⟨thr, ht⟩ := h3 Cpr δ hδ
    exact ⟨thr, fun C0 hC0 => ht C0 (hSS hC0)⟩
  · intro h Cg cb Cu cT CT δ hb hT hδ
    obtain ⟨thr, ht⟩ := h Cg cb Cu cT CT δ hb hT hδ
    exact ⟨thr, fun C0 hC0 => ht C0 (hSS hC0)⟩
  · intro h Cg cb Cu cT CT
    obtain ⟨c3, cH, cS, c4, thr, ht⟩ := h Cg cb Cu cT CT
    exact ⟨c3, cH, cS, c4, thr, fun C0 hC0 => ht C0 (hSS hC0)⟩
  · intro h Cg cb Cu cT CT
    obtain ⟨c3, cH, thr, ht⟩ := h Cg cb Cu cT CT
    exact ⟨c3, cH, thr, fun C0 hC0 => ht C0 (hSS hC0)⟩
  · intro h Cg cb Cu cT CT
    obtain ⟨cV, thr, ht⟩ := h Cg cb Cu cT CT
    exact ⟨cV, thr, fun C0 hC0 => ht C0 (hSS hC0)⟩

end GlobalTheory.Core.Deg
