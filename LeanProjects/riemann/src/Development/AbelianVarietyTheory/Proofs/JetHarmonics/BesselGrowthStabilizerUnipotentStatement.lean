import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGrowthStabilizerUnipotent
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselGrowth_stabilizer_unipotent : Formalism.FourierDecayAlt.ThreeDimData.GrowthS := by
  first | exact @GlobalTheory.besselGrowthS | exact GlobalTheory.besselGrowthS | (intros; apply GlobalTheory.besselGrowthS <;> assumption)
