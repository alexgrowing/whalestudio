import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GrowthUnitaryGroupRpowNegIntegrable
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.growth_unitaryGroup_rpow_neg_integrable : Formalism.FourierDecayAlt.ThreeDimData.GrowthG := by
  first | exact @GlobalTheory.gN_rpow_neg_integrable_haar | exact GlobalTheory.gN_rpow_neg_integrable_haar | (intros; apply GlobalTheory.gN_rpow_neg_integrable_haar <;> assumption)
