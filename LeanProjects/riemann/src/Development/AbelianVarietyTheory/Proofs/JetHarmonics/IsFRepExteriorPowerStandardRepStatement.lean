import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsFRepExteriorPowerStandardRep
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFRep_exteriorPower_standardRep : ∀ (k r : ℕ) (l : ℕ), IsFRep (k := k) (r := r) (cmp l) (cmp l (Formalism.QuantumDeterminants.Hpk k r)) l := by
  first | exact @GlobalTheory.WedgeFRep.isFRep_cmp | exact GlobalTheory.WedgeFRep.isFRep_cmp | (intros; apply GlobalTheory.WedgeFRep.isFRep_cmp <;> assumption)
