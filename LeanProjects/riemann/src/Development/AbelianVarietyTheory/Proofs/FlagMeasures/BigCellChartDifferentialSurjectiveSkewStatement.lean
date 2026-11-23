import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BigCellChartDifferentialSurjectiveSkew
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Dchart
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bigCellChartDifferential_surjective_skew : ∀ (k r : ℕ) (Z : Mat k r), Zᴴ * Hpk k r + Hpk k r * Z = 0 → ∃ v : EE k r, dchart k r v = Z := by
  first | exact @GlobalTheory.CellDens.Onto.dchart_onto | exact GlobalTheory.CellDens.Onto.dchart_onto | (intros; apply GlobalTheory.CellDens.Onto.dchart_onto <;> assumption)
