import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BigCellChartDifferentialSkewAndFrobenius
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Dchart
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bigCellChartDifferential_skew_and_frobenius : ∀ (k r : ℕ) (v : EE k r), ((dchart k r v)ᴴ * Hpk k r + Hpk k r * dchart k r v = 0) ∧ (∑ i, ∑ j, ‖dchart k r v i j‖ ^ 2) = ‖v.1.1‖ ^ 2 + ‖v.1.2‖ ^ 2 + 2 * (∑ a, ‖v.2.1 a‖ ^ 2) + ‖v.2.2‖ ^ 2 := by
  first | exact @GlobalTheory.CellDens.DNorm.dchart_skew_norm | exact GlobalTheory.CellDens.DNorm.dchart_skew_norm | (intros; apply GlobalTheory.CellDens.DNorm.dchart_skew_norm <;> assumption)
