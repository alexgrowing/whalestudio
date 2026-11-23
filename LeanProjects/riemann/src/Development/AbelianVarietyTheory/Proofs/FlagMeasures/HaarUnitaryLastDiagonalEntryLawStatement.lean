import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarUnitaryLastDiagonalEntryLaw
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Formalism.PeriodIntegrals.QuotInv
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.LocalRingCardinality.DataCD
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haarUnitary_lastDiagonalEntry_law : ∀ (k : ℕ) (μ : Measure (PI.MtM (k + 1))), 1 ≤ k → PI.IsHaarOnM (UH (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)) μ → μ Set.univ = 1 → ∀ t : ℝ, 0 ≤ t → t ≤ 1 → μ {g | |‖g (Fin.last k) (Fin.last k)‖ ^ 2 - 1| ≤ t} = ENNReal.ofReal (t ^ k) := by
  first | exact @GlobalTheory.Amp.EntryLaw.measure_entry | exact GlobalTheory.Amp.EntryLaw.measure_entry | (intros; apply GlobalTheory.Amp.EntryLaw.measure_entry <;> assumption)
