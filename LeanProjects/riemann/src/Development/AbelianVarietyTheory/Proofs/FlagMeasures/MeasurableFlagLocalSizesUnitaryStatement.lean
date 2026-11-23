import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableFlagLocalSizesUnitary
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_flagLocalSizes_unitary : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) (i : Fin a), Measurable fun g : Formalism.REAL.UJ ε => locSize j W (uMat g) i := by
  first | exact @GlobalTheory.FlagMeas.measurable_locSize_uMat | exact GlobalTheory.FlagMeas.measurable_locSize_uMat | (intros; apply GlobalTheory.FlagMeas.measurable_locSize_uMat <;> assumption)
