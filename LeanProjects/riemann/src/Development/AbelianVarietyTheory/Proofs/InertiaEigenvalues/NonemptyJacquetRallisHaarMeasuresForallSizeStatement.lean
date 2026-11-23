import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyJacquetRallisHaarMeasuresForallSize
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_jacquetRallisHaarMeasures_forall_size : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ), Nonempty (Meas r F E) := by
  first | exact @GlobalTheory.JR.HaarExist.meas_nonempty | exact GlobalTheory.JR.HaarExist.meas_nonempty | (intros; apply GlobalTheory.JR.HaarExist.meas_nonempty <;> assumption)
