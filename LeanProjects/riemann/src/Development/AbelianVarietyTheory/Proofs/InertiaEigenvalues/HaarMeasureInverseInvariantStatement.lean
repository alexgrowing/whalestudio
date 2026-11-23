import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HaarMeasureInverseInvariant
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_measure_inverse_invariant : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) [MeasurableSpace (GA E n)] [BorelSpace (GA E n)]
    (ν : Measure (GlobalTheory.CellDec.NA E n)) [ν.IsHaarMeasure], ν.IsInvInvariant := by
  first | exact @GlobalTheory.CellDec.NA_isInvInvariant | exact GlobalTheory.CellDec.NA_isInvInvariant | (intros; apply GlobalTheory.CellDec.NA_isInvInvariant <;> assumption)
