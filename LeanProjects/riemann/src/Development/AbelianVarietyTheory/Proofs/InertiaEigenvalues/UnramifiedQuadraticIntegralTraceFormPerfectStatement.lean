import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticIntegralTraceFormPerfect
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedQuadratic_integral_traceForm_perfect : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E], (∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y) ∧ (∃ e : E, ‖e‖ ≤ 1 ∧ e + star e = 1) ∧ ∀ y : E, (∀ e : E, ‖e‖ ≤ 1 → ‖Algebra.trace F E (e * y)‖ < 1) → ‖y‖ < 1 := by
  first | exact @GlobalTheory.NTr.traceForm_perfect | exact GlobalTheory.NTr.traceForm_perfect | (intros; apply GlobalTheory.NTr.traceForm_perfect <;> assumption)
