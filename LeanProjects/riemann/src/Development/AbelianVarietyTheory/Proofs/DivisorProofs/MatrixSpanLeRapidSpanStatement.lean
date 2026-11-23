import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixSpanLeRapidSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.MeasurableCompInfGL
open Classical MeasureTheory NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_span_le_rapid_span : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (π : GlobalTheory.CuspRep.CuspSub E a), GlobalTheory.JSW.mspan π ≤ GlobalTheory.JSW.rspan π := by
  first | exact @GlobalTheory.JSW.mspan_le_rspan | exact GlobalTheory.JSW.mspan_le_rspan | (intros; apply GlobalTheory.JSW.mspan_le_rspan <;> assumption)
