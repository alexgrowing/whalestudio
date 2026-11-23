import Mathlib
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.SpanEquality
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_equality : SpanEq := by
  first | exact @GlobalTheory.CompanionTheory.InertSpan.spanEq | exact GlobalTheory.CompanionTheory.InertSpan.spanEq | (intros; apply GlobalTheory.CompanionTheory.InertSpan.spanEq <;> assumption)
