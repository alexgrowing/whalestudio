import Mathlib
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.PointwiseOfSpanHeisenberg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointwise_of_span_heisenberg : AddVec → Dual → SpanEq → Heis → Pointwise := by
  first | exact @GlobalTheory.CompanionTheory.InertLen.pointwise | exact GlobalTheory.CompanionTheory.InertLen.pointwise | (intros; apply GlobalTheory.CompanionTheory.InertLen.pointwise <;> assumption)
