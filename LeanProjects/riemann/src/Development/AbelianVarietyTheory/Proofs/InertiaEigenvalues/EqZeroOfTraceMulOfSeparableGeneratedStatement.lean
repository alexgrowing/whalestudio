import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfTraceMulOfSeparableGenerated
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_trace_mul_of_separable_generated : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → (∀ a : B.A, ∃ f : K.E[X], a = aeval B.g f) → ∀ w : B.A, (∀ y, Algebra.trace K.E B.A (w * y) = 0) → w = 0 := by
  first | exact @GlobalTheory.UnitLemma.TraceNondeg.eq_zero_of_trace_mul_eq_zero | exact GlobalTheory.UnitLemma.TraceNondeg.eq_zero_of_trace_mul_eq_zero | (intros; apply GlobalTheory.UnitLemma.TraceNondeg.eq_zero_of_trace_mul_eq_zero <;> assumption)
