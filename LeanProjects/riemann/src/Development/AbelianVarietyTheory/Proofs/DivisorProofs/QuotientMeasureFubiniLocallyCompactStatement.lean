import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientMeasureFubiniLocallyCompact
import Mathlib

open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_measure_fubini_locally_compact : ∀ (N V L : Type) [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [LocallyCompactSpace N] [T2Space N]
    [SecondCountableTopology N] [MeasurableSpace N] [BorelSpace N]
    [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V] [T2Space V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    [AddCommGroup L] [TopologicalSpace L] [IsTopologicalAddGroup L] [LocallyCompactSpace L] [T2Space L]
    [SecondCountableTopology L] [MeasurableSpace L] [BorelSpace L]
    (χ : N ≃ₜ V × L) (ω : V → V → L), Continuous (fun p : V × V => ω p.1 p.2) →
    (∀ n₁ n₂ : N, χ (n₁ * n₂) = ((χ n₁).1 + (χ n₂).1, (χ n₁).2 + (χ n₂).2 + ω (χ n₁).1 (χ n₂).1)) →
    ∀ (φ : N ≃ₜ* N) (A : V ≃ₜ+ V) (Bl : L ≃ₜ+ L), (∀ n, χ (φ n) = (A (χ n).1, Bl (χ n).2)) →
      mulEquivHaarChar φ = addEquivAddHaarChar A * addEquivAddHaarChar Bl := by
  first | exact @GlobalTheory.HeisChart.mulEquivHaarChar_eq_mul_of_heisenberg_chart | exact GlobalTheory.HeisChart.mulEquivHaarChar_eq_mul_of_heisenberg_chart | (intros; apply GlobalTheory.HeisChart.mulEquivHaarChar_eq_mul_of_heisenberg_chart <;> assumption)
