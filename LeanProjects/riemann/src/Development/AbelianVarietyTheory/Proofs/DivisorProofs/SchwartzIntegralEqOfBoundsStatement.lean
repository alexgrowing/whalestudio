import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzIntegralEqOfBounds
import Mathlib
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_integral_eq_of_bounds : ∀ {D S : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] [TopologicalSpace S] [SecondCountableTopology S]
    [MeasurableSpace S] [OpensMeasurableSpace S] (ν : Measure S) (f : S → SchwartzMap D ℂ) (F : SchwartzMap D ℂ),
    Continuous f →
    (∀ m n : ℕ, ∃ c : S → ℝ, Integrable c ν ∧ ∀ s, SchwartzMap.seminorm ℂ m n (f s) ≤ c s) →
    (∀ (n : ℕ) (x : D), iteratedFDeriv ℝ n F x = ∫ s, iteratedFDeriv ℝ n (f s) x ∂ν) →
    ∀ T : SchwartzMap D ℂ →L[ℂ] ℂ, T F = ∫ s, T (f s) ∂ν := by
  first | exact @GlobalTheory.SchwartzFormIntegral.form_integral_comm | exact GlobalTheory.SchwartzFormIntegral.form_integral_comm | (intros; apply GlobalTheory.SchwartzFormIntegral.form_integral_comm <;> assumption)
