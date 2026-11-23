import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzIntegralOfIntegrableBounds
import Mathlib
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_integral_of_integrable_bounds : ∀ {D S : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] [MeasurableSpace S] (ν : Measure S)
    (f : S → SchwartzMap D ℂ),
    (∀ (n : ℕ) (x : D), AEStronglyMeasurable (fun s => iteratedFDeriv ℝ n (f s) x) ν) →
    (∀ m n : ℕ, ∃ c : S → ℝ, Integrable c ν ∧ ∀ s, SchwartzMap.seminorm ℂ m n (f s) ≤ c s) →
    ∃ G : SchwartzMap D ℂ, (∀ x, G x = ∫ s, f s x ∂ν) ∧
      (∀ (n : ℕ) (x : D), iteratedFDeriv ℝ n G x = ∫ s, iteratedFDeriv ℝ n (f s) x ∂ν) ∧
      ∀ (m n : ℕ) (c : S → ℝ), Integrable c ν → (∀ s, SchwartzMap.seminorm ℂ m n (f s) ≤ c s) →
        SchwartzMap.seminorm ℂ m n G ≤ ∫ s, c s ∂ν := by
  first | exact @GlobalTheory.ConeSch.exists_schwartz_integral | exact GlobalTheory.ConeSch.exists_schwartz_integral | (intros; apply GlobalTheory.ConeSch.exists_schwartz_integral <;> assumption)
