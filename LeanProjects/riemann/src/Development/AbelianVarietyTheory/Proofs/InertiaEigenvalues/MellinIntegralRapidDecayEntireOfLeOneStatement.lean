import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MellinIntegralRapidDecayEntireOfLeOne
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.ThetaPoisson GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped ComplexConjugate nonZeroDivisors ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mellin_integral_rapidDecay_entire_of_le_one : ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) (δ : X → ℝ) (F : X → ℂ), Measurable δ → (∀ᵐ x ∂ν, 0 < δ x ∧ δ x ≤ 1) → Integrable δ ν → AEStronglyMeasurable F ν → (∀ K : ℕ, ∃ C : ℝ, ∀ᵐ x ∂ν, ‖F x‖ ≤ C * δ x ^ K) → (∀ s : ℂ, Integrable (fun x => F x * (δ x : ℂ) ^ s) ν) ∧ Differentiable ℂ fun s : ℂ => ∫ x, F x * (δ x : ℂ) ^ s ∂ν := by
  first | exact @GlobalTheory.integral_mul_cpow_of_rapid_decay_entire | exact GlobalTheory.integral_mul_cpow_of_rapid_decay_entire | (intros; apply GlobalTheory.integral_mul_cpow_of_rapid_decay_entire <;> assumption)
