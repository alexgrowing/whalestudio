import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MellinTypeIntegralEntireOfRapidDecay
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemContraIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MeasurePreservingToMixedPiSymm

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mellinType_integral_entire_of_rapid_decay : ∀ {X : Type} [MeasurableSpace X] (ν : Measure X) (A : X → ℂ) (T : X → ℝ),
    AEStronglyMeasurable A ν → Measurable T → (∀ x, 0 < T x) → Integrable (fun x => min (T x) (T x)⁻¹) ν →
    (∀ N : ℕ, ∃ C : ℝ, ∀ x, ‖A x‖ ≤ C * (min (T x) (T x)⁻¹) ^ N) →
    (∀ s : ℂ, Integrable (fun x => A x * ((T x : ℝ) : ℂ) ^ s) ν) ∧
      Differentiable ℂ (fun s : ℂ => ∫ x, A x * ((T x : ℝ) : ℂ) ^ s ∂ν) := by
  first | exact @GlobalTheory.MellinEntire.integrable_and_differentiable | exact GlobalTheory.MellinEntire.integrable_and_differentiable | (intros; apply GlobalTheory.MellinEntire.integrable_and_differentiable <;> assumption)
