import Mathlib

open MeasureTheory

noncomputable section

namespace GlobalTheory.ConeSch

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem integral_curryLeft {α : Type} [MeasurableSpace α] (ν : Measure α) {n : ℕ}
    (F : α → ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => V) ℂ) :
    ∫ a, (F a).curryLeft ∂ν = (∫ a, F a ∂ν).curryLeft :=
  (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => V) ℂ).toLinearIsometry.integral_comp_comm F

theorem hasFDerivAt_integral_curry {α : Type} [MeasurableSpace α] (ν : Measure α) {n : ℕ}
    (F : α → V → ContinuousMultilinearMap ℝ (fun _ : Fin n => V) ℂ)
    (F' : α → V → ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => V) ℂ) (c : α → ℝ)
    (hF : ∀ a v, HasFDerivAt (F a) (F' a v).curryLeft v)
    (hFm : ∀ v, AEStronglyMeasurable (fun a => F a v) ν) (hFi : ∀ v, Integrable (fun a => F a v) ν)
    (hF'm : ∀ v, AEStronglyMeasurable (fun a => F' a v) ν) (hb : ∀ a v, ‖F' a v‖ ≤ c a)
    (hc : Integrable c ν) (v : V) :
    HasFDerivAt (fun w => ∫ a, F a w ∂ν) (∫ a, F' a v ∂ν).curryLeft v := by
  have h := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := ν) (F := fun w a => F a w)
    (F' := fun w a => (F' a w).curryLeft) (x₀ := v) (bound := c) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun w => hFm w) (hFi v)
    ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => V) ℂ).continuous.comp_aestronglyMeasurable (hF'm v))
    (ae_of_all _ fun a w _ => by simpa using hb a w) hc (ae_of_all _ fun a w _ => hF a w)
  rw [integral_curryLeft] at h
  exact h

end GlobalTheory.ConeSch
