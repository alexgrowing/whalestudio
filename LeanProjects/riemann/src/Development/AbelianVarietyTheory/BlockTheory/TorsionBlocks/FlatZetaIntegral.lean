import Mathlib

open MeasureTheory Set

namespace GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral

variable {X : Type} [MeasurableSpace X]

noncomputable def flatIntegrand (f : X → ℂ) (a : X → ℝ) (s₀ s : ℂ) (x : X) : ℂ :=
  f x * ((a x : ℝ) : ℂ) ^ (s - s₀)

noncomputable def flatZeta (μ : Measure X) (f : X → ℂ) (a : X → ℝ) (s₀ s : ℂ) : ℂ :=
  ∫ x, flatIntegrand f a s₀ s x ∂μ

def ConvergesAbsLocUnifOn (μ : Measure X) (F : ℂ → X → ℂ) (D : Set ℂ) : Prop :=
  (∀ s ∈ D, Integrable (F s) μ) ∧
    ∀ s ∈ D, ∃ U ∈ nhdsWithin s D, ∃ g : X → ℝ, Integrable g μ ∧
      ∀ s' ∈ U, ∀ x, ‖F s' x‖ ≤ g x

def FlatZetaHolomorphic : Prop :=
  ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (f : X → ℂ) (a : X → ℝ) (s₀ s₁ : ℂ),
    Measurable a → (∀ x, 0 < a x) → (∀ x, a x ≤ 1) →
    Integrable (flatIntegrand f a s₀ s₁) μ →
      ConvergesAbsLocUnifOn μ (flatIntegrand f a s₀) {s | s₁.re ≤ s.re} ∧
      DifferentiableOn ℂ (flatZeta μ f a s₀) {s | s₁.re < s.re} ∧
      ContinuousOn (flatZeta μ f a s₀) {s | s₁.re ≤ s.re}

omit [MeasurableSpace X] in

theorem flatIntegrand_self (f : X → ℂ) (a : X → ℝ) (s₀ : ℂ) : flatIntegrand f a s₀ s₀ = f := by
  funext x
  simp [flatIntegrand]

omit [MeasurableSpace X] in

theorem norm_flatIntegrand (f : X → ℂ) {a : X → ℝ} (s₀ s : ℂ) {x : X} (hx : 0 < a x) :
    ‖flatIntegrand f a s₀ s x‖ = ‖f x‖ * a x ^ (s.re - s₀.re) := by
  rw [flatIntegrand, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.sub_re]

example (s : ℂ) :
    Integrable (flatIntegrand (fun _ : Unit => (1 : ℂ)) (fun _ => (1 / 2 : ℝ)) 0 s)
        (Measure.dirac ()) ∧
      flatZeta (Measure.dirac ()) (fun _ : Unit => (1 : ℂ)) (fun _ => (1 / 2 : ℝ)) 0 s
        = (((1 / 2 : ℝ) : ℝ) : ℂ) ^ s := by
  refine ⟨?_, ?_⟩
  · exact Integrable.of_finite
  · simp [flatZeta, flatIntegrand]

end GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral
