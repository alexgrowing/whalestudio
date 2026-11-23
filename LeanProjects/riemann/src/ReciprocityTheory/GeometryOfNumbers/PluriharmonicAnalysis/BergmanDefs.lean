import Mathlib

noncomputable section

namespace ReciprocityTheory.GeometryOfNumbersTheory

open MeasureTheory

variable {X : Type*} [MeasurableSpace X]

def bGram (μ : Measure X) {r : ℕ} (s : Fin r → X → ℂ) (w : X → ℝ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun i j => ∫ x, starRingEnd ℂ (s i x) * s j x * (w x : ℂ) ∂μ

def bNormSq (μ : Measure X) {r : ℕ} (s : Fin r → X → ℂ) (w : X → ℝ) (c : Fin r → ℂ) : ℝ :=
  ∫ x, ‖∑ i, c i * s i x‖ ^ 2 * w x ∂μ

def bergmanDensity (μ : Measure X) {r : ℕ} (s : Fin r → X → ℂ) (w : X → ℝ) (x : X) : ℝ :=
  w x * (∑ i, ∑ j, (bGram μ s w)⁻¹ i j * s i x * starRingEnd ℂ (s j x)).re

end ReciprocityTheory.GeometryOfNumbersTheory
