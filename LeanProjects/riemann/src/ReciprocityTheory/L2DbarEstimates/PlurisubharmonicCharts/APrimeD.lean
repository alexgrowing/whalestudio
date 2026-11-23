import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.APrimeDA

open Complex ComplexConjugate

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal

noncomputable section

namespace LeviFormQuadraticSums

variable {n d : ℕ} {p : V n → V d} {U : Set (V n)}

theorem norm_bound (c : ℝ) (hc : 0 < c) (x y : Fin d → ℂ) (P : V d) (hP : ∀ k, ‖x k‖ = ‖P k‖)
    (B : ℝ) (hB : B = ∑ k, ‖y k‖ ^ 2) :
    ‖∑ k, (c : ℂ)⁻¹ * (x k * y k)‖ ^ 2 ≤ (‖P‖ ^ 2 / c) * (c⁻¹ * B) := by
  rw [← Finset.mul_sum, norm_mul, mul_pow, EuclideanSpace.norm_sq_eq]
  have cs := norm_sum_mul_sq_le x y
  simp only [hP] at cs
  rw [← hB] at cs
  have hn : ‖(c : ℂ)⁻¹‖ = c⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hc.le]
  rw [hn]
  have e : (∑ k, ‖P k‖ ^ 2) / c * (c⁻¹ * B) = c⁻¹ ^ 2 * ((∑ k, ‖P k‖ ^ 2) * B) := by
    field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left cs (sq_nonneg _)

theorem arith {a b t L s : ℝ} (ha : 0 ≤ a) (hab : 0 ≤ a + t * b) (hL : 0 ≤ L) (hs0 : 0 ≤ s)
    (hs : s ≤ t * L) : 0 ≤ a * L + b * s := by
  rcases le_total 0 b with hb | hb
  · positivity
  · nlinarith [mul_le_mul_of_nonpos_left hs hb, mul_nonneg hab hL]

end LeviFormQuadraticSums

end

end ReciprocityTheory.L2DbarEstimates.Y
