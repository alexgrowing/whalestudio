import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.GROWCountStatement
import ReciprocityTheory.L2DbarEstimates.LeviForms.OfRealNormSqSumMul
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.DifferentiableAtChart
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth

open Complex ComplexConjugate Filter Topology
open scoped ContDiff

namespace ReciprocityTheory.L2DbarEstimates.Y

noncomputable section

namespace LeviFormQuadraticSums

variable {n : ℕ}

theorem wdb_sum {ι : Type*} (s : Finset ι) {g : ι → V n → ℂ} {y : V n}
    (hg : ∀ i ∈ s, DifferentiableAt ℝ (g i) y) (j : Fin n) :
    wdb n j (fun w => ∑ i ∈ s, g i w) y = ∑ i ∈ s, wdb n j (g i) y := by
  simp only [wdb, fderiv_fun_sum hg, FunLike.coe_sum, Finset.sum_apply, Finset.mul_sum,
    ← Finset.sum_add_distrib, Finset.sum_div]

theorem norm_sum_mul_sq_le {d : ℕ} (x y : Fin d → ℂ) :
    ‖∑ k, x k * y k‖ ^ 2 ≤ (∑ k, ‖x k‖ ^ 2) * (∑ k, ‖y k‖ ^ 2) := by
  have h1 : ‖∑ k, x k * y k‖ ≤ ∑ k, ‖x k‖ * ‖y k‖ :=
    (norm_sum_le _ _).trans (le_of_eq (by simp))
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖x k‖) (fun k => ‖y k‖)
  calc ‖∑ k, x k * y k‖ ^ 2 ≤ (∑ k, ‖x k‖ * ‖y k‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

theorem normSq_eq_ofReal {z : ℂ} : z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.sq_norm]

section Main

variable {d : ℕ} (p : V n → V d) (U : Set (V n)) (c : ℝ)

theorem q_eq : (fun x => ((‖p x‖ ^ 2 / c : ℝ) : ℂ)) =
    fun x => ∑ k, (c : ℂ)⁻¹ * (p x k * conj (p x k : ℂ)) := by
  funext x
  simp only [normSq_eq_ofReal]
  rw [EuclideanSpace.norm_sq_eq]
  push_cast
  rw [div_eq_inv_mul, Finset.mul_sum]

variable {p U}

end Main

end LeviFormQuadraticSums

end

end ReciprocityTheory.L2DbarEstimates.Y
