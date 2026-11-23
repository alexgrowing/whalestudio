import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem mul_diagonal_eq_neg_of_exp {ι : Type} [Fintype ι] [DecidableEq ι] (y : Matrix ι ι ℂ) (d d' : ι → ℝ)
    (h : diagonal (fun i => (Real.exp (d' i) : ℂ)) * y * diagonal (fun i => (Real.exp (d i) : ℂ)) = y) :
    y * diagonal (fun i => (d i : ℂ)) = -(diagonal (fun i => (d' i : ℂ)) * y) := by
  ext i j
  have hij := congrFun (congrFun h i) j
  rw [mul_diagonal, diagonal_mul] at hij
  rw [neg_apply, mul_diagonal, diagonal_mul]
  by_cases hy : y i j = 0
  · simp [hy]
  · have h1 : ((Real.exp (d' i) : ℝ) : ℂ) * (Real.exp (d j) : ℝ) = 1 := by
      apply mul_left_cancel₀ hy
      linear_combination hij
    have h2 : Real.exp (d' i + d j) = 1 := by
      rw [Real.exp_add]
      exact_mod_cast h1
    have h3 : d' i + d j = 0 := by simpa using h2
    have h4 : (d' i : ℂ) + (d j : ℂ) = 0 := by exact_mod_cast h3
    linear_combination (y i j) * h4

theorem mul_log_eq_neg_log_mul : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (x x' H H' : Matrix ι ι ℂ), IsLog H (xᴴ * x) → IsLog H' (x'ᴴ * x') → x' * x = 1 → x * H = -(H' * x) := by
  intro ι _ _ x x' H H' ⟨U, d, hU, hH, hA⟩ ⟨V, d', hV, hH', hA'⟩ hx
  have hx' : x * x' = 1 := mul_eq_one_comm.mp hx
  have hU' : Uᴴ * U = 1 := mul_eq_one_comm.mp hU
  have hV' : Vᴴ * V = 1 := mul_eq_one_comm.mp hV
  have key : (x'ᴴ * x') * x * (xᴴ * x) = x := by
    calc (x'ᴴ * x') * x * (xᴴ * x) = x'ᴴ * (x' * x) * xᴴ * x := by simp only [Matrix.mul_assoc]
      _ = (x * x')ᴴ * x := by rw [hx, Matrix.mul_one, conjTranspose_mul]
      _ = x := by rw [hx', conjTranspose_one, Matrix.one_mul]
  rw [hA, hA'] at key
  have hy := mul_diagonal_eq_neg_of_exp (Vᴴ * x * U) d d' (by
    calc _ = (Vᴴ * V) * diagonal (fun i => (Real.exp (d' i) : ℂ)) * (Vᴴ * x * U) *
            diagonal (fun i => (Real.exp (d i) : ℂ)) * (Uᴴ * U) := by
          rw [hV', hU', Matrix.one_mul, Matrix.mul_one]
      _ = Vᴴ * (V * diagonal (fun i => (Real.exp (d' i) : ℂ)) * Vᴴ * x *
            (U * diagonal (fun i => (Real.exp (d i) : ℂ)) * Uᴴ)) * U := by
          simp only [Matrix.mul_assoc]
      _ = Vᴴ * x * U := by rw [key])
  calc x * H = (V * Vᴴ) * x * H := by rw [hV, Matrix.one_mul]
    _ = V * (Vᴴ * x * U * diagonal (fun i => (d i : ℂ))) * Uᴴ := by
        rw [hH]; simp only [Matrix.mul_assoc]
    _ = -(H' * x * (U * Uᴴ)) := by
        rw [hy, hH']; simp only [Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul]
    _ = -(H' * x) := by rw [hU, Matrix.mul_one]

end GlobalTheory.ClassFin
