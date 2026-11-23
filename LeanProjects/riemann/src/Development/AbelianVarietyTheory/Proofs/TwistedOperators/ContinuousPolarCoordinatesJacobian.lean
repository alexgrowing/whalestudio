import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY

noncomputable section
namespace GlobalTheory.PolarU
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

theorem continuous_sinhc_series {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] :
    Continuous fun x : A => ∑' k : ℕ, (((2 * k + 1).factorial : ℂ)⁻¹) • x ^ (2 * k) := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  set R : ℝ := ‖x₀‖ + 1
  have hball : Metric.ball x₀ 1 ∈ nhds x₀ := Metric.ball_mem_nhds x₀ one_pos
  refine ContinuousOn.continuousAt ?_ hball
  have hsum : Summable fun k : ℕ => ((2 * k + 1).factorial : ℝ)⁻¹ * (‖(1 : A)‖ + R ^ (2 * k)) := by
    have h1 : Summable fun n : ℕ => R ^ n / (n.factorial : ℝ) := Real.summable_pow_div_factorial R
    have h2 : Summable fun k : ℕ => R ^ (2 * k) / ((2 * k).factorial : ℝ) := by
      have := h1.comp_injective (i := fun k : ℕ => 2 * k) (fun a b h => by simp only at h; omega)
      simpa only [Function.comp_def] using this
    have h3 : Summable fun n : ℕ => (1 : ℝ) ^ n / (n.factorial : ℝ) := Real.summable_pow_div_factorial 1
    have h4 : Summable fun k : ℕ => ((2 * k + 1).factorial : ℝ)⁻¹ := by
      have := h3.comp_injective (i := fun k : ℕ => 2 * k + 1) (fun a b h => by simp only at h; omega)
      simpa only [Function.comp_def, one_pow, one_div] using this
    refine (((h4.mul_left ‖(1 : A)‖)).add h2).of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    rw [mul_add, mul_comm _ ‖(1 : A)‖]
    gcongr
    have hf : ((2 * k).factorial : ℝ) ≤ ((2 * k + 1).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (by omega)
    have hp : (0 : ℝ) < ((2 * k).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    rw [div_eq_mul_inv, mul_comm]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hp hf) (by positivity)
  refine continuousOn_tsum (fun k => (continuous_const.smul (continuous_pow _)).continuousOn) hsum ?_
  intro k x hx
  have hxR : ‖x‖ ≤ R := by
    have := Metric.mem_ball.1 hx
    have h := norm_le_norm_add_norm_sub' x x₀
    rw [dist_eq_norm] at this
    simp only [R]; linarith
  have hpow : ‖x ^ (2 * k)‖ ≤ ‖(1 : A)‖ + R ^ (2 * k) := by
    rcases Nat.eq_zero_or_pos (2 * k) with h | h
    · rw [h, pow_zero, pow_zero]; linarith [norm_nonneg (1 : A)]
    · calc ‖x ^ (2 * k)‖ ≤ ‖x‖ ^ (2 * k) := norm_pow_le' x h
        _ ≤ R ^ (2 * k) := pow_le_pow_left₀ (norm_nonneg x) hxR _
        _ ≤ ‖(1 : A)‖ + R ^ (2 * k) := le_add_of_nonneg_left (norm_nonneg _)
  calc ‖(((2 * k + 1).factorial : ℂ)⁻¹) • x ^ (2 * k)‖
      ≤ ‖(((2 * k + 1).factorial : ℂ)⁻¹)‖ * ‖x ^ (2 * k)‖ := norm_smul_le _ _
    _ = ((2 * k + 1).factorial : ℝ)⁻¹ * ‖x ^ (2 * k)‖ := by rw [norm_inv, Complex.norm_natCast]
    _ ≤ ((2 * k + 1).factorial : ℝ)⁻¹ * (‖(1 : A)‖ + R ^ (2 * k)) := by gcongr

theorem continuous_adMat (p q : ℕ) : Continuous (adMat : Mat p q → _) := by
  unfold adMat
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [Matrix.sub_apply, Matrix.kroneckerMap_apply, Matrix.transpose_apply]
  exact ((continuous_apply_apply a.1 b.1).mul continuous_const).sub
    (continuous_const.mul (continuous_apply_apply b.2 a.2))

open scoped Matrix.Norms.Operator in
theorem continuous_sinhcAd (p q : ℕ) : Continuous (sinhcAd : Mat p q → _) := by
  unfold sinhcAd
  exact continuous_sinhc_series.comp (continuous_adMat p q)

theorem continuous_polJ : ∀ (p q : ℕ), Continuous (polJ : Mat p q → ℝ) := by
  intro p q
  unfold polJ
  exact Complex.continuous_re.comp
    (((continuous_sinhcAd p q).matrix_submatrix _ _).matrix_det)

end GlobalTheory.PolarU
