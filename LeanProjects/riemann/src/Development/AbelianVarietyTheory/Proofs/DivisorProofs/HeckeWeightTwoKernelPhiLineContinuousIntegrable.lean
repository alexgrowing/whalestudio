import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
open NumberField Complex MeasureTheory

namespace GlobalTheory.HeckeTwo.PhiLine

theorem norm_line_sq (t y : ℝ) : ‖((t : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 = t ^ 2 + y ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp; ring

theorem abs_le_norm_line (t y : ℝ) : |y| ≤ ‖((t : ℂ) + (y : ℂ) * Complex.I)‖ := by
  have := Complex.abs_im_le_norm ((t : ℂ) + (y : ℂ) * Complex.I)
  simpa using this

theorem line_ne_zero (t y : ℝ) (hy : y ≠ 0) : ((t : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  exact hy this

theorem norm_phi_le (σ : ℂ) (hσ : 0 < σ.re) (y : ℝ) (hy : y ≠ 0) (t : ℝ) :
    ‖GlobalTheory.HeckeTwo.phi σ ((t : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      |y| ^ (-2 * σ.re) * (min 1 (y ^ 2))⁻¹ * (1 + t ^ 2)⁻¹ := by
  set w : ℂ := (t : ℂ) + (y : ℂ) * Complex.I with hw
  have hay : 0 < |y| := abs_pos.2 hy
  have hle : |y| ≤ ‖w‖ := abs_le_norm_line t y
  have hpos : 0 < ‖w‖ := lt_of_lt_of_le hay hle
  have hsq : ‖w‖ ^ 2 = t ^ 2 + y ^ 2 := norm_line_sq t y
  unfold GlobalTheory.HeckeTwo.phi
  rw [norm_mul, norm_pow, norm_inv, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  have hre : (-2 * σ).re = -2 * σ.re := by simp
  rw [hre]
  have h1 : ‖w‖ ^ (-2 * σ.re) ≤ |y| ^ (-2 * σ.re) :=
    Real.rpow_le_rpow_of_nonpos hay hle (by linarith)
  have hy2 : 0 < y ^ 2 := by positivity
  have hm : 0 < min 1 (y ^ 2) := lt_min one_pos hy2
  have h2 : ‖w‖⁻¹ ^ 2 ≤ (min 1 (y ^ 2))⁻¹ * (1 + t ^ 2)⁻¹ := by
    rw [inv_pow, hsq, ← mul_inv]
    apply inv_anti₀ (by positivity)
    have := min_le_left 1 (y ^ 2)
    have := min_le_right 1 (y ^ 2)
    nlinarith [sq_nonneg t]
  calc ‖w‖⁻¹ ^ 2 * ‖w‖ ^ (-2 * σ.re) ≤ ((min 1 (y ^ 2))⁻¹ * (1 + t ^ 2)⁻¹) * |y| ^ (-2 * σ.re) :=
        mul_le_mul h2 h1 (by positivity) (by positivity)
    _ = _ := by ring

theorem phi_line (σ : ℂ) (hσ : 0 < σ.re) (y : ℝ) (hy : y ≠ 0) :
    Continuous (fun t : ℝ => GlobalTheory.HeckeTwo.phi σ ((t : ℂ) + (y : ℂ) * Complex.I)) ∧
      MeasureTheory.Integrable (fun t : ℝ => GlobalTheory.HeckeTwo.phi σ ((t : ℂ) + (y : ℂ) * Complex.I)) := by
  have hw : Continuous (fun t : ℝ => ((t : ℂ) + (y : ℂ) * Complex.I)) := by fun_prop
  have hcont : Continuous (fun t : ℝ => GlobalTheory.HeckeTwo.phi σ ((t : ℂ) + (y : ℂ) * Complex.I)) := by
    unfold GlobalTheory.HeckeTwo.phi
    refine Continuous.mul ((hw.inv₀ fun t => line_ne_zero t y hy).pow 2) ?_
    refine Continuous.cpow (Complex.continuous_ofReal.comp hw.norm) continuous_const ?_
    intro t
    exact Complex.ofReal_mem_slitPlane.2
      (lt_of_lt_of_le (abs_pos.2 hy) (abs_le_norm_line t y))
  refine ⟨hcont, ?_⟩
  refine MeasureTheory.Integrable.mono' (integrable_inv_one_add_sq.const_mul
    (|y| ^ (-2 * σ.re) * (min 1 (y ^ 2))⁻¹)) hcont.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun t => norm_phi_le σ hσ y hy t

end GlobalTheory.HeckeTwo.PhiLine

theorem GlobalTheory.HeckeTwo.phi_line_continuous_integrable : ∀ (σ : ℂ), 0 < σ.re → ∀ (y : ℝ), y ≠ 0 →
    Continuous (fun t : ℝ => GlobalTheory.HeckeTwo.phi σ ((t : ℂ) + (y : ℂ) * Complex.I)) ∧
      MeasureTheory.Integrable (fun t : ℝ => GlobalTheory.HeckeTwo.phi σ ((t : ℂ) + (y : ℂ) * Complex.I)) :=
  fun σ hσ y hy => GlobalTheory.HeckeTwo.PhiLine.phi_line σ hσ y hy
