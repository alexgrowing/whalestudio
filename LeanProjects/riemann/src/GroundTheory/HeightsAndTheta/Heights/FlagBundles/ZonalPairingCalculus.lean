import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open Polynomial MeasureTheory Set

noncomputable section

theorem exists_polynomial_antiderivative (p : ℝ[X]) : ∃ q : ℝ[X], derivative q = p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    exact ⟨a + b, by rw [derivative_add, ha, hb]⟩
  | monomial n a =>
    refine ⟨monomial (n + 1) (a / (n + 1)), ?_⟩
    rw [derivative_monomial, Nat.add_sub_cancel]
    congr 1
    have : (n : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp

theorem exists_centredPrimitive_poly (F : ℝ[X]) :
    ∃ G : ℝ[X], (∀ c, centredPrimitive F c = G.eval c) ∧
      derivative G = F - C (uniformMean F.eval) ∧ G.eval (-1) = 0 ∧ G.eval 1 = 0 := by
  obtain ⟨q, hq⟩ := exists_polynomial_antiderivative (F - C (uniformMean F.eval))
  have hprim : ∀ c, centredPrimitive F c = q.eval c - q.eval (-1) := by
    intro c
    unfold centredPrimitive
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt]
    · intro x _
      have := q.hasDerivAt x
      rwa [hq, eval_sub, eval_C] at this
    · exact (F.continuous.sub continuous_const).intervalIntegrable _ _
  refine ⟨q - C (q.eval (-1)), fun c => by rw [hprim]; simp, by simp [hq], by simp, ?_⟩
  have h1 := hprim 1
  unfold centredPrimitive at h1
  rw [intervalIntegral.integral_sub (F.continuous.intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_const] at h1
  simp only [eval_sub, eval_C]
  rw [← h1]
  unfold uniformMean
  simp only [smul_eq_mul]
  ring

theorem exists_eq_sq_sub_one_mul (G : ℝ[X]) (hm : G.eval (-1) = 0) (hp : G.eval 1 = 0) :
    ∃ w : ℝ[X], G = (X ^ 2 - C 1) * w := by
  have h1 : (X - C 1) * (G /ₘ (X - C 1)) = G := mul_divByMonic_eq_iff_isRoot.mpr hp
  have hq : (G /ₘ (X - C 1)).IsRoot (-1) := by
    have h := congrArg (eval (-1)) h1
    rw [eval_mul, hm, eval_sub, eval_X, eval_C] at h
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  have h2 : (X - C (-1)) * ((G /ₘ (X - C 1)) /ₘ (X - C (-1))) = G /ₘ (X - C 1) :=
    mul_divByMonic_eq_iff_isRoot.mpr hq
  refine ⟨(G /ₘ (X - C 1)) /ₘ (X - C (-1)), ?_⟩
  conv_lhs => rw [← h1, ← h2]
  simp only [map_neg, map_one]
  ring

theorem zonalKernel_of_le {x y : ℝ} (hx : -1 < x) (hy : y < 1) (hyx : y ≤ x) :
    zonalKernel x y = (1 / 2) * Real.log (1 + x) + (1 / 2) * Real.log (1 - y) - Real.log 2 := by
  have h1 : (0 : ℝ) < 1 + x := by linarith
  have h2 : (0 : ℝ) < 1 - y := by linarith
  unfold zonalKernel
  rw [max_eq_left hyx, min_eq_right hyx, Real.log_div (mul_pos h1 h2).ne' (by norm_num),
    Real.log_mul h1.ne' h2.ne']
  have : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [this]
  ring

theorem zonalKernel_of_ge {x y : ℝ} (hx : x < 1) (hy : -1 < y) (hxy : x ≤ y) :
    zonalKernel x y = (1 / 2) * Real.log (1 + y) + (1 / 2) * Real.log (1 - x) - Real.log 2 := by
  have h1 : (0 : ℝ) < 1 + y := by linarith
  have h2 : (0 : ℝ) < 1 - x := by linarith
  unfold zonalKernel
  rw [max_eq_right hxy, min_eq_left hxy, Real.log_div (mul_pos h1 h2).ne' (by norm_num),
    Real.log_mul h1.ne' h2.ne']
  have : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [this]
  ring

theorem continuousOn_zonalKernel_mul_eval {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (H : ℝ[X]) :
    ContinuousOn (fun y => zonalKernel x y * H.eval y) (Icc (-1) 1) := by
  apply ContinuousOn.mul _ H.continuous.continuousOn
  unfold zonalKernel
  apply ContinuousOn.mul continuousOn_const
  apply ContinuousOn.log (by fun_prop)
  intro y _
  have h1 : 0 < 1 + max x y := by linarith [le_max_left x y, hx.1]
  have h2 : 0 < 1 - min x y := by linarith [min_le_left x y, hx.2]
  exact (div_pos (mul_pos h1 h2) (by norm_num)).ne'

theorem integral_zonalKernel_mul_eval (H w ρ σ : ℝ[X]) (e : ℝ)
    (hw : derivative ((X ^ 2 - C 1) * w) = H - C e)
    (hρ : derivative ρ = -((X + C 1) * w)) (hσ : derivative σ = (C 1 - X) * w)
    {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    ∫ y in (-1 : ℝ)..1, zonalKernel x y * H.eval y =
      -e + (1 / 2) * (ρ.eval x - ρ.eval (-1) - σ.eval x + σ.eval 1) := by
  obtain ⟨hx1, hx2⟩ := hx
  have hcont := continuousOn_zonalKernel_mul_eval ⟨hx1, hx2⟩ H
  have hint1 : IntervalIntegrable (fun y => zonalKernel x y * H.eval y) volume (-1) x :=
    (hcont.mono (by rw [uIcc_of_le hx1.le]; exact Icc_subset_Icc le_rfl hx2.le)).intervalIntegrable
  have hint2 : IntervalIntegrable (fun y => zonalKernel x y * H.eval y) volume x 1 :=
    (hcont.mono (by rw [uIcc_of_le hx2.le]; exact Icc_subset_Icc hx1.le le_rfl)).intervalIntegrable
  set Γ : ℝ[X] := (X ^ 2 - C 1) * w with hΓ
  have hΓe : ∀ y, Γ.eval y = (y ^ 2 - 1) * w.eval y := fun y => by simp [hΓ]
  rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
  have h1 : ∫ y in (-1 : ℝ)..x, zonalKernel x y * H.eval y =
      (((1 / 2) * Real.log (1 + x) - Real.log 2 + (1 / 2) * Real.log (1 - x)) *
          (Γ.eval x + e * (1 + x)) + (1 / 2) * (ρ.eval x - e * x - 2 * e * Real.log (1 - x))) -
      (((1 / 2) * Real.log (1 + x) - Real.log 2 + (1 / 2) * Real.log (1 - -1)) *
          (Γ.eval (-1) + e * (1 + -1)) +
        (1 / 2) * (ρ.eval (-1) - e * (-1) - 2 * e * Real.log (1 - -1))) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y =>
      ((1 / 2) * Real.log (1 + x) - Real.log 2 + (1 / 2) * Real.log (1 - y)) *
          (Γ.eval y + e * (1 + y)) + (1 / 2) * (ρ.eval y - e * y - 2 * e * Real.log (1 - y)))
      ?_ hint1
    intro y hy
    rw [uIcc_of_le hx1.le] at hy
    obtain ⟨hy1, hy2⟩ := hy
    have hy3 : 0 < 1 - y := by linarith
    have hL : HasDerivAt (fun y => Real.log (1 - y)) (-1 / (1 - y)) y := by
      exact ((hasDerivAt_id y).const_sub 1).log hy3.ne'
    have hk : HasDerivAt (fun y => (1 / 2) * Real.log (1 + x) - Real.log 2 +
        (1 / 2) * Real.log (1 - y)) ((1 / 2) * (-1 / (1 - y))) y :=
      (hL.const_mul (1 / 2)).const_add _
    have hP : HasDerivAt (fun y => Γ.eval y + e * (1 + y)) (Γ.derivative.eval y + e * 1) y :=
      (Γ.hasDerivAt y).add (((hasDerivAt_id y).const_add 1).const_mul e)
    have hQ : HasDerivAt (fun y => (1 / 2) * (ρ.eval y - e * y - 2 * e * Real.log (1 - y)))
        ((1 / 2) * (ρ.derivative.eval y - e * 1 - 2 * e * (-1 / (1 - y)))) y :=
      (((ρ.hasDerivAt y).sub ((hasDerivAt_id y).const_mul e)).sub (hL.const_mul (2 * e))).const_mul
        (1 / 2)
    refine ((hk.mul hP).add hQ).congr_deriv ?_
    rw [zonalKernel_of_le hx1 (by linarith) hy2, hw, hρ]
    simp only [eval_sub, eval_neg, eval_mul, eval_add, eval_C, eval_X, hΓe]
    field_simp
    ring
  have h2 : ∫ y in x..1, zonalKernel x y * H.eval y =
      (-(((1 / 2) * Real.log (1 - x) - Real.log 2 + (1 / 2) * Real.log (1 + 1)) *
          (-Γ.eval 1 + e * (1 - 1))) +
        (1 / 2) * (σ.eval 1 + 2 * e * Real.log (1 + 1) - e * 1)) -
      (-(((1 / 2) * Real.log (1 - x) - Real.log 2 + (1 / 2) * Real.log (1 + x)) *
          (-Γ.eval x + e * (1 - x))) +
        (1 / 2) * (σ.eval x + 2 * e * Real.log (1 + x) - e * x)) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y =>
      -(((1 / 2) * Real.log (1 - x) - Real.log 2 + (1 / 2) * Real.log (1 + y)) *
          (-Γ.eval y + e * (1 - y))) + (1 / 2) * (σ.eval y + 2 * e * Real.log (1 + y) - e * y))
      ?_ hint2
    intro y hy
    rw [uIcc_of_le hx2.le] at hy
    obtain ⟨hy1, hy2⟩ := hy
    have hy3 : 0 < 1 + y := by linarith
    have hL : HasDerivAt (fun y => Real.log (1 + y)) (1 / (1 + y)) y := by
      exact ((hasDerivAt_id y).const_add 1).log hy3.ne'
    have hk : HasDerivAt (fun y => (1 / 2) * Real.log (1 - x) - Real.log 2 +
        (1 / 2) * Real.log (1 + y)) ((1 / 2) * (1 / (1 + y))) y :=
      (hL.const_mul (1 / 2)).const_add _
    have hP : HasDerivAt (fun y => -Γ.eval y + e * (1 - y)) (-Γ.derivative.eval y + e * (-1)) y :=
      (Γ.hasDerivAt y).neg.add (((hasDerivAt_id y).const_sub 1).const_mul e)
    have hQ : HasDerivAt (fun y => (1 / 2) * (σ.eval y + 2 * e * Real.log (1 + y) - e * y))
        ((1 / 2) * (σ.derivative.eval y + 2 * e * (1 / (1 + y)) - e * 1)) y :=
      (((σ.hasDerivAt y).add (hL.const_mul (2 * e))).sub ((hasDerivAt_id y).const_mul e)).const_mul
        (1 / 2)
    refine ((hk.mul hP).neg.add hQ).congr_deriv ?_
    rw [zonalKernel_of_ge hx2 (by linarith) hy1, hw, hσ]
    simp only [eval_sub, eval_mul, eval_C, eval_X, hΓe]
    field_simp
    ring
  rw [h1, h2]
  simp only [hΓe]
  norm_num
  ring

end

end GroundTheory.Heights₂.Heights.FlagBundles
