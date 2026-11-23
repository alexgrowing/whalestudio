import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.LogEtaStatement
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open Filter Topology Complex
open scoped Real UpperHalfPlane ModularForm

noncomputable section

theorem LogEta.proof : LogEta.Statement := by
  intro τ
  set q : ℂ := Complex.exp (2 * π * Complex.I * (τ : ℂ)) with hq
  have hq1 : ‖q‖ < 1 := UpperHalfPlane.norm_exp_two_pi_I_lt_one τ
  have hr0 : 0 ≤ ‖q‖ := norm_nonneg _
  have hpow : ∀ k : ℕ, ‖q ^ (k + 1)‖ < 1 := fun k ↦ by
    rw [norm_pow]; exact pow_lt_one₀ hr0 hq1 (Nat.succ_ne_zero k)

  let F : ℕ × ℕ → ℂ := fun p ↦ ((1 / (p.1 + 1 : ℝ) : ℝ) : ℂ) * q ^ ((p.1 + 1) * (p.2 + 1))
  have hFs : Summable F := by
    refine Summable.of_norm_bounded (g := fun p : ℕ × ℕ ↦ ‖q‖ ^ p.1 * ‖q‖ ^ p.2)
      (Summable.mul_of_nonneg (summable_geometric_of_lt_one hr0 hq1)
        (summable_geometric_of_lt_one hr0 hq1) (fun _ ↦ pow_nonneg hr0 _)
        (fun _ ↦ pow_nonneg hr0 _)) ?_
    rintro ⟨m, k⟩
    simp only [F, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    rw [← pow_add]
    have h1 : |1 / ((m : ℝ) + 1)| ≤ 1 := by
      rw [abs_of_pos (by positivity)]
      exact div_le_one_of_le₀ (by linarith [m.cast_nonneg (α := ℝ)]) (by positivity)
    have h2 : ‖q‖ ^ ((m + 1) * (k + 1)) ≤ ‖q‖ ^ (m + k) :=
      pow_le_pow_of_le_one hr0 hq1.le (by nlinarith)
    calc _ ≤ 1 * ‖q‖ ^ (m + k) := mul_le_mul h1 h2 (pow_nonneg hr0 _) zero_le_one
      _ = _ := one_mul _
  set T := ∑' p, F p

  have hA : HasSum (fun m : ℕ ↦ ∑' k : ℕ, F (m, k)) T :=
    hFs.hasSum.prod_fiberwise fun m ↦ (hFs.prod_factor m).hasSum

  have hcol : ∀ k : ℕ, HasSum (fun m : ℕ ↦ F (m, k)) (-Complex.log (1 - q ^ (k + 1))) := by
    intro k
    convert hasSum_taylorSeries_neg_log' (hpow k) using 1
    ext m
    simp only [F]
    rw [← pow_mul, mul_comm (k + 1)]
    push_cast
    ring
  have hB : HasSum (fun k : ℕ ↦ -Complex.log (1 - q ^ (k + 1))) T := by
    have hsw : HasSum (F ∘ Prod.swap) T :=
      (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hFs.hasSum
    exact hsw.prod_fiberwise fun k ↦ hcol k

  have hne : ∀ k : ℕ, 1 - q ^ (k + 1) ≠ 0 := fun k ↦
    sub_ne_zero.mpr (ne_of_apply_ne norm (by rw [norm_one]; exact (hpow k).ne)).symm
  have hlog : HasSum (fun k : ℕ ↦ Real.log ‖1 - q ^ (k + 1)‖) (-T.re) := by
    have := (Complex.hasSum_re hB).neg
    simpa only [neg_re, Complex.log_re, neg_neg] using this
  have hprod : HasProd (fun k : ℕ ↦ ‖1 - q ^ (k + 1)‖) (Real.exp (-T.re)) := by
    convert hlog.rexp using 1
    ext k
    simp only [Function.comp_apply]
    rw [Real.exp_log (norm_pos_iff.mpr (hne k))]
  have hnorm : ‖∏' k : ℕ, (1 - q ^ (k + 1))‖ = Real.exp (-T.re) :=
    (ModularForm.multipliable_one_sub_pow hq1).hasProd.norm.unique hprod
  have heta : ‖η (τ : ℂ)‖ = Real.exp (-2 * π * (τ : ℂ).im / 24) * Real.exp (-T.re) := by
    rw [ModularForm.eta, norm_mul, Function.Periodic.norm_qParam, ← hnorm]
    congr 2
    refine tprod_congr fun n ↦ ?_
    rw [ModularForm.eta_q_eq_pow]
  have hlogeta : Real.log ‖η (τ : ℂ)‖ = -2 * π * τ.im / 24 - T.re := by
    rw [heta, ← Real.exp_add, Real.log_exp, UpperHalfPlane.coe_im]
    ring
  rw [hlogeta]
  convert Complex.hasSum_re hA using 1
  · ext m
    simp only [F]
    rw [tsum_mul_left, re_ofReal_mul]
  · ring

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
