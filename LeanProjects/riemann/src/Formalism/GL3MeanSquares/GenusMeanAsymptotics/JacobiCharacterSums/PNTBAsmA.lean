import Mathlib

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

theorem num_alg (M y C D Pt t lg lm : ℝ) (hM : 1 ≤ M) (hy : M ^ 5 ≤ y) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hPt : Pt ≤ (M ^ 8)⁻¹) (ht : t ≤ (M ^ 2)⁻¹) (hlg : lg ≤ D * M ^ 2)
    (hlm0 : 0 ≤ lm) (hlm : lm ≤ 13 * M) :
    M * (4 * y * (C * (Pt + lg * lm ^ 2 / M ^ 12)) / (M ^ 5)⁻¹ + 4 * ((M ^ 5)⁻¹ * y + 1) * lg)
        + 20 * (M ^ 5)⁻¹ * y + 2 * y * t ≤ (4 * C + 676 * C * D + 8 * D + 22) * y * (M ^ 2)⁻¹ := by
  have hM0 : 0 < M := by linarith
  have hy0 : 0 ≤ y := le_trans (by positivity) hy
  have hA : M ^ 6 * Pt ≤ (M ^ 2)⁻¹ := by
    calc M ^ 6 * Pt ≤ M ^ 6 * (M ^ 8)⁻¹ := mul_le_mul_of_nonneg_left hPt (by positivity)
      _ = (M ^ 2)⁻¹ := by field_simp
  have hB : lg * lm ^ 2 / M ^ 6 ≤ 169 * D * (M ^ 2)⁻¹ := by
    have hlm2 : lm ^ 2 ≤ 169 * M ^ 2 := by nlinarith
    have h2 : lg * lm ^ 2 ≤ D * M ^ 2 * (169 * M ^ 2) :=
      calc lg * lm ^ 2 ≤ D * M ^ 2 * lm ^ 2 := mul_le_mul_of_nonneg_right hlg (sq_nonneg _)
        _ ≤ D * M ^ 2 * (169 * M ^ 2) := mul_le_mul_of_nonneg_left hlm2 (by positivity)
    calc lg * lm ^ 2 / M ^ 6 ≤ D * M ^ 2 * (169 * M ^ 2) / M ^ 6 :=
          div_le_div_of_nonneg_right h2 (by positivity)
      _ = 169 * D * (M ^ 2)⁻¹ := by field_simp <;> ring
  have e1 : M * (4 * y * (C * (Pt + lg * lm ^ 2 / M ^ 12)) / (M ^ 5)⁻¹)
      = 4 * C * y * (M ^ 6 * Pt + lg * lm ^ 2 / M ^ 6) := by
    field_simp <;> ring
  have h1 : M * (4 * y * (C * (Pt + lg * lm ^ 2 / M ^ 12)) / (M ^ 5)⁻¹)
      ≤ 4 * C * y * ((M ^ 2)⁻¹ + 169 * D * (M ^ 2)⁻¹) := by
    rw [e1]; exact mul_le_mul_of_nonneg_left (add_le_add hA hB) (by positivity)
  have hM3 : M ^ 3 ≤ y * (M ^ 2)⁻¹ := by
    rw [le_mul_inv_iff₀ (by positivity)]; calc M ^ 3 * M ^ 2 = M ^ 5 := by ring
      _ ≤ y := hy
  have h2 : M * (4 * ((M ^ 5)⁻¹ * y + 1) * lg) ≤ 8 * D * y * (M ^ 2)⁻¹ := by
    have hc : 0 ≤ 4 * M * ((M ^ 5)⁻¹ * y + 1) := by positivity
    calc M * (4 * ((M ^ 5)⁻¹ * y + 1) * lg) = 4 * M * ((M ^ 5)⁻¹ * y + 1) * lg := by ring
      _ ≤ 4 * M * ((M ^ 5)⁻¹ * y + 1) * (D * M ^ 2) := mul_le_mul_of_nonneg_left hlg hc
      _ = 4 * D * (y * (M ^ 2)⁻¹ + M ^ 3) := by field_simp <;> ring
      _ ≤ 4 * D * (y * (M ^ 2)⁻¹ + y * (M ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 8 * D * y * (M ^ 2)⁻¹ := by ring
  have h5 : (M ^ 5)⁻¹ ≤ (M ^ 2)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_right₀ hM (by norm_num))
  have h3 : 20 * (M ^ 5)⁻¹ * y ≤ 20 * (M ^ 2)⁻¹ * y := by
    have := mul_le_mul_of_nonneg_right h5 hy0; linarith
  have h4 : 2 * y * t ≤ 2 * y * (M ^ 2)⁻¹ := mul_le_mul_of_nonneg_left ht (by positivity)
  have e2 : M * (4 * y * (C * (Pt + lg * lm ^ 2 / M ^ 12)) / (M ^ 5)⁻¹ + 4 * ((M ^ 5)⁻¹ * y + 1) * lg)
      = M * (4 * y * (C * (Pt + lg * lm ^ 2 / M ^ 12)) / (M ^ 5)⁻¹)
        + M * (4 * ((M ^ 5)⁻¹ * y + 1) * lg) := by ring
  rw [e2]
  have e3 : (4 * C + 676 * C * D + 8 * D + 22) * y * (M ^ 2)⁻¹
      = 4 * C * y * ((M ^ 2)⁻¹ + 169 * D * (M ^ 2)⁻¹) + 8 * D * y * (M ^ 2)⁻¹
        + 20 * (M ^ 2)⁻¹ * y + 2 * y * (M ^ 2)⁻¹ := by ring
  rw [e3]
  linarith

theorem one_le_log_of_three_le {x : ℝ} (hx : 3 ≤ x) : 1 ≤ Real.log x := by
  have h3 : Real.exp 1 ≤ x := by linarith [Real.exp_one_lt_d9]
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log x := Real.log_le_log (Real.exp_pos 1) h3

theorem inv_pow_eq_exp {M : ℝ} (hM : 0 < M) (n : ℕ) : (M ^ n)⁻¹ = Real.exp (-(n * Real.log M)) := by
  rw [Real.exp_neg, ← Real.log_pow, Real.exp_log (pow_pos hM n)]

theorem logy_lt {cA M y : ℝ} (hcA : 0 < cA) (hy : 2 ≤ y)
    (h : cA * Real.sqrt (Real.log y) < Real.log M) : cA ^ 2 * Real.log y < Real.log M ^ 2 := by
  have hl : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hs := Real.sq_sqrt hl
  have h0 : 0 ≤ cA * Real.sqrt (Real.log y) := by positivity
  have h2 : (cA * Real.sqrt (Real.log y)) ^ 2 < Real.log M ^ 2 := by nlinarith
  calc cA ^ 2 * Real.log y = (cA * Real.sqrt (Real.log y)) ^ 2 := by rw [mul_pow, hs]
    _ < Real.log M ^ 2 := h2

theorem inv_le_exp {cA c M y : ℝ} (hcA : 0 < cA) (hc : 0 < c) (hc' : c ≤ cA ^ 2) (hM : 8 ≤ M) (hy : 2 ≤ y)
    (h : cA * Real.sqrt (Real.log y) < Real.log M) :
    M⁻¹ ≤ Real.exp (-(c * Real.log y / Real.log M)) := by
  have hM0 : 0 < M := by linarith
  have hlM : 0 < Real.log M := Real.log_pos (by linarith)
  have hly : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have h2 := logy_lt hcA hy h
  have h3 : c * Real.log y ≤ Real.log M ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hc' hly]
  have h4 : c * Real.log y / Real.log M ≤ Real.log M := by
    rw [div_le_iff₀ hlM]; nlinarith
  calc M⁻¹ = Real.exp (-Real.log M) := by rw [Real.exp_neg, Real.exp_log hM0]
    _ ≤ Real.exp (-(c * Real.log y / Real.log M)) := Real.exp_le_exp.mpr (by linarith)

theorem num_main (cA κ C : ℝ) (hcA : 0 < cA) (hκ : 0 < κ) (hC : 0 < C) :
    ∃ C₀ B : ℝ, 0 ≤ C₀ ∧ 0 ≤ B ∧ ∀ M y : ℝ, 8 ≤ M → 2 ≤ y →
      C₀ * Real.log M * Real.log (Real.log M + 2) ≤ Real.log y →
      cA * Real.sqrt (Real.log y) < Real.log M →
      M * (4 * y * (C * ((M * M ^ (12 : ℝ)) ^ C * y ^ (-(κ / 2))
          + Real.log (2 * y) * Real.log (M * M ^ (12 : ℝ)) ^ 2 / M ^ (12 : ℝ))) / (M ^ 5)⁻¹
          + 4 * ((M ^ 5)⁻¹ * y + 1) * Real.log (2 * y))
        + 20 * (M ^ 5)⁻¹ * y + 2 * y * y ^ (-(κ / 2)) ≤ B * y * (M⁻¹ * M⁻¹) := by
  set D : ℝ := 1 + (cA ^ 2)⁻¹ with hDdef
  have hD : 0 ≤ D := by positivity
  refine ⟨5 + (26 * C + 20) / κ, 4 * C + 676 * C * D + 8 * D + 22, by positivity, by positivity, ?_⟩
  intro M y hM hy hlog hsq
  have hM0 : 0 < M := by linarith
  have hy0 : 0 < y := by linarith
  have hL1 : 1 ≤ Real.log M := one_le_log_of_three_le (by linarith)
  have hl1 : 1 ≤ Real.log (Real.log M + 2) := one_le_log_of_three_le (by linarith)
  have hLM : Real.log M ≤ M := by linarith [Real.log_le_sub_one_of_pos hM0]
  have hC0 : 0 ≤ 5 + (26 * C + 20) / κ := by positivity
  have hlog' : (5 + (26 * C + 20) / κ) * Real.log M ≤ Real.log y := by
    have : (5 + (26 * C + 20) / κ) * Real.log M * 1
        ≤ (5 + (26 * C + 20) / κ) * Real.log M * Real.log (Real.log M + 2) :=
      mul_le_mul_of_nonneg_left hl1 (by positivity)
    linarith
  have hkC : κ * (5 + (26 * C + 20) / κ) = 5 * κ + (26 * C + 20) := by field_simp
  have hK : (26 * C + 20) * Real.log M ≤ κ * Real.log y := by
    have := mul_le_mul_of_nonneg_left hlog' hκ.le
    have h5 : 0 ≤ 5 * κ * Real.log M := by positivity
    nlinarith
  have hy5 : M ^ 5 ≤ y := by
    rw [← Real.log_le_log_iff (by positivity) hy0, Real.log_pow]
    have : 5 * Real.log M ≤ (5 + (26 * C + 20) / κ) * Real.log M := by
      have : 0 ≤ (26 * C + 20) / κ * Real.log M := by positivity
      nlinarith
    push_cast; linarith
  have h12 : M ^ (12 : ℝ) = M ^ 12 := by
    rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [h12]
  have hlm : Real.log (M * M ^ 12) = 13 * Real.log M := by
    rw [show M * M ^ 12 = M ^ 13 by ring, Real.log_pow]; push_cast; ring
  have hpow : (M * M ^ 12) ^ C = Real.exp (13 * C * Real.log M) := by
    rw [Real.rpow_def_of_pos (by positivity), hlm]; ring_nf
  have hyk : y ^ (-(κ / 2)) = Real.exp (-(κ / 2 * Real.log y)) := by
    rw [Real.rpow_def_of_pos hy0]; ring_nf
  have hPt : (M * M ^ 12) ^ C * y ^ (-(κ / 2)) ≤ (M ^ 8)⁻¹ := by
    rw [hpow, hyk, ← Real.exp_add, inv_pow_eq_exp hM0]
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith
  have ht : y ^ (-(κ / 2)) ≤ (M ^ 2)⁻¹ := by
    rw [hyk, inv_pow_eq_exp hM0]
    apply Real.exp_le_exp.mpr
    push_cast
    have : 0 ≤ 26 * C * Real.log M := by positivity
    nlinarith
  have hlg : Real.log (2 * y) ≤ D * M ^ 2 := by
    have hq := logy_lt hcA hy hsq
    have hq' : Real.log y ≤ Real.log M ^ 2 * (cA ^ 2)⁻¹ := by
      rw [le_mul_inv_iff₀ (by positivity)]; linarith
    have hLM2 : Real.log M ^ 2 ≤ M ^ 2 := by nlinarith
    have hq'' : Real.log M ^ 2 * (cA ^ 2)⁻¹ ≤ M ^ 2 * (cA ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_right hLM2 (by positivity)
    have h2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
    have hM1 : 1 ≤ M ^ 2 := by nlinarith
    rw [Real.log_mul (by norm_num) hy0.ne', hDdef]
    nlinarith
  have hlm0 : 0 ≤ Real.log (M * M ^ 12) := by rw [hlm]; linarith
  have hlm13 : Real.log (M * M ^ 12) ≤ 13 * M := by rw [hlm]; linarith
  have key := num_alg M y C D ((M * M ^ 12) ^ C * y ^ (-(κ / 2))) (y ^ (-(κ / 2)))
    (Real.log (2 * y)) (Real.log (M * M ^ 12)) (by linarith) hy5 hC.le hD hPt ht hlg hlm0 hlm13
  refine key.trans (le_of_eq ?_)
  ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions
