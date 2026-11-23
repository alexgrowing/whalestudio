import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ResidueLatticeCount.HeckeLower

namespace PI.Residue

theorem third_le_log : (1 : ℝ) / 3 ≤ Real.log (3 / 2) := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h3 : Real.exp (1 / 3) ^ 3 ≤ (3 / 2 : ℝ) ^ 3 := by
    rw [← Real.exp_nat_mul]
    have : ((3 : ℕ) : ℝ) * (1 / 3) = 1 := by norm_num
    rw [this]
    have := Real.exp_one_lt_d9
    norm_num at this ⊢
    linarith
  exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) h3

theorem pow_le_lower (m : ℕ) (hm : 2 ≤ m) :
    (3 / 2 : ℝ) ^ m ≤ 4 / 9 * (3 * Real.pi / 4) ^ m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hpi := Real.pi_gt_three
  have h1 : (3 / 2 : ℝ) ^ k ≤ (3 * Real.pi / 4) ^ k :=
    pow_le_pow_left₀ (by norm_num) (by linarith) k
  have h2 : (3 / 2 : ℝ) ^ 2 ≤ 4 / 9 * (3 * Real.pi / 4) ^ 2 := by nlinarith
  have h3 : (0 : ℝ) ≤ (3 / 2 : ℝ) ^ k := by positivity
  have h4 : (0 : ℝ) ≤ 4 / 9 * (3 * Real.pi / 4) ^ 2 := by positivity
  calc (3 / 2 : ℝ) ^ (2 + k) = (3 / 2 : ℝ) ^ 2 * (3 / 2 : ℝ) ^ k := pow_add _ _ _
    _ ≤ (4 / 9 * (3 * Real.pi / 4) ^ 2) * (3 * Real.pi / 4) ^ k := mul_le_mul h2 h1 h3 h4
    _ = 4 / 9 * (3 * Real.pi / 4) ^ (2 + k) := by rw [pow_add]; ring

theorem optimise : Optimise := by
  refine ⟨128 * Real.pi * Real.exp (1 / 2), ?_, ?_⟩
  · have hpi := Real.pi_gt_three
    have he : 1 ≤ Real.exp (1 / 2) := Real.one_le_exp (by norm_num)
    nlinarith
  intro m D hm hD
  have hm0 : (0 : ℝ) < m := by
    have : 0 < m := by omega
    exact_mod_cast this
  have hD1 : (3 / 2 : ℝ) ^ m ≤ D := (pow_le_lower m hm).trans hD
  have hDpos : 0 < D := lt_of_lt_of_le (by positivity) hD1
  set l : ℝ := Real.log (D ^ ((1 : ℝ) / m)) with hl
  have hlD : Real.log D = m * l := by
    rw [hl, Real.log_rpow hDpos]
    field_simp
  have hl3 : 1 / 3 ≤ l := by
    have h1 : Real.log ((3 / 2 : ℝ) ^ m) ≤ Real.log D := Real.log_le_log (by positivity) hD1
    rw [Real.log_pow, hlD] at h1
    have h2 : Real.log (3 / 2) ≤ l := le_of_mul_le_mul_left h1 hm0
    exact third_le_log.trans h2
  have hlpos : 0 < l := by linarith
  refine ⟨1 + 1 / l, by linarith [one_div_pos.mpr hlpos], ?_⟩
  have e1 : (1 + 1 / l - 1) = 1 / l := by ring
  rw [e1, one_div_one_div]

  have hDexp : D ^ (1 / l / 2) = Real.exp (1 / 2) ^ m := by
    rw [← Real.exp_nat_mul, Real.rpow_def_of_pos hDpos, hlD]
    congr 1
    field_simp

  have h4 : (4 : ℝ) ^ (1 + 1 / l) ≤ 16 ^ m := by
    have hle : 1 + 1 / l ≤ 4 := by
      have : 1 / l ≤ 3 := by
        rw [div_le_iff₀ hlpos]
        linarith
      linarith
    calc (4 : ℝ) ^ (1 + 1 / l) ≤ (4 : ℝ) ^ (4 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hle
      _ = 16 ^ 2 := by
          rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          norm_num
      _ ≤ 16 ^ m := pow_le_pow_right₀ (by norm_num) hm
  have h5 : (1 + l) ^ m ≤ (4 * l) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
  rw [hDexp]
  have hpi : 0 < Real.pi := Real.pi_pos
  calc (4 : ℝ) ^ (1 + 1 / l) * (2 * Real.pi) ^ m * Real.exp (1 / 2) ^ m * (1 + l) ^ m
      ≤ 16 ^ m * (2 * Real.pi) ^ m * Real.exp (1 / 2) ^ m * (4 * l) ^ m := by
        gcongr
    _ = (128 * Real.pi * Real.exp (1 / 2) * l) ^ m := by
        rw [← mul_pow, ← mul_pow, ← mul_pow]
        congr 1
        ring

end PI.Residue
