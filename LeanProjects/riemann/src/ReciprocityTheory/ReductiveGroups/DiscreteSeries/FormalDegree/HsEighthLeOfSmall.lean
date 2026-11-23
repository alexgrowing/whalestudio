import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.SCoefGeTwoOfHc

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem pmat_smul {ε : Fin n → Bool} (c : ℝ) (z : PCoord ε → ℂ) :
    pmat (c • z) = (c : ℂ) • pmat z := by
  ext a b
  simp only [pmat, Pi.smul_apply, Matrix.smul_apply]
  split_ifs <;> simp [Complex.real_smul]

theorem hs_pmat_smul {ε : Fin n → Bool} (c : ℝ) (z : PCoord ε → ℂ) :
    hs (pmat (c • z)) = c ^ 2 * hs (pmat z) := by
  rw [hs_pmat, hs_pmat, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ab _ => ?_
  rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem hs_half_le_quadratic {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    hs (pmat z) / 2 ≤ Qf (0 : Fin n → ℝ) z := by
  have e : hs (pmat z) / 2 = ∑ ab, ‖z ab‖ ^ 2 := by rw [hs_pmat]; ring
  rw [e, Qf]
  refine Finset.sum_le_sum fun ab _ => ?_
  have hv : ((ab.1.2 : ℕ) : ℝ) + 1 ≤ ((ab.1.1 : ℕ) : ℝ) := by exact_mod_cast Fin.lt_def.mp ab.2.1
  have hw : 1 ≤ wab (0 : Fin n → ℝ) ab.1.1 ab.1.2 := by simp only [wab, Pi.zero_apply]; linarith
  exact le_mul_of_one_le_left (by positivity) hw

theorem hs_eighth_le_of_small {ε : Fin n → Bool} (z : PCoord ε → ℂ) (h : rhoP z ≤ 1 / 2) :
    hs (pmat z) / 8 ≤ Ph (0 : Fin n → ℝ) (pmat z) := by
  have hA : Antitone (0 : Fin n → ℝ) := fun _ _ _ => le_rfl
  have h1 := ph_lower hA z h (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have h2 := hs_half_le_quadratic z
  linarith

theorem potential_lower_min {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    1 / 16 * min (hs (pmat z)) (Real.sqrt (hs (pmat z)) / Real.sqrt (2 * (q0 ε : ℝ))) ≤
      Ph (0 : Fin n → ℝ) (pmat z) := by
  have hA : Antitone (0 : Fin n → ℝ) := fun _ _ _ => le_rfl
  have hH0 : 0 ≤ hs (pmat z) := by rw [hs_pmat]; positivity
  have hP0 := ph_nonneg hA z
  rcases Nat.eq_zero_or_pos (q0 ε) with hq | hq
  · have e : min (hs (pmat z)) (Real.sqrt (hs (pmat z)) / Real.sqrt (2 * (q0 ε : ℝ))) = 0 := by
      rw [hq]; simp [hH0]
    rw [e]; linarith
  · set c := Real.sqrt (2 * (q0 ε : ℝ)) with hc
    have hq1 : (1 : ℝ) ≤ (q0 ε : ℝ) := by exact_mod_cast hq
    have hc0 : 0 < c := Real.sqrt_pos.mpr (by linarith)
    set r := Real.sqrt (hs (pmat z)) with hr
    have hrr : r ^ 2 = hs (pmat z) := Real.sq_sqrt hH0
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    have hrho : rhoP z = c * r := rfl
    by_cases hsm : c * r ≤ 1 / 2
    · have := hs_eighth_le_of_small z (by rw [hrho]; exact hsm)
      have hm := min_le_left (hs (pmat z)) (r / c)
      nlinarith
    · replace hsm := lt_of_not_ge hsm
      have hrp : 0 < r := by
        by_contra h0
        have : r = 0 := le_antisymm (not_lt.mp h0) hr0
        rw [this, mul_zero] at hsm; linarith
      set t := 2 * c * r with ht
      have ht1 : 1 ≤ t := by rw [ht]; linarith
      have ht0 : 0 < t := by linarith
      set z' := (1 / t) • z with hz'
      have hpz : pmat z = (t : ℂ) • pmat z' := by
        rw [hz', pmat_smul, smul_smul, ← Complex.ofReal_mul, mul_one_div_cancel ht0.ne',
          Complex.ofReal_one, one_smul]
      have hhs : hs (pmat z') = (1 / t) ^ 2 * r ^ 2 := by rw [hz', hs_pmat_smul, hrr]
      have hsq : Real.sqrt (hs (pmat z')) = 1 / t * r := by
        rw [hhs, ← mul_pow, Real.sqrt_sq (by positivity)]
      have hrho' : rhoP z' ≤ 1 / 2 := by
        have e2 : rhoP z' = c * Real.sqrt (hs (pmat z')) := rfl
        rw [e2, hsq, ht]
        field_simp
        linarith
      have hsm' := hs_eighth_le_of_small z' hrho'
      have hsc := ph_scale hA z' ht1
      rw [← hpz] at hsc
      have hm := min_le_right (hs (pmat z)) (r / c)
      have key : 1 / 16 * (r / c) ≤ t * (hs (pmat z') / 8) := by
        rw [hhs, ht]
        field_simp
        nlinarith
      have := mul_le_mul_of_nonneg_left hsm' ht0.le
      nlinarith

end ReciprocityTheory.ChartRestriction.DS
