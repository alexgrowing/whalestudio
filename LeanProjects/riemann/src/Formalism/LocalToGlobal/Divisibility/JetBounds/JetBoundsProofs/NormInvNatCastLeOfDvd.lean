import Formalism.LocalToGlobal.Divisibility.JetBounds.Statement

open Module NumberField IsDedekindDomain
open scoped BigOperators

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.DworkPowerSeriesWeights Formalism.DworkPowerSeriesWeights.OddLevelGainBounds Formalism.IncomingBounds

theorem embedding_lower_bound : EmbLower := by
  intro K _ _ _ w l _ ι hι a s ha h
  have h0 := norm_l_pos l
  have h1 := norm_l_lt_one l
  rw [hι a ha, Real.rpow_le_rpow_left_iff_of_base_lt_one h0 h1] at h
  have hr : (1 : ℤ) ≤ ramw w := (Formalism.EigenvalueLevelCeiling.ramBasic K w).2.1
  have hr' : (0 : ℝ) < (ramw w : ℝ) := by
    have : (0 : ℤ) < ramw w := by omega
    exact_mod_cast this
  rw [le_div_iff₀ hr'] at h
  linarith

theorem embeddingIntegral_holds : EmbInt := by
  intro K _ _ _ w l _ ι hι a ha
  by_cases h : a = 0
  · rw [h, map_zero, norm_zero]
    exact zero_le_one
  · have hv : 0 ≤ vw w a := ha.resolve_left h
    have hr : (1 : ℤ) ≤ ramw w := (Formalism.EigenvalueLevelCeiling.ramBasic K w).2.1
    have hr' : (0 : ℝ) ≤ (ramw w : ℝ) := by
      have : (0 : ℤ) ≤ ramw w := by omega
      exact_mod_cast this
    have hv' : (0 : ℝ) ≤ (vw w a : ℝ) := by exact_mod_cast hv
    rw [hι a h]
    exact Real.rpow_le_one (norm_l_pos l).le (norm_l_lt_one l).le (div_nonneg hv' hr')

theorem norm_inv_natCast_le_of_dvd (l : ℕ) [hl : Fact l.Prime] {c D : ℕ} (hD : D ≠ 0) (hc : c ∣ D) :
    ‖((c : ℕ) : ℂ_[l])⁻¹‖ ≤ ‖(l : ℂ_[l])‖ ^ (-(padicValNat l D : ℝ)) := by
  have h0 := norm_l_pos l
  have h1 := norm_l_lt_one l
  have hc0 : c ≠ 0 := fun h => hD (by rw [h] at hc; exact Nat.eq_zero_of_zero_dvd hc)
  have hle : padicValNat l c ≤ padicValNat l D :=
    (padicValNat_dvd_iff_le hD).1 (dvd_trans pow_padicValNat_dvd hc)
  rw [norm_inv, norm_natCast_eq_pow_padicValNat hl.out h1 hc0, Real.rpow_neg h0.le, Real.rpow_natCast]
  exact inv_anti₀ (pow_pos h0 _) (pow_le_pow_of_le_one h0.le h1.le hle)

theorem path_height_bound : PathBound := by
  intro K _ l hl J A B _ _ _ _ _ X ι D j1 s φ F hx hy hr he hS hE
  classical
  obtain ⟨hD, hg, hgP, hg1⟩ := hS
  have h0 := norm_l_pos l
  have h1 := norm_l_lt_one l
  set p : ℝ := ‖(l : ℂ_[l])‖ with hp
  set v : ℝ := (padicValNat l D : ℝ) with hv
  unfold PathData.val
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_nonneg h0.le _) ?_
  intro π _

  have hfac : ∀ j, ‖(((X.gam π j : ℕ) : ℂ_[l])⁻¹ * X.eps π j * X.e π j)‖ ≤
      p ^ (s j - v) * (if j = j1 then p ^ v else 1) := by
    intro j
    rw [norm_mul, norm_mul]
    have hs0 : 0 ≤ p ^ (s j) := Real.rpow_nonneg h0.le _
    by_cases hj : j = j1
    · rw [if_pos hj, ← Real.rpow_add h0, sub_add_cancel]
      have : X.gam π j = 1 := by rw [hj]; exact hg1 π
      rw [this, Nat.cast_one, inv_one, norm_one, one_mul]
      calc ‖X.eps π j‖ * ‖X.e π j‖ ≤ 1 * p ^ (s j) :=
            mul_le_mul (he π j) (hE π j) (norm_nonneg _) zero_le_one
        _ = p ^ (s j) := one_mul _
    · rw [if_neg hj, mul_one, sub_eq_add_neg, Real.rpow_add h0]
      have hi := norm_inv_natCast_le_of_dvd l hD (hg π j)
      have hv0 : 0 ≤ p ^ (-v) := Real.rpow_nonneg h0.le _
      calc ‖((X.gam π j : ℕ) : ℂ_[l])⁻¹‖ * ‖X.eps π j‖ * ‖X.e π j‖ ≤ p ^ (-v) * 1 * p ^ (s j) :=
            mul_le_mul (mul_le_mul hi (he π j) (norm_nonneg _) hv0) (hE π j) (norm_nonneg _)
              (by rw [mul_one]; exact hv0)
        _ = p ^ (s j) * p ^ (-v) := by ring
  have hprod : ‖∏ j : J, (((X.gam π j : ℕ) : ℂ_[l])⁻¹ * X.eps π j * X.e π j)‖ ≤
      p ^ (∑ j, (s j - v)) * p ^ v := by
    rw [norm_prod, Real.rpow_sum_of_pos h0]
    calc ∏ j : J, ‖(((X.gam π j : ℕ) : ℂ_[l])⁻¹ * X.eps π j * X.e π j)‖
        ≤ ∏ j : J, (p ^ (s j - v) * (if j = j1 then p ^ v else 1)) :=
          Finset.prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => hfac j)
      _ = (∏ j : J, p ^ (s j - v)) * p ^ v := by
          rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ j1 (fun _ => p ^ v),
            if_pos (Finset.mem_univ _)]
  have hiP := norm_inv_natCast_le_of_dvd l hD (hgP π)
  have hS0 : 0 ≤ p ^ (∑ j, (s j - v)) * p ^ v :=
    mul_nonneg (Real.rpow_nonneg h0.le _) (Real.rpow_nonneg h0.le _)
  have hv0 : 0 ≤ p ^ (-v) := Real.rpow_nonneg h0.le _
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  calc ‖ι (X.x π φ)‖ * ‖∏ j : J, (((X.gam π j : ℕ) : ℂ_[l])⁻¹ * X.eps π j * X.e π j)‖ * ‖X.r π‖ *
        (‖((X.gamP π : ℕ) : ℂ_[l])⁻¹‖ * ‖ι (X.y π F)‖)
      ≤ 1 * (p ^ (∑ j, (s j - v)) * p ^ v) * 1 * (p ^ (-v) * 1) := by
        refine mul_le_mul (mul_le_mul (mul_le_mul (hx π) hprod (norm_nonneg _) zero_le_one) (hr π)
          (norm_nonneg _) (by rw [one_mul]; exact hS0))
          (mul_le_mul hiP (hy π) (norm_nonneg _) hv0)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by rw [one_mul, mul_one]; exact hS0)
    _ = p ^ (∑ j, (s j - v)) * (p ^ v * p ^ (-v)) := by ring
    _ = p ^ (∑ j, (s j - v)) := by
        rw [← Real.rpow_add h0, add_neg_cancel, Real.rpow_zero, mul_one]

end Formalism.L2.DIV
