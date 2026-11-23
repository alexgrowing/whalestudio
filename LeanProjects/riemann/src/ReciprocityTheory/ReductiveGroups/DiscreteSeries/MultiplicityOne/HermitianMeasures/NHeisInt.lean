import Mathlib

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A

theorem heis_norm_sq_le (m : ℕ) (x : (Fin m → ℂ) × ℝ) :
    ‖x‖ ^ 2 ≤ ∑ i, Complex.normSq (x.1 i) + x.2 ^ 2 := by
  have hS : 0 ≤ ∑ i, Complex.normSq (x.1 i) :=
    Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hT : 0 ≤ ∑ i, Complex.normSq (x.1 i) + x.2 ^ 2 := by positivity
  have h1 : ‖x.1‖ ≤ Real.sqrt (∑ i, Complex.normSq (x.1 i) + x.2 ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 (fun i => ?_)
    calc ‖x.1 i‖ = Real.sqrt (‖x.1 i‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (∑ i, Complex.normSq (x.1 i) + x.2 ^ 2) := by
        apply Real.sqrt_le_sqrt
        have hi : Complex.normSq (x.1 i) ≤ ∑ j, Complex.normSq (x.1 j) :=
          Finset.single_le_sum (f := fun j => Complex.normSq (x.1 j))
            (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
        rw [← Complex.normSq_eq_norm_sq]
        nlinarith [sq_nonneg x.2]
  have h2 : ‖x.2‖ ≤ Real.sqrt (∑ i, Complex.normSq (x.1 i) + x.2 ^ 2) := by
    calc ‖x.2‖ = Real.sqrt (x.2 ^ 2) := by rw [Real.sqrt_sq_eq_abs, Real.norm_eq_abs]
      _ ≤ _ := Real.sqrt_le_sqrt (by linarith)
  have h3 : ‖x‖ ≤ Real.sqrt (∑ i, Complex.normSq (x.1 i) + x.2 ^ 2) := by
    rw [Prod.norm_def]; exact max_le h1 h2
  calc ‖x‖ ^ 2 ≤ (Real.sqrt (∑ i, Complex.normSq (x.1 i) + x.2 ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h3 2
    _ = _ := Real.sq_sqrt hT

theorem heis_pointwise (m : ℕ) {d : ℝ} (hd : 0 ≤ d) (x : (Fin m → ℂ) × ℝ) :
    (1 + ∑ i, Complex.normSq (x.1 i) + x.2 ^ 2) ^ (-(d / 2)) ≤
      (2 : ℝ) ^ (d / 2) * (1 + ‖x‖) ^ (-d) := by
  have hn := heis_norm_sq_le m x
  have hS : 0 ≤ ∑ i, Complex.normSq (x.1 i) :=
    Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  set Q := 1 + ∑ i, Complex.normSq (x.1 i) + x.2 ^ 2 with hQ
  have hQ0 : 0 < Q := by nlinarith [sq_nonneg x.2]
  have ha0 : 0 < 1 + ‖x‖ := by have := norm_nonneg x; linarith
  have hsq : (1 + ‖x‖) ^ 2 ≤ 2 * Q := by nlinarith [sq_nonneg (‖x‖ - 1), norm_nonneg x]
  have had : (1 + ‖x‖) ^ d ≤ (2 : ℝ) ^ (d / 2) * Q ^ (d / 2) := by
    have h1 : (1 + ‖x‖) ^ d = ((1 + ‖x‖) ^ (2 : ℝ)) ^ (d / 2) := by
      rw [← Real.rpow_mul ha0.le]; congr 1; ring
    rw [h1, ← Real.mul_rpow (by norm_num) hQ0.le]
    apply Real.rpow_le_rpow (by positivity) _ (by linarith)
    rw [Real.rpow_two]; exact hsq
  have hQd : 0 < Q ^ (d / 2) := Real.rpow_pos_of_pos hQ0 _
  have had0 : 0 < (1 + ‖x‖) ^ d := Real.rpow_pos_of_pos ha0 _
  rw [Real.rpow_neg hQ0.le, Real.rpow_neg ha0.le, ← div_eq_mul_inv, le_div_iff₀ had0]
  calc (Q ^ (d / 2))⁻¹ * (1 + ‖x‖) ^ d ≤ (Q ^ (d / 2))⁻¹ * ((2 : ℝ) ^ (d / 2) * Q ^ (d / 2)) := by
        gcongr
    _ = (2 : ℝ) ^ (d / 2) := by
        rw [mul_comm ((2 : ℝ) ^ (d / 2)), ← mul_assoc, inv_mul_cancel₀ hQd.ne', one_mul]

theorem heis_lint_fin (m : ℕ) {d : ℝ} (hd : (2 * m + 1 : ℝ) < d) :
    ∫⁻ x : (Fin m → ℂ) × ℝ, ENNReal.ofReal ((1 + ∑ i, Complex.normSq (x.1 i) + x.2 ^ 2) ^ (-(d / 2))) < ∞ := by
  have hd0 : 0 ≤ d := by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith
  have hfin : ∫⁻ x : (Fin m → ℂ) × ℝ, ENNReal.ofReal ((1 + ‖x‖) ^ (-d)) < ⊤ := by
    haveI hC : (volume : Measure ℂ).IsAddHaarMeasure := by
      first
        | infer_instance
        | exact Complex.isAddHaarMeasure_volume
    haveI hP : (volume : Measure (Fin m → ℂ)).IsAddHaarMeasure := by
      first
        | infer_instance
        | exact MeasureTheory.Measure.pi.isAddHaarMeasure _
    haveI hV : (volume : Measure ((Fin m → ℂ) × ℝ)).IsAddHaarMeasure := by
      first
        | infer_instance
        | exact MeasureTheory.Measure.prod.instIsAddHaarMeasure _ _
        | (show ((volume : Measure (Fin m → ℂ)).prod (volume : Measure ℝ)).IsAddHaarMeasure
           infer_instance)
    apply finite_integral_one_add_norm
    simp only [Module.finrank_prod, Module.finrank_pi_fintype, Complex.finrank_real_complex,
      Module.finrank_self, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    push_cast
    linarith
  refine lt_of_le_of_lt (lintegral_mono (g := fun x : (Fin m → ℂ) × ℝ =>
    ENNReal.ofReal ((2 : ℝ) ^ (d / 2)) * ENNReal.ofReal ((1 + ‖x‖) ^ (-d))) fun x => ?_) ?_
  · dsimp only
    rw [← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (heis_pointwise m hd0 x)
  · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

end ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A
