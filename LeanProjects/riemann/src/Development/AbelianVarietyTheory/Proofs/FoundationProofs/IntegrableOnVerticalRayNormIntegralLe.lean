import Mathlib
open MeasureTheory Filter Topology Set

namespace GlobalTheory

theorem vertRay_expPow_weight_integrableOn (c : ℝ) (m : ℕ) (hc : 0 < c) :
    IntegrableOn (fun s : ℝ => Real.exp (-c * s) * (1 + s) ^ m) (Ioi 0) := by
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = c / 2 := ⟨_, rfl⟩
  have hb : 0 < b := by rw [hbdef]; positivity
  have hI : IntegrableOn (fun s : ℝ =>
      ((m.factorial : ℝ) / b ^ m * Real.exp b) * Real.exp (-b * s)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hb).const_mul _
  refine Integrable.mono' hI ?_ ?_
  · exact (Continuous.aestronglyMeasurable (by fun_prop))
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_)
    have hs0 : (0:ℝ) ≤ s := le_of_lt hs
    have h1 := Real.pow_div_factorial_le_exp (b * (1 + s)) (mul_nonneg hb.le (by linarith)) m
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg (by linarith) _))]
    have hf : (0:ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
    rw [div_le_iff₀ hf, mul_pow] at h1
    have key : (1 + s) ^ m ≤ (m.factorial : ℝ) / b ^ m * Real.exp (b * (1 + s)) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hb m)]
      linarith [h1]
    have he : Real.exp (b * (1 + s)) = Real.exp b * Real.exp (b * s) := by
      rw [← Real.exp_add]; ring_nf
    have hcs : Real.exp (-c * s) * Real.exp (b * s) = Real.exp (-b * s) := by
      rw [← Real.exp_add]; congr 1; rw [hbdef]; ring
    calc Real.exp (-c * s) * (1 + s) ^ m
        ≤ Real.exp (-c * s) * ((m.factorial : ℝ) / b ^ m * Real.exp (b * (1 + s))) :=
          mul_le_mul_of_nonneg_left key (Real.exp_pos _).le
      _ = ((m.factorial : ℝ) / b ^ m * Real.exp b) * (Real.exp (-c * s) * Real.exp (b * s)) := by
          rw [he]; ring
      _ = ((m.factorial : ℝ) / b ^ m * Real.exp b) * Real.exp (-b * s) := by rw [hcs]

theorem vertRay_integral_expPow_bound : ∀ (g : ℂ → ℂ) (K c : ℝ) (m : ℕ) (τ : ℂ),
    ContinuousOn g {z : ℂ | 0 < z.im} → 0 < c →
    (∀ z : ℂ, 1 ≤ z.im → ‖g z‖ ≤ K * Real.exp (-c * z.im) * (1 + ‖z‖) ^ m) → 1 ≤ τ.im →
    IntegrableOn (fun s : ℝ => g (τ + s * Complex.I)) (Ioi 0) ∧
      ‖∫ s in Ioi (0:ℝ), g (τ + s * Complex.I)‖ ≤
        K * Real.exp (-c * τ.im) * (1 + ‖τ‖) ^ m *
          ∫ s in Ioi (0:ℝ), Real.exp (-c * s) * (1 + s) ^ m := by
  intro g K c m τ hg hc hb hτ
  have hK : 0 ≤ K := by
    have h := hb Complex.I (by simp)
    have hpos : 0 < Real.exp (-c * Complex.I.im) * (1 + ‖Complex.I‖) ^ m := by positivity
    by_contra hneg
    have hneg' : K < 0 := not_le.mp hneg
    have : K * Real.exp (-c * Complex.I.im) * (1 + ‖Complex.I‖) ^ m < 0 := by
      rw [mul_assoc]; exact mul_neg_of_neg_of_pos hneg' hpos
    linarith [norm_nonneg (g Complex.I)]
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = K * Real.exp (-c * τ.im) * (1 + ‖τ‖) ^ m := ⟨_, rfl⟩
  rw [← hA]
  have hw := vertRay_expPow_weight_integrableOn c m hc
  have hbound : ∀ s : ℝ, 0 < s →
      ‖g (τ + s * Complex.I)‖ ≤ A * (Real.exp (-c * s) * (1 + s) ^ m) := by
    intro s hs
    have him : (τ + s * Complex.I).im = τ.im + s := by simp
    have h1 := hb (τ + s * Complex.I) (by rw [him]; linarith)
    rw [him] at h1
    have hn : ‖τ + s * Complex.I‖ ≤ ‖τ‖ + s := by
      calc ‖τ + s * Complex.I‖ ≤ ‖τ‖ + ‖(s:ℂ) * Complex.I‖ := norm_add_le _ _
        _ = ‖τ‖ + s := by
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    have hp : (1 + ‖τ + s * Complex.I‖) ^ m ≤ (1 + ‖τ‖) ^ m * (1 + s) ^ m := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      nlinarith [mul_nonneg (norm_nonneg τ) hs.le]
    have he : Real.exp (-c * (τ.im + s)) = Real.exp (-c * τ.im) * Real.exp (-c * s) := by
      rw [← Real.exp_add]; ring_nf
    calc ‖g (τ + s * Complex.I)‖
        ≤ K * Real.exp (-c * (τ.im + s)) * (1 + ‖τ + s * Complex.I‖) ^ m := h1
      _ ≤ K * Real.exp (-c * (τ.im + s)) * ((1 + ‖τ‖) ^ m * (1 + s) ^ m) :=
          mul_le_mul_of_nonneg_left hp (mul_nonneg hK (Real.exp_pos _).le)
      _ = A * (Real.exp (-c * s) * (1 + s) ^ m) := by rw [he, hA]; ring
  have hmeas : AEStronglyMeasurable (fun s : ℝ => g (τ + s * Complex.I))
      (volume.restrict (Ioi 0)) := by
    have hc' : ContinuousOn (fun s : ℝ => g (τ + s * Complex.I)) (Ioi 0) := by
      refine ContinuousOn.comp (g := g) (f := fun s : ℝ => τ + s * Complex.I) hg (by fun_prop) ?_
      intro s hs
      have him : (τ + s * Complex.I).im = τ.im + s := by simp
      show 0 < (τ + s * Complex.I).im
      rw [him]
      linarith [mem_Ioi.mp hs]
    exact hc'.aestronglyMeasurable measurableSet_Ioi
  have hae : ∀ᵐ s : ℝ ∂(volume.restrict (Ioi (0:ℝ))),
      ‖g (τ + s * Complex.I)‖ ≤ A * (Real.exp (-c * s) * (1 + s) ^ m) :=
    (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => hbound s hs)
  have hint : IntegrableOn (fun s : ℝ => g (τ + s * Complex.I)) (Ioi 0) :=
    Integrable.mono' (hw.const_mul A) hmeas hae
  refine ⟨hint, ?_⟩
  calc ‖∫ s in Ioi (0:ℝ), g (τ + s * Complex.I)‖
      ≤ ∫ s in Ioi (0:ℝ), A * (Real.exp (-c * s) * (1 + s) ^ m) :=
        norm_integral_le_of_norm_le (hw.const_mul A) hae
    _ = A * ∫ s in Ioi (0:ℝ), Real.exp (-c * s) * (1 + s) ^ m := integral_const_mul A _

end GlobalTheory
