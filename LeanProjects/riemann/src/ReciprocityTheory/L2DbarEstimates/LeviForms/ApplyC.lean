import ReciprocityTheory.L2DbarEstimates.LeviForms.ApplyB

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

theorem ap_key (η D : ℝ) (h8 : 8 ≤ η) (hD : 2 * η ≤ D) : 4 / η ^ 2 ≤ 1 / η - 1 / D := by
  have hη : 0 < η := by linarith
  have h1 : 1 / D ≤ 1 / (2 * η) := one_div_le_one_div_of_le (by positivity) hD
  have h2 : 4 / η ^ 2 ≤ 1 / η - 1 / (2 * η) := by
    rw [show 1 / η - 1 / (2 * η) = 1 / (2 * η) by field_simp; ring]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

theorem ap_pt_in (u E η D a I : ℝ) (hu : 0 ≤ u) (hE : 0 ≤ E) (h8 : 8 ≤ η) (hD : 2 * η ≤ D)
    (ha : 0 ≤ a) (hI : 2 * a * (E / η) ≤ I) :
    (Real.sqrt a + u * Real.sqrt (2 / η)) ^ 2 * (E / η) ≤
      (u ^ 2 * (E / η) - u ^ 2 * (E / D)) + I := by
  have hη : 0 < η := by linarith
  have hb : 0 ≤ 2 / η := by positivity
  have ham : 2 * Real.sqrt a * (u * Real.sqrt (2 / η)) ≤ a + u ^ 2 * (2 / η) := by
    have := two_mul_le_add_sq (Real.sqrt a) (u * Real.sqrt (2 / η))
    rwa [mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb] at this
  have h1 : (Real.sqrt a + u * Real.sqrt (2 / η)) ^ 2 ≤ 2 * a + 2 * (u ^ 2 * (2 / η)) := by
    have e : (Real.sqrt a + u * Real.sqrt (2 / η)) ^ 2 = Real.sqrt a ^ 2 +
        2 * Real.sqrt a * (u * Real.sqrt (2 / η)) + u ^ 2 * Real.sqrt (2 / η) ^ 2 := by ring
    rw [e, Real.sq_sqrt ha, Real.sq_sqrt hb]
    linarith
  have hk := ap_key η D h8 hD
  calc (Real.sqrt a + u * Real.sqrt (2 / η)) ^ 2 * (E / η)
      ≤ (2 * a + 2 * (u ^ 2 * (2 / η))) * (E / η) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = 2 * a * (E / η) + u ^ 2 * E * (4 / η ^ 2) := by field_simp; ring
    _ ≤ I + u ^ 2 * E * (1 / η - 1 / D) :=
        add_le_add hI (mul_le_mul_of_nonneg_left hk (by positivity))
    _ = (u ^ 2 * (E / η) - u ^ 2 * (E / D)) + I := by ring

theorem ap_pt_out (u E η X : ℝ) (hη : 0 < η) :
    (Real.sqrt 0 + u * Real.sqrt ((X + 1) ^ 2 / ((X + 1) ^ 2 + η))) ^ 2 * (E / η) =
      u ^ 2 * (E / η) - u ^ 2 * (E / ((X + 1) ^ 2 + η)) := by
  have hD : 0 < (X + 1) ^ 2 + η := by positivity
  rw [Real.sqrt_zero, zero_add, mul_pow, Real.sq_sqrt (by positivity)]
  field_simp
  ring

theorem ap_bound (D ε η Θ : ℝ) (G B : ℂ) (hε : 0 < ε) (hD : |D| ≤ 3)
    (hB : ‖B‖ ^ 2 ≤ 4 * ε ^ 4 * η * Θ) (hη : 0 ≤ η) (hΘ : 0 ≤ Θ) :
    ‖((D * (1 / ε ^ 2) : ℝ) : ℂ) * G * B‖ ^ 2 ≤ 36 * η * ‖G‖ ^ 2 * Θ := by
  have e1 : ‖((D * (1 / ε ^ 2) : ℝ) : ℂ) * G * B‖ ^ 2 = D ^ 2 * ‖G‖ ^ 2 * ‖B‖ ^ 2 / ε ^ 4 := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, mul_pow, abs_mul,
      mul_pow, sq_abs, abs_of_pos (by positivity : (0:ℝ) < 1 / ε ^ 2)]
    field_simp
  have hD2 : D ^ 2 ≤ 9 := by
    have := sq_le_sq' (abs_le.1 hD).1 (abs_le.1 hD).2
    linarith
  rw [e1]
  have hε4 : 0 < ε ^ 4 := by positivity
  rw [div_le_iff₀ hε4]
  have hG : 0 ≤ ‖G‖ ^ 2 := by positivity
  calc D ^ 2 * ‖G‖ ^ 2 * ‖B‖ ^ 2 ≤ D ^ 2 * ‖G‖ ^ 2 * (4 * ε ^ 4 * η * Θ) :=
        mul_le_mul_of_nonneg_left hB (by positivity)
    _ = D ^ 2 * (4 * ε ^ 4 * (η * ‖G‖ ^ 2 * Θ)) := by ring
    _ ≤ 9 * (4 * ε ^ 4 * (η * ‖G‖ ^ 2 * Θ)) :=
        mul_le_mul_of_nonneg_right hD2 (by positivity)
    _ = 36 * η * ‖G‖ ^ 2 * Θ * ε ^ 4 := by ring

end ReciprocityTheory.L2DbarEstimates.I
