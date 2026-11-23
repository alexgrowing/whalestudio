import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.RadialIntegralLemmas
open UpperTheory.Esk

theorem one_sub_ne (ζ : ℂ) (hζ : ‖ζ‖ = 1) (hζ1 : ζ ≠ 1) (r : ℝ) : 1 - ζ * (r : ℂ) ^ 2 ≠ 0 := by
  intro h
  have h1 : ζ * (r : ℂ) ^ 2 = 1 := by linear_combination -h
  have h2 : ‖ζ * (r : ℂ) ^ 2‖ = 1 := by rw [h1, norm_one]
  rw [norm_mul, hζ, one_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h2
  have h3 : (r : ℂ) ^ 2 = 1 := by exact_mod_cast h2
  apply hζ1
  rw [h3, mul_one] at h1
  exact h1

theorem radial_integral_unit_circle_eq (n : ℕ) (K ζ : ℂ) (hζ : ‖ζ‖ = 1) (hζ1 : ζ ≠ 1) :
    ∫ r in (0 : ℝ)..1, K * (4 * (r : ℂ) * (1 - (r : ℂ) ^ 2) ^ n / (1 - ζ * (r : ℂ) ^ 2) ^ (n + 2))
      = K * (2 / (((n : ℂ) + 1) * (1 - ζ))) := by
  have hne := one_sub_ne ζ hζ hζ1
  have hζ1' : ζ - 1 ≠ 0 := sub_ne_zero.2 hζ1
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  set G : ℝ → ℂ := fun r => K * (2 / (((n : ℂ) + 1) * (ζ - 1))) *
    ((1 - (r : ℂ) ^ 2) / (1 - ζ * (r : ℂ) ^ 2)) ^ (n + 1) with hG
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt G
      (K * (4 * (x : ℂ) * (1 - (x : ℂ) ^ 2) ^ n / (1 - ζ * (x : ℂ) ^ 2) ^ (n + 2))) x := by
    intro x _
    have h1 : HasDerivAt (fun w : ℂ => 1 - w ^ 2) (-(2 * (x : ℂ))) (x : ℂ) := by
      simpa using ((hasDerivAt_pow 2 (x : ℂ)).const_sub 1)
    have h2 : HasDerivAt (fun w : ℂ => 1 - ζ * w ^ 2) (-(ζ * (2 * (x : ℂ)))) (x : ℂ) := by
      simpa using (((hasDerivAt_pow 2 (x : ℂ)).const_mul ζ).const_sub 1)
    have h3 := ((h1.div h2 (hne x)).pow (n + 1)).const_mul (K * (2 / (((n : ℂ) + 1) * (ζ - 1))))
    have h5 : HasDerivAt G _ x := h3.comp_ofReal
    refine h5.congr_deriv ?_
    have e := hne x
    simp only [Pi.div_apply, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, div_pow]
    field_simp
    ring
  have hcont : ContinuousOn (fun x : ℝ => K * (4 * (x : ℂ) * (1 - (x : ℂ) ^ 2) ^ n / (1 - ζ * (x : ℂ) ^ 2) ^ (n + 2)))
      (Set.uIcc 0 1) := by
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x _
    exact pow_ne_zero _ (hne x)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  simp only [hG]
  push_cast
  have e0 : (1 : ℂ) - ζ * 0 ^ 2 = 1 := by ring
  simp only [one_pow, sub_self, zero_div, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
    not_false_eq_true, zero_pow, mul_zero, zero_sub]
  field_simp
  ring

theorem rad_int (k : ℕ) (hk : 2 ≤ k) (c η ζ : ℂ) (hζ : ‖ζ‖ = 1) (hζ1 : ζ ≠ 1) :
    ∫ p in Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi, ((4 * p.1 / (1 - p.1 ^ 2) ^ 2 : ℝ) : ℂ) *
      (c * (η * (1 - (p.1 : ℂ) ^ 2) / (1 - ζ * (p.1 : ℂ) ^ 2)) ^ k)
      = c * η ^ k * (4 * Real.pi / (((k : ℂ) - 1) * (1 - ζ))) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  have hne := one_sub_ne ζ hζ hζ1
  have e1 := setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun r : ℝ => ((4 * r / (1 - r ^ 2) ^ 2 : ℝ) : ℂ) * (c * (η * (1 - (r : ℂ) ^ 2) / (1 - ζ * (r : ℂ) ^ 2)) ^ (n + 2)))
    (fun _ : ℝ => (1 : ℂ)) (Set.Ioo 0 1) (Set.Ioo (-Real.pi) Real.pi)
  simp only [mul_one] at e1
  rw [Measure.volume_eq_prod, e1]
  rw [setIntegral_const, Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos])]
  have e2 : ∫ r in Set.Ioo (0 : ℝ) 1, ((4 * r / (1 - r ^ 2) ^ 2 : ℝ) : ℂ) *
      (c * (η * (1 - (r : ℂ) ^ 2) / (1 - ζ * (r : ℂ) ^ 2)) ^ (n + 2)) =
      ∫ r in Set.Ioo (0 : ℝ) 1, (c * η ^ (n + 2)) *
        (4 * (r : ℂ) * (1 - (r : ℂ) ^ 2) ^ n / (1 - ζ * (r : ℂ) ^ 2) ^ (n + 2)) := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r hr
    have h1 : (1 - (r : ℂ) ^ 2) ≠ 0 := by
      have : (1 - r ^ 2 : ℝ) ≠ 0 := by nlinarith [hr.1, hr.2]
      exact_mod_cast this
    have h2 := hne r
    simp only []
    push_cast
    rw [div_pow, mul_pow]
    field_simp
    ring
  rw [e2, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    radial_integral_unit_circle_eq n _ ζ hζ hζ1]
  have hζ1' : 1 - ζ ≠ 0 := sub_ne_zero.2 (Ne.symm hζ1)
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  push_cast
  rw [show (n : ℂ) + 2 - 1 = n + 1 by ring]
  simp only [Complex.real_smul]
  push_cast
  field_simp
  ring

end UpperTheory.Esk.RadialIntegralLemmas
