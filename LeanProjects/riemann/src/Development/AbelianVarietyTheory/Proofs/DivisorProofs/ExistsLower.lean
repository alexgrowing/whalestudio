import Mathlib

namespace GlobalTheory.LowerTriangularEntryBound

theorem exists_lower {n : ℕ} (f : (Fin n → ℂ) → ℝ) (hc : Continuous f)
    (hh : ∀ (t : ℝ) (x : Fin n → ℂ), f (t • x) = t ^ (2 : ℕ) * f x)
    (hp : ∀ x : Fin n → ℂ, x ≠ 0 → 0 < f x) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Fin n → ℂ, c * ‖x‖ ^ 2 ≤ f x := by
  have hf0 : f 0 = 0 := by simpa using hh 0 0
  have hscale : ∀ x : Fin n → ℂ, x ≠ 0 → f x = ‖x‖ ^ 2 * f (‖x‖⁻¹ • x) := by
    intro x hx
    have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have hx' : x = ‖x‖ • (‖x‖⁻¹ • x) := by rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
    conv_lhs => rw [hx']
    exact hh _ _
  have hunit : ∀ x : Fin n → ℂ, x ≠ 0 → ‖x‖⁻¹ • x ∈ Metric.sphere (0 : Fin n → ℂ) 1 := by
    intro x hx
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
  by_cases hS : (Metric.sphere (0 : Fin n → ℂ) 1).Nonempty
  · obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : Fin n → ℂ) 1).exists_isMinOn hS hc.continuousOn
    have hu0 : u ≠ 0 := by
      rintro rfl
      simp at hu
    refine ⟨f u, hp u hu0, fun x => ?_⟩
    by_cases hx : x = 0
    · subst hx
      simp [hf0]
    · have hle : f u ≤ f (‖x‖⁻¹ • x) := isMinOn_iff.mp hmin _ (hunit x hx)
      rw [hscale x hx]
      calc f u * ‖x‖ ^ 2 ≤ f (‖x‖⁻¹ • x) * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_right hle (sq_nonneg _)
        _ = ‖x‖ ^ 2 * f (‖x‖⁻¹ • x) := mul_comm _ _
  · refine ⟨1, one_pos, fun x => ?_⟩
    by_cases hx : x = 0
    · subst hx
      simp [hf0]
    · exact absurd ⟨_, hunit x hx⟩ hS

theorem entry_bound {n : ℕ} (f : (Fin n → ℂ) → ℝ) (hc : Continuous f)
    (hh : ∀ (t : ℝ) (x : Fin n → ℂ), f (t • x) = t ^ (2 : ℕ) * f x)
    (hp : ∀ x : Fin n → ℂ, x ≠ 0 → 0 < f x) :
    ∃ K : ℝ, ∀ (A : Matrix (Fin n) (Fin n) ℂ) (s : ℝ), 0 ≤ s →
      (∀ x : Fin n → ℂ, f (Matrix.mulVec A x) = s * f x) →
      ∀ a b : Fin n, ‖A a b‖ ≤ K * √s := by
  obtain ⟨c, hc0, hlow⟩ := exists_lower f hc hh hp
  set C : ℝ := ∑ j : Fin n, |f (Pi.single j (1 : ℂ))| with hCdef
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨√(C / c), fun A s hs hA a b => ?_⟩
  have hfb : f (Pi.single b (1 : ℂ)) ≤ C :=
    (le_abs_self _).trans (Finset.single_le_sum (f := fun j : Fin n => |f (Pi.single j (1 : ℂ))|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ b))
  have hcol : (Matrix.mulVec A (Pi.single b (1 : ℂ))) a = A a b := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have h2 : ‖A a b‖ ≤ ‖Matrix.mulVec A (Pi.single b (1 : ℂ))‖ := by
    rw [← hcol]
    exact norm_le_pi_norm _ a
  have h2' : ‖A a b‖ ^ 2 ≤ ‖Matrix.mulVec A (Pi.single b (1 : ℂ))‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h2 2
  have h3 : c * ‖Matrix.mulVec A (Pi.single b (1 : ℂ))‖ ^ 2 ≤ s * C :=
    calc c * ‖Matrix.mulVec A (Pi.single b (1 : ℂ))‖ ^ 2 ≤ f (Matrix.mulVec A (Pi.single b (1 : ℂ))) := hlow _
      _ = s * f (Pi.single b (1 : ℂ)) := hA _
      _ ≤ s * C := mul_le_mul_of_nonneg_left hfb hs
  have h4 : ‖A a b‖ ^ 2 ≤ C / c * s := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc0]
    nlinarith [mul_le_mul_of_nonneg_left h2' hc0.le, h3]
  calc ‖A a b‖ = √(‖A a b‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ √(C / c * s) := Real.sqrt_le_sqrt h4
    _ = √(C / c) * √s := Real.sqrt_mul (div_nonneg hC hc0.le) s

end GlobalTheory.LowerTriangularEntryBound
