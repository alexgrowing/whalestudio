import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.CSandwichStB

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder Matrix

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem bNormSq_nonneg' (μ : Measure (Ix κ → ℂ)) (m : ConeMetric ℂ (Ix κ)) {r n : ℕ}
    (s : Fin r → (Ix κ → ℂ) → ℂ) (c : Fin r → ℂ) : 0 ≤ bNormSq μ s (wgt m n) c := by
  unfold bNormSq
  refine MeasureTheory.integral_nonneg fun z => mul_nonneg (sq_nonneg _) ?_
  unfold wgt
  refine inv_nonneg.mpr ?_
  rw [pow_mul]
  exact pow_nonneg (sq_nonneg _) _

theorem norm_le_of_sq_wgt_le {m : ConeMetric ℂ (Ix κ)} {n : ℕ} {z : Ix κ → ℂ} (hz : z ≠ 0)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 * wgt m n z ≤ b) :
    a ≤ Real.sqrt b * m.ρ z ^ n := by
  have hρ : 0 < m.ρ z := m.pos z hz
  have hP : 0 < m.ρ z ^ n := pow_pos hρ n
  have hw : wgt m n z = ((m.ρ z ^ n) ^ 2)⁻¹ := by
    unfold wgt
    rw [← pow_mul, mul_comm n 2]
  rw [hw] at h
  have hP2 : 0 < (m.ρ z ^ n) ^ 2 := pow_pos hP 2
  have h2 : a ^ 2 ≤ b * (m.ρ z ^ n) ^ 2 := by
    rwa [← div_eq_mul_inv, div_le_iff₀ hP2] at h
  calc a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha).symm
    _ ≤ Real.sqrt (b * (m.ρ z ^ n) ^ 2) := Real.sqrt_le_sqrt h2
    _ = Real.sqrt b * m.ρ z ^ n := by rw [Real.sqrt_mul hb, Real.sqrt_sq hP.le]

theorem log_sqrt_bound (D : ℕ) {T : ℝ} (hT : 1 ≤ T) {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ Real.log (Real.sqrt (T * (n : ℝ) ^ D)) ∧
      Real.log (Real.sqrt (T * (n : ℝ) ^ D)) ≤
        (1 / 2) * (Real.log T / Real.log 2 + D) * Real.log (n + 1) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hT0' : 0 < T := by linarith
  have hnpos : (0 : ℝ) < n := by linarith
  have hpos : 0 < T * (n : ℝ) ^ D := mul_pos hT0' (pow_pos hnpos D)
  have hlog : Real.log (Real.sqrt (T * (n : ℝ) ^ D)) = (1 / 2) * (Real.log T + D * Real.log n) := by
    rw [Real.log_sqrt hpos.le, Real.log_mul hT0'.ne' (pow_pos hnpos D).ne', Real.log_pow]
    ring
  have hT0 : 0 ≤ Real.log T := Real.log_nonneg hT
  have hn0 : 0 ≤ Real.log n := Real.log_nonneg hn'
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2n : Real.log 2 ≤ Real.log (n + 1) := Real.log_le_log (by norm_num) (by linarith)
  have hln : Real.log n ≤ Real.log (n + 1) := Real.log_le_log hnpos (by linarith)
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  refine ⟨?_, ?_⟩
  · rw [hlog]
    exact mul_nonneg (by norm_num) (add_nonneg hT0 (mul_nonneg hD0 hn0))
  · rw [hlog]
    have h1 : Real.log T ≤ Real.log T / Real.log 2 * Real.log (n + 1) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
      exact mul_le_mul_of_nonneg_left hl2n hT0
    have h2 : (D : ℝ) * Real.log n ≤ D * Real.log (n + 1) := mul_le_mul_of_nonneg_left hln hD0
    have h3 : (1 / 2) * (Real.log T / Real.log 2 + D) * Real.log (n + 1) =
        (1 / 2) * (Real.log T / Real.log 2 * Real.log (n + 1) + D * Real.log (n + 1)) := by ring
    rw [h3]
    linarith

theorem choose_bound (k D : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    (((n + k + D).choose D : ℕ) : ℝ) ≤ ((1 + k + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D := by
  have hN : n + k + D ≤ (1 + k + D) * n := by nlinarith
  have h1 : (n + k + D).choose D ≤ (n + k + D) ^ D := Nat.choose_le_pow _ _
  have h2 : (n + k + D) ^ D ≤ ((1 + k + D) * n) ^ D := Nat.pow_le_pow_left hN D
  have h3 : (n + k + D).choose D ≤ (1 + k + D) ^ D * n ^ D := by
    rw [← mul_pow]
    exact h1.trans h2
  exact_mod_cast h3

theorem le_of_injective_mulVec {R r : ℕ} (M : Matrix (Fin R) (Fin r) ℚ)
    (hM : Function.Injective M.mulVec) : r ≤ R := by
  have h := LinearMap.finrank_le_finrank_of_injective (f := Matrix.mulVecLin M) hM
  simpa using h

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
