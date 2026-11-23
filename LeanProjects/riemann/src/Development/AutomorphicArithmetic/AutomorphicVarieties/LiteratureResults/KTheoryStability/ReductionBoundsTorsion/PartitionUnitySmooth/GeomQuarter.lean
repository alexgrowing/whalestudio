import Mathlib

noncomputable section

namespace PositivityTheory.KB.SmoothPartitionUnityBasic.GeometricWindowBounds

theorem geom_quarter (m : ℕ) : ∑ i ∈ Finset.range m, (1 / 4 : ℝ) ^ i ≤ 4 / 3 := by
  have hp : 0 ≤ (1 / 4 : ℝ) ^ m := by positivity
  rw [geom_sum_eq (by norm_num : (1 / 4 : ℝ) ≠ 1), div_le_iff_of_neg (by norm_num)]
  linarith

theorem geo_sum (S : Finset ℤ) (n0 : ℤ) (hS : ∀ n ∈ S, n0 ≤ n) :
    ∑ n ∈ S, ((4 : ℝ) ^ n)⁻¹ ≤ 4 / 3 * ((4 : ℝ) ^ n0)⁻¹ := by
  have key : ∀ n ∈ S, ((4 : ℝ) ^ n)⁻¹ = ((4 : ℝ) ^ n0)⁻¹ * (1 / 4 : ℝ) ^ (n - n0).toNat := by
    intro n hn
    have e : n = n0 + ((n - n0).toNat : ℤ) := by
      rw [Int.toNat_of_nonneg (sub_nonneg.2 (hS n hn))]; ring
    conv_lhs => rw [e]
    rw [zpow_add₀ (by norm_num), zpow_natCast, mul_inv, one_div, inv_pow]
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have hinj : Set.InjOn (fun n : ℤ => (n - n0).toNat) S := by
    intro x hx y hy hxy
    have hxy' : (x - n0).toNat = (y - n0).toNat := hxy
    have h1 := Int.toNat_of_nonneg (sub_nonneg.2 (hS x hx))
    have h2 := Int.toNat_of_nonneg (sub_nonneg.2 (hS y hy))
    omega
  have hsum : ∑ i ∈ S.image (fun n : ℤ => (n - n0).toNat), (1 / 4 : ℝ) ^ i =
      ∑ n ∈ S, (1 / 4 : ℝ) ^ (n - n0).toNat := Finset.sum_image hinj
  rw [← hsum]
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_range_sup_succ _)
    fun _ _ _ => by positivity).trans (geom_quarter _)

theorem geo_rel (T : Finset ℤ) {x0 B : ℝ} (hx0 : 0 < x0) (hB : 0 ≤ B) (f : ℤ → ℝ)
    (hf : ∀ n ∈ T, |f n| ≤ B * ((4 : ℝ) ^ n)⁻¹) (hz : ∀ n ∈ T, f n ≠ 0 → x0 < (4 : ℝ) ^ n) :
    |∑ n ∈ T, f n| ≤ 4 / 3 * B / x0 := by
  rw [← Finset.sum_filter_of_ne hz]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hb : ∀ n ∈ T.filter (fun n => x0 < (4 : ℝ) ^ n), |f n| ≤ B * ((4 : ℝ) ^ n)⁻¹ :=
    fun n hn => hf n (Finset.mem_filter.1 hn).1
  refine (Finset.sum_le_sum hb).trans ?_
  rw [← Finset.mul_sum]
  rcases (T.filter (fun n => x0 < (4 : ℝ) ^ n)).eq_empty_or_nonempty with he | hne
  · rw [he, Finset.sum_empty, mul_zero]
    exact div_nonneg (mul_nonneg (by norm_num) hB) hx0.le
  · have hmin := (Finset.mem_filter.1 (Finset.min'_mem _ hne)).2
    have h1 := geo_sum (T.filter (fun n => x0 < (4 : ℝ) ^ n)) (Finset.min' _ hne)
      fun n hn => Finset.min'_le _ n hn
    have h2 : ((4 : ℝ) ^ Finset.min' _ hne)⁻¹ ≤ x0⁻¹ := inv_anti₀ hx0 hmin.le
    calc B * ∑ n ∈ T.filter (fun n => x0 < (4 : ℝ) ^ n), ((4 : ℝ) ^ n)⁻¹ ≤ B * (4 / 3 * x0⁻¹) :=
          mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h2 (by norm_num))) hB
      _ = 4 / 3 * B / x0 := by ring

theorem zpow_window {x0 y0 : ℝ} (hx : 0 < x0) (hy : 0 < y0) :
    ∃ a b : ℤ, ∀ n : ℤ, x0 < (4 : ℝ) ^ n → (4 : ℝ) ^ n < y0 → n ∈ Finset.Icc a b := by
  obtain ⟨a, ha, -⟩ := exists_mem_Ioc_zpow hx (by norm_num : (1 : ℝ) < 4)
  obtain ⟨b, -, hb⟩ := exists_mem_Ioc_zpow hy (by norm_num : (1 : ℝ) < 4)
  refine ⟨a, b, fun n h1 h2 => Finset.mem_Icc.2 ⟨?_, ?_⟩⟩
  · exact ((zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 4)).1 (ha.trans h1)).le
  · have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 4)).1 (h2.trans_le hb)
    omega

theorem fin_alg {δ A R μh lh ld c Cm E D1 D2 : ℝ} (hδ : 0 ≤ δ) (hA : 0 ≤ A) (hc : 0 < c)
    (hlh : 0 < lh) (hld : 0 < ld) (hCm : 0 ≤ Cm) (hE : 0 ≤ E) (hR : μh * A ≤ R) (hμ : c * ld ≤ μh)
    (h1 : |D1| ≤ (5 / 4 * Cm + 1) * δ * (μh * A)) (h2 : |D2| ≤ 4 / 3 * (E * δ * A) / (3 / 16 * lh)) :
    |D1 + D2| ≤ ((5 / 4 * Cm + 1) + 64 / 9 * E / c) * (1 + (lh * ld)⁻¹) * δ * R := by
  have hμ0 : 0 ≤ μh := (mul_pos hc hld).le.trans hμ
  have hR0 : 0 ≤ R := (mul_nonneg hμ0 hA).trans hR
  have hAR : A ≤ R / (c * ld) := by
    rw [le_div_iff₀ (mul_pos hc hld)]
    calc A * (c * ld) = (c * ld) * A := by ring
      _ ≤ μh * A := mul_le_mul_of_nonneg_right hμ hA
      _ ≤ R := hR
  have hlh0 : lh ≠ 0 := hlh.ne'
  have hld0 : ld ≠ 0 := hld.ne'
  have hc0 : c ≠ 0 := hc.ne'
  have e2 : 4 / 3 * (E * δ * A) / (3 / 16 * lh) = 64 / 9 * E * δ * A / lh := by
    field_simp <;> ring
  have h2' : |D2| ≤ 64 / 9 * E / c * δ * R * (lh * ld)⁻¹ := by
    rw [e2] at h2
    refine h2.trans ?_
    rw [div_le_iff₀ hlh]
    have e3 : 64 / 9 * E / c * δ * R * (lh * ld)⁻¹ * lh = 64 / 9 * E * δ * (R / (c * ld)) := by
      field_simp <;> ring
    rw [e3]
    exact mul_le_mul_of_nonneg_left hAR (by positivity)
  have h1' : |D1| ≤ (5 / 4 * Cm + 1) * δ * R := h1.trans (mul_le_mul_of_nonneg_left hR (by positivity))
  have hP : 0 ≤ (lh * ld)⁻¹ := inv_nonneg.2 (mul_pos hlh hld).le
  have hQ : 0 ≤ 64 / 9 * E / c := by positivity
  have hS : 0 ≤ 5 / 4 * Cm + 1 := by positivity
  have hδR : 0 ≤ δ * R := mul_nonneg hδ hR0
  calc |D1 + D2| ≤ |D1| + |D2| := abs_add_le _ _
    _ ≤ (5 / 4 * Cm + 1) * δ * R + 64 / 9 * E / c * δ * R * (lh * ld)⁻¹ := add_le_add h1' h2'
    _ ≤ _ := by
        nlinarith [mul_nonneg hQ hδR, mul_nonneg hS hδR, mul_nonneg (mul_nonneg hQ hδR) hP,
          mul_nonneg (mul_nonneg hS hδR) hP]

end PositivityTheory.KB.SmoothPartitionUnityBasic.GeometricWindowBounds
