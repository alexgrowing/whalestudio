import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FrobFixNegOne
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.NormNatCastClOfNotDvd

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM

variable (l : ℕ) [Fact l.Prime]

theorem rmu_norm_le {x : ℂ_[l]} (hx : x ∈ Rmu l) : ‖x‖ ≤ 1 := by
  induction hx using Subring.closure_induction with
  | mem x hx => exact (muP_norm l hx).le
  | zero => simp
  | one => simp
  | add x y _ _ hx hy =>
    exact (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
  | neg x _ hx => rwa [norm_neg]
  | mul x y _ _ hx hy =>
    rw [norm_mul]
    exact mul_le_one₀ hx (norm_nonneg _) hy

theorem kmu_frac {x : ℂ_[l]} (hx : x ∈ Kmu l) :
    ∃ a ∈ Rmu l, ∃ b ∈ Rmu l, b ≠ 0 ∧ x = a / b := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Subfield.mem_closure_iff.1 hx
  by_cases hz0 : z = 0
  · refine ⟨0, (Rmu l).zero_mem, 1, (Rmu l).one_mem, one_ne_zero, ?_⟩
    rw [hz0, div_zero, zero_div]
  · exact ⟨y, hy, z, hz, hz0, rfl⟩

theorem exists_power_mul_unitNorm (k : ℕ) : ∀ a ∈ Rmu l, a ≠ 0 → 1 < (l : ℝ) ^ k * ‖a‖ →
    ∃ m : ℕ, ∃ c ∈ Rmu l, ∃ u ∈ Rmu l, ‖c‖ = 1 ∧ ‖u‖ = 1 ∧ a * u = (l : ℂ_[l]) ^ m * c := by
  induction k with
  | zero =>
    intro a ha _ h
    rw [pow_zero, one_mul] at h
    exact absurd (rmu_norm_le l ha) (not_le.2 h)
  | succ k ih =>
    intro a ha ha0 h
    rcases (rmu_norm_le l ha).eq_or_lt with h1 | h1
    · exact ⟨0, a, ha, 1, (Rmu l).one_mem, h1, norm_one, by rw [pow_zero, one_mul, mul_one]⟩
    obtain ⟨f, hf, r, hr, he⟩ := rmu_frob l a ha
    have hl1 : 1 < l := (Fact.out : l.Prime).one_lt
    have hq : 1 ≤ l ^ f - 1 := by
      have : 2 ≤ l ^ f := le_trans (Fact.out : l.Prime).two_le (Nat.le_self_pow hf.ne' l)
      omega
    set u := a ^ (l ^ f - 1) - 1 with hu
    have huR : u ∈ Rmu l := sub_mem (pow_mem ha _) (Rmu l).one_mem
    have hu1 : ‖u‖ = 1 := by
      have hsm : ‖a ^ (l ^ f - 1)‖ < 1 := by
        rw [norm_pow]
        exact pow_lt_one₀ (norm_nonneg _) h1 (by omega)
      have := ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation.norm_eq_of_norm_sub_lt' l (a := u) (b := -1)
        (by rw [hu, sub_neg_eq_add, sub_add_cancel, norm_neg, norm_one]; exact hsm)
      rwa [norm_neg, norm_one] at this
    have hau : a * u = (l : ℂ_[l]) * r := by
      rw [← he, hu, mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ l ^ f)]
    have hnr : ‖r‖ = l * ‖a‖ := by
      have := congrArg norm hau
      rw [norm_mul, norm_mul, hu1, mul_one, norm_l_Cl] at this
      have hl0 : (l : ℝ) ≠ 0 := by positivity
      rw [this, ← mul_assoc, mul_inv_cancel₀ hl0, one_mul]
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hnr
      have : (0 : ℝ) < l * ‖a‖ := mul_pos (by positivity) (norm_pos_iff.2 ha0)
      linarith
    have h' : 1 < (l : ℝ) ^ k * ‖r‖ := by
      rw [hnr, ← mul_assoc, ← pow_succ]; exact h
    obtain ⟨m, c, hc, v, hv, hc1, hv1, hrv⟩ := ih r hr hr0 h'
    refine ⟨m + 1, c, hc, u * v, mul_mem huR hv, hc1, by rw [norm_mul, hu1, hv1, one_mul], ?_⟩
    rw [← mul_assoc, hau, mul_assoc, hrv, pow_succ]
    ring

theorem rmu_shape {a : ℂ_[l]} (ha : a ∈ Rmu l) (ha0 : a ≠ 0) :
    ∃ m : ℕ, ∃ c ∈ Rmu l, ∃ u ∈ Rmu l, ‖c‖ = 1 ∧ ‖u‖ = 1 ∧ a * u = (l : ℂ_[l]) ^ m * c := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (‖a‖⁻¹) (by exact_mod_cast (Fact.out : l.Prime).one_lt :
    (1 : ℝ) < l)
  refine exists_power_mul_unitNorm l k a ha ha0 ?_
  have hpos : 0 < ‖a‖ := norm_pos_iff.2 ha0
  calc (1 : ℝ) = ‖a‖⁻¹ * ‖a‖ := (inv_mul_cancel₀ hpos.ne').symm
    _ < (l : ℝ) ^ k * ‖a‖ := mul_lt_mul_of_pos_right hk hpos

theorem kmu_shape {x : ℂ_[l]} (hx : x ∈ Kmu l) (hx0 : x ≠ 0) :
    ∃ m : ℤ, ∃ a ∈ Rmu l, ∃ b ∈ Rmu l, ‖a‖ = 1 ∧ ‖b‖ = 1 ∧ x = (l : ℂ_[l]) ^ m * (a / b) := by
  obtain ⟨a, ha, b, hb, hb0, rfl⟩ := kmu_frac l hx
  have ha0 : a ≠ 0 := by rintro rfl; exact hx0 (zero_div b)
  obtain ⟨m, c, hc, u, hu, hc1, hu1, hau⟩ := rmu_shape l ha ha0
  obtain ⟨n, d, hd, v, hv, hd1, hv1, hbv⟩ := rmu_shape l hb hb0
  have hl0 : (l : ℂ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu1
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv1
  have hd0 : d ≠ 0 := by rintro rfl; simp at hd1
  refine ⟨(m : ℤ) - n, c * v, mul_mem hc hv, d * u, mul_mem hd hu,
    by rw [norm_mul, hc1, hv1, one_mul], by rw [norm_mul, hd1, hu1, one_mul], ?_⟩
  rw [zpow_sub₀ hl0, zpow_natCast, zpow_natCast]
  have ha' : a = (l : ℂ_[l]) ^ m * c / u := by rw [← hau, mul_div_cancel_right₀ _ hu0]
  have hb' : b = (l : ℂ_[l]) ^ n * d / v := by rw [← hbv, mul_div_cancel_right₀ _ hv0]
  rw [ha', hb']
  field_simp

end ReciprocityTheory.ChartRestriction.L1
