import Mathlib

namespace KStar.IdealCounting

open Finset

private theorem card_fiber_le (n M k : ℕ) (hk : 1 ≤ k) :
    (((Fintype.piFinset fun _ : Fin (n + 2) => Icc 1 M).filter
      (fun a => ∏ i, a i ≤ M)).filter (fun a => a 0 = k)).card ≤
    ((Fintype.piFinset fun _ : Fin (n + 1) => Icc 1 (M / k)).filter
      (fun a => ∏ i, a i ≤ M / k)).card := by
  refine Finset.card_le_card_of_injOn (fun a => Fin.tail a) ?_ ?_
  · intro a ha
    simp only [coe_filter, mem_filter, Fintype.mem_piFinset, mem_Icc, Set.mem_setOf_eq] at ha ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := ha
    rw [Fin.prod_univ_succ, h3] at h2
    have h4 : ∏ i, Fin.tail a i ≤ M / k := by
      rw [Nat.le_div_iff_mul_le (by omega), mul_comm]
      exact h2
    refine ⟨fun i => ⟨(h1 _).1, le_trans ?_ h4⟩, h4⟩
    exact Finset.single_le_prod' (f := fun i => Fin.tail a i) (fun j _ => (h1 _).1) (mem_univ i)
  · intro a ha b hb hab
    simp only [coe_filter, Set.mem_setOf_eq] at ha hb
    have : Fin.tail a = Fin.tail b := hab
    rw [← Fin.cons_self_tail a, ← Fin.cons_self_tail b, ha.2, hb.2, this]

theorem card_tuples_le (n M : ℕ) (hM : 1 ≤ M) :
    (((Fintype.piFinset fun _ : Fin (n + 1) => Icc 1 M).filter
      (fun a => ∏ i, a i ≤ M)).card : ℝ) ≤ M * (1 + Real.log M) ^ n := by
  induction n generalizing M with
  | zero =>
    have := Finset.card_filter_le (Fintype.piFinset fun _ : Fin (0 + 1) => Icc 1 M)
      (fun a => ∏ i, a i ≤ M)
    rw [Fintype.card_piFinset] at this
    simp only [Nat.card_Icc, Nat.add_sub_cancel, prod_const, card_univ, Fintype.card_fin,
      zero_add, pow_one] at this
    rw [pow_zero, mul_one]
    exact_mod_cast this
  | succ n ih =>
    have hlog : 0 ≤ Real.log M := Real.log_natCast_nonneg M
    rw [Finset.card_eq_sum_card_fiberwise (f := fun a : Fin (n + 1 + 1) → ℕ => a 0)
      (t := Icc 1 M) (by
        intro a ha
        simp only [coe_filter, Fintype.mem_piFinset, Set.mem_setOf_eq] at ha
        exact_mod_cast ha.1 0)]
    push_cast
    have key : ∀ k ∈ Icc 1 M,
        ((((Fintype.piFinset fun _ : Fin (n + 1 + 1) => Icc 1 M).filter
          (fun a => ∏ i, a i ≤ M)).filter (fun a => a 0 = k)).card : ℝ) ≤
          (M * (1 + Real.log M) ^ n) * ((k : ℝ))⁻¹ := by
      intro k hk
      rw [mem_Icc] at hk
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk.1
      have h1 : 1 ≤ M / k := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
      have h2 := ih (M / k) h1
      have h3 := card_fiber_le n M k hk.1
      have h4 : ((M / k : ℕ) : ℝ) ≤ M * (k : ℝ)⁻¹ := by
        rw [← div_eq_mul_inv]; exact Nat.cast_div_le
      have h5 : Real.log ((M / k : ℕ) : ℝ) ≤ Real.log M := by
        apply Real.log_le_log (by exact_mod_cast h1)
        exact_mod_cast Nat.div_le_self M k
      have h6 : 0 ≤ Real.log ((M / k : ℕ) : ℝ) := Real.log_natCast_nonneg _
      calc _ ≤ _ := Nat.cast_le.2 h3
        _ ≤ _ := h2
        _ ≤ (M * (k : ℝ)⁻¹) * (1 + Real.log M) ^ n := by gcongr
        _ = _ := by ring
    have hh : ∑ k ∈ Icc 1 M, ((k : ℝ))⁻¹ ≤ 1 + Real.log M := by
      have := harmonic_le_one_add_log M
      rw [harmonic_eq_sum_Icc] at this
      push_cast at this
      exact this
    calc _ ≤ _ := Finset.sum_le_sum key
      _ = (M * (1 + Real.log M) ^ n) * ∑ k ∈ Icc 1 M, ((k : ℝ))⁻¹ := by rw [Finset.mul_sum]
      _ ≤ (M * (1 + Real.log M) ^ n) * (1 + Real.log M) := by gcongr
      _ = _ := by ring

end KStar.IdealCounting
