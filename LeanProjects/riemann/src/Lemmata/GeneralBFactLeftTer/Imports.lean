import Mathlib

universe u_1

namespace Bl.general_b_fact_left_ter

theorem goal1 :
  ∀ {F : Type u_1} [inst : NormedField.{u_1} F] [IsUltrametricDist.{u_1} F] {y : F} (p : Polynomial.{0} Int),
  Polynomial.Monic.{0} p →
    Eq.{u_1 + 1} (Polynomial.eval₂.{0, u_1} (Int.castRingHom.{u_1} F) y p) 0 → LE.le.{0} (Norm.norm.{u_1} y) 1 := by
  intro F _ _ y p hp h
  by_contra hy0
  have hy : 1 < ‖y‖ := not_le.mp hy0
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, map_one,
    one_mul] at h
  have hsum : ‖∑ i ∈ Finset.range p.natDegree, (Int.castRingHom F) (p.coeff i) * y ^ i‖
      < ‖y‖ ^ p.natDegree := by
    rcases (Finset.range p.natDegree).eq_empty_or_nonempty with he | hne
    · rw [he, Finset.sum_empty, norm_zero]; positivity
    · obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hne
        (fun i => (Int.castRingHom F) (p.coeff i) * y ^ i)
      refine lt_of_le_of_lt hle ?_
      rw [norm_mul, norm_pow]
      have h1 : ‖(Int.castRingHom F) (p.coeff i)‖ ≤ 1 := by
        rw [eq_intCast]; exact IsUltrametricDist.norm_intCast_le_one F _
      have h2 : ‖y‖ ^ i < ‖y‖ ^ p.natDegree := pow_lt_pow_right₀ hy (Finset.mem_range.mp hi)
      calc _ ≤ 1 * ‖y‖ ^ i := mul_le_mul_of_nonneg_right h1 (by positivity)
        _ < ‖y‖ ^ p.natDegree := by rw [one_mul]; exact h2
  rw [eq_neg_of_add_eq_zero_left h, norm_neg, norm_pow] at hsum
  exact lt_irrefl _ hsum

end Bl.general_b_fact_left_ter
