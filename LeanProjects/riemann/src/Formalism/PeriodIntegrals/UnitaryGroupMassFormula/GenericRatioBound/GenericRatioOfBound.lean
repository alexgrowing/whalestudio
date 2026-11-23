import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolic

namespace PI.GGRatio

open Finset

theorem sum_Ico_one_id (k : ℕ) : ∑ i ∈ Ico 1 k, i = k * (k - 1) / 2 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  rw [← Finset.sum_range_id, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hk]
  simp

theorem pow_gauss_eq_prod (q : ℝ) (k : ℕ) : q ^ (k * (k - 1) / 2) = ∏ i ∈ Ico 1 k, q ^ i := by
  rw [Finset.prod_pow_eq_pow_sum, sum_Ico_one_id]

theorem inv_one_sub_inv (Q : ℝ) (hQ : 1 < Q) : (1 - Q⁻¹)⁻¹ = Q / (Q - 1) := by
  have h1 : Q ≠ 0 := by linarith
  have h2 : Q - 1 ≠ 0 := by linarith
  field_simp

theorem ratio_le (q k d : ℕ) (hq : 2 ≤ q) (hd : ∏ i ∈ Ico 1 k, (q ^ i - 1) ≤ d) :
    ((q ^ (k * (k - 1) / 2) : ℕ) : ℝ) / (d : ℝ) ≤ ∏ i ∈ Ico 1 k, (1 - ((q : ℝ) ^ i)⁻¹)⁻¹ := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  have hcast : ((∏ i ∈ Ico 1 k, (q ^ i - 1) : ℕ) : ℝ) = ∏ i ∈ Ico 1 k, ((q : ℝ) ^ i - 1) := by
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    have h1 : 1 ≤ q ^ i := Nat.one_le_pow _ _ (by omega)
    push_cast [Nat.cast_sub h1]
    ring
  have hprodpos : (0 : ℝ) < ∏ i ∈ Ico 1 k, ((q : ℝ) ^ i - 1) := by
    refine Finset.prod_pos fun i hi => ?_
    have h1 : 1 ≤ i := (Finset.mem_Ico.1 hi).1
    have h2 := one_lt_pow₀ hq1 (by omega : i ≠ 0)
    linarith
  have hdle : ∏ i ∈ Ico 1 k, ((q : ℝ) ^ i - 1) ≤ d := by
    rw [← hcast]
    exact_mod_cast hd
  have e : ∏ i ∈ Ico 1 k, (1 - ((q : ℝ) ^ i)⁻¹)⁻¹ = (q : ℝ) ^ (k * (k - 1) / 2) / ∏ i ∈ Ico 1 k, ((q : ℝ) ^ i - 1) := by
    rw [pow_gauss_eq_prod, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun i hi => ?_
    have h1 : 1 ≤ i := (Finset.mem_Ico.1 hi).1
    exact inv_one_sub_inv _ (one_lt_pow₀ hq1 (by omega))
  rw [e]
  push_cast
  exact div_le_div_of_nonneg_left (by positivity) hprodpos hdle

open Formalism.L2.SG.GGMirabolic in

theorem genericRatioOfBound : GenericRatioOfBound := by
  intro hB hU F _ _ k ψ hψ V _ _ _ π hπ hg
  rw [hU]
  exact ratio_le (Fintype.card F) k _ Fintype.one_lt_card (hB F k ψ hψ V π hπ hg)

end PI.GGRatio
