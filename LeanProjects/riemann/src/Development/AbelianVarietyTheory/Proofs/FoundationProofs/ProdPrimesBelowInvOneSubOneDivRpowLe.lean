import Mathlib
open Filter Topology

namespace GlobalTheory

theorem one_div_succ_rpow_one_add_le_telescope {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    1 / (x + 1) ^ (1 + s) ≤ (1 / x ^ s - 1 / (x + 1) ^ s) / s := by
  have hx1 : 0 < x + 1 := by linarith
  have hq : 0 < (x + 1) / x := div_pos hx1 hx
  have h1 : 1 - ((x + 1) / x)⁻¹ ≤ Real.log ((x + 1) / x) := Real.one_sub_inv_le_log_of_pos hq
  have h2 : 1 - ((x + 1) / x)⁻¹ = 1 / (x + 1) := by field_simp; ring
  have h3 : 1 + s * (1 / (x + 1)) ≤ ((x + 1) / x) ^ s := by
    rw [Real.rpow_def_of_pos hq]
    have h4 := Real.add_one_le_exp (Real.log ((x + 1) / x) * s)
    have h5 : s * (1 / (x + 1)) ≤ Real.log ((x + 1) / x) * s := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (h2 ▸ h1) hs.le
    linarith
  rw [Real.div_rpow hx1.le hx.le] at h3
  rw [Real.rpow_add hx1, Real.rpow_one]
  have hA : 0 < x ^ s := Real.rpow_pos_of_pos hx _
  have hB : 0 < (x + 1) ^ s := Real.rpow_pos_of_pos hx1 _
  generalize x ^ s = A at *
  generalize (x + 1) ^ s = B at *
  rw [le_div_iff₀ hs]
  have h6 : (1 + s * (1 / (x + 1))) / B ≤ B / A / B := by gcongr
  have h7 : B / A / B = 1 / A := by field_simp
  have h8 : (1 + s * (1 / (x + 1))) / B = 1 / B + 1 / ((x + 1) * B) * s := by field_simp
  linarith

theorem sum_range_one_div_rpow_one_add_le {s : ℝ} (hs : 0 < s) (k : ℕ) :
    ∑ n ∈ Finset.range (k + 2), 1 / (n : ℝ) ^ (1 + s)
      ≤ 1 + (1 - 1 / ((k : ℝ) + 1) ^ s) / s := by
  induction k with
  | zero =>
    have : (1 + s) ≠ 0 := by linarith
    simp [Finset.sum_range_succ, Real.zero_rpow this]
  | succ k ih =>
    rw [show k + 1 + 2 = (k + 2) + 1 from rfl, Finset.sum_range_succ]
    have h := one_div_succ_rpow_one_add_le_telescope (x := (k : ℝ) + 1) hs (by positivity)
    have e : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 1 + 1 := by push_cast; ring
    have e' : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [e, e']
    have : (1 - 1 / ((k : ℝ) + 1 + 1) ^ s) / s = (1 - 1 / ((k : ℝ) + 1) ^ s) / s
        + (1 / ((k : ℝ) + 1) ^ s - 1 / ((k : ℝ) + 1 + 1) ^ s) / s := by ring
    linarith

theorem tsum_one_div_rpow_one_add_le {s : ℝ} (hs : 0 < s) :
    ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + s) ≤ 1 + 1 / s := by
  refine Real.tsum_le_of_sum_range_le (fun n => by positivity) fun k => ?_
  calc ∑ n ∈ Finset.range k, 1 / (n : ℝ) ^ (1 + s)
      ≤ ∑ n ∈ Finset.range (k + 2), 1 / (n : ℝ) ^ (1 + s) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
          (fun n _ _ => by positivity)
    _ ≤ 1 + (1 - 1 / ((k : ℝ) + 1) ^ s) / s := sum_range_one_div_rpow_one_add_le hs k
    _ ≤ 1 + 1 / s := by
        have : 0 ≤ 1 / ((k : ℝ) + 1) ^ s := by positivity
        gcongr
        linarith

theorem prod_primesBelow_inv_one_sub_one_div_rpow_le :
    ∀ (s : ℝ), 0 < s → ∀ N : ℕ, ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ (1 + s))⁻¹ ≤ 1 + 1 / s := by
  intro s hs N
  have hsum : Summable fun n : ℕ => 1 / (n : ℝ) ^ (1 + s) :=
    Real.summable_one_div_nat_rpow.2 (by linarith)
  have hE := EulerProduct.prod_primesBelow_tsum_eq_tsum_smoothNumbers
    (f := fun n : ℕ => 1 / (n : ℝ) ^ (1 + s)) (by simp)
    (fun {m n} _ => by
      simp only [Nat.cast_mul]
      rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _), one_div_mul_one_div])
    hsum.norm N
  have hP : ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ (1 + s))⁻¹
      = ∏ p ∈ N.primesBelow, ∑' e : ℕ, 1 / ((p ^ e : ℕ) : ℝ) ^ (1 + s) := by
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_lt
    have hp0 : (0 : ℝ) ≤ p := by linarith
    have h1 : (1 : ℝ) < (p : ℝ) ^ (1 + s) := Real.one_lt_rpow hp1 (by linarith)
    rw [← tsum_geometric_of_lt_one (by positivity) ((div_lt_one (by linarith)).2 h1)]
    refine tsum_congr fun e => ?_
    rw [Nat.cast_pow, ← Real.rpow_natCast (p : ℝ) e, ← Real.rpow_mul hp0, mul_comm,
      Real.rpow_mul hp0, Real.rpow_natCast, one_div_pow]
  rw [hP, hE]
  exact (Summable.tsum_subtype_le _ _ (fun n => by positivity) hsum).trans
    (tsum_one_div_rpow_one_add_le hs)

end GlobalTheory
