import Mathlib

open Matrix Finset Real

namespace GlobalTheory

namespace ZetaProd

theorem zeta_le (l K : ℕ) (hK : 0 < K) :
    (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ (l + 2)) ≤
      (∑ m ∈ Finset.range K, 1 / ((m : ℝ) + 1) ^ (l + 2)) + 1 / ((K : ℝ) + 1) ^ l * (1 / K) := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have key : ∀ n : ℕ, (∑ m ∈ Finset.range (K + n), 1 / ((m : ℝ) + 1) ^ (l + 2)) ≤
      (∑ m ∈ Finset.range K, 1 / ((m : ℝ) + 1) ^ (l + 2)) +
        1 / ((K : ℝ) + 1) ^ l * (1 / K - 1 / ((K : ℝ) + n)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← add_assoc, Finset.sum_range_succ]
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have h1 : 1 / (((K + n : ℕ) : ℝ) + 1) ^ (l + 2) ≤
          1 / ((K : ℝ) + 1) ^ l * (1 / ((K : ℝ) + n) - 1 / ((K : ℝ) + (n + 1 : ℕ))) := by
        push_cast
        have e : 1 / ((K : ℝ) + n) - 1 / ((K : ℝ) + (n + 1)) =
            1 / (((K : ℝ) + n) * ((K : ℝ) + n + 1)) := by
          field_simp
          ring
        rw [e, one_div_mul_one_div]
        apply one_div_le_one_div_of_le (by positivity)
        rw [pow_add]
        apply mul_le_mul
        · apply pow_le_pow_left₀ (by positivity)
          linarith
        · nlinarith
        · positivity
        · positivity
      nlinarith
  apply Real.tsum_le_of_sum_range_le (fun m => by positivity)
  intro n
  have h2 : (∑ m ∈ Finset.range n, 1 / ((m : ℝ) + 1) ^ (l + 2)) ≤
      ∑ m ∈ Finset.range (K + n), 1 / ((m : ℝ) + 1) ^ (l + 2) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.range_mono (by omega)
    · intro i _ _
      positivity
  have h3 : 0 ≤ 1 / ((K : ℝ) + 1) ^ l * (1 / ((K : ℝ) + n)) := by positivity
  have := key n
  nlinarith

theorem zeta_nonneg (l : ℕ) : 0 ≤ ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ l :=
  tsum_nonneg (fun m => by positivity)

theorem zeta_two_le : (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 2) ≤ 1.645 := by
  have h := (hasSum_nat_add_iff' 1).2 hasSum_zeta_two
  have h2 : HasSum (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
    simpa using h
  rw [h2.tsum_eq]
  have := Real.pi_lt_d4
  have := Real.pi_pos
  nlinarith

theorem zeta_three_le : (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 3) ≤ 1.2027 :=
  (zeta_le 1 30 (by norm_num)).trans (by norm_num [Finset.sum_range_succ])

theorem zeta_four_le : (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 4) ≤ 1.0825 :=
  (zeta_le 2 30 (by norm_num)).trans (by norm_num [Finset.sum_range_succ])

theorem zeta_five_le : (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 5) ≤ 1.0370 :=
  (zeta_le 3 30 (by norm_num)).trans (by norm_num [Finset.sum_range_succ])

theorem zeta_six_le : (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 6) ≤ 1.0174 :=
  (zeta_le 4 30 (by norm_num)).trans (by norm_num [Finset.sum_range_succ])

theorem zeta_seven_le : (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 7) ≤ 1.0084 :=
  (zeta_le 5 30 (by norm_num)).trans (by norm_num [Finset.sum_range_succ])

theorem zeta_eight_le : (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 8) ≤ 1.0041 :=
  (zeta_le 6 30 (by norm_num)).trans (by norm_num [Finset.sum_range_succ])

theorem zeta_tail_le (n : ℕ) :
    (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ (n + 9)) ≤ 1 + 0.00235 * (1 / 2) ^ n := by
  refine (zeta_le (n + 7) 2 (by norm_num)).trans ?_
  have h : (1 / 3 : ℝ) ^ n ≤ (1 / 2) ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have e1 : 1 / ((1 : ℝ) + 1) ^ (n + 7 + 2) = (1 / 2) ^ n / 512 := by
    rw [_root_.one_div_pow, add_assoc, pow_add]; norm_num; ring
  have e2 : 1 / ((2 : ℝ) + 1) ^ (n + 7) = (1 / 3) ^ n / 2187 := by
    rw [_root_.one_div_pow, pow_add]; norm_num; ring
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.cast_zero,
    Nat.cast_one, Nat.cast_ofNat, zero_add, one_pow]
  rw [e1, e2]
  have : (0 : ℝ) ≤ (1 / 2) ^ n := by positivity
  linarith

theorem prod_three_eight (N : ℕ) (hN : N ≤ 8) :
    ∏ l ∈ Finset.Icc 3 N, (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ l) ≤ 1.391 := by
  have hb : ∏ l ∈ Finset.Icc 3 N, (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ l) ≤
      ∏ l ∈ Finset.Icc 3 N, (if l = 3 then (1.2027 : ℝ) else if l = 4 then 1.0825 else
        if l = 5 then 1.0370 else if l = 6 then 1.0174 else if l = 7 then 1.0084
        else 1.0041) := by
    apply Finset.prod_le_prod (fun l _ => zeta_nonneg l)
    intro l hl
    rw [Finset.mem_Icc] at hl
    obtain ⟨h1, h2⟩ := hl
    have h3 : l ≤ 8 := h2.trans hN
    interval_cases l
    · simpa using zeta_three_le
    · simpa using zeta_four_le
    · simpa using zeta_five_le
    · simpa using zeta_six_le
    · simpa using zeta_seven_le
    · simpa using zeta_eight_le
  refine hb.trans ?_
  interval_cases N <;> norm_num [Finset.prod_Icc_succ_top]

theorem prod_three_tail (n : ℕ) :
    ∏ l ∈ Finset.Icc 3 (n + 8), (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ l) ≤
      1.398 * (1 - 0.0047 * (1 / 2) ^ n) := by
  induction n with
  | zero =>
    refine (prod_three_eight 8 le_rfl).trans ?_
    norm_num
  | succ n ih =>
    rw [show n + 1 + 8 = (n + 8) + 1 by ring, Finset.prod_Icc_succ_top (by omega)]
    have h1 := zeta_tail_le n
    have hx : (0 : ℝ) ≤ (1 / 2) ^ n := by positivity
    have hx1 : ((1 : ℝ) / 2) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    refine (mul_le_mul ih h1 (zeta_nonneg _) (by nlinarith)).trans ?_
    rw [pow_succ]
    nlinarith [mul_nonneg hx hx]

theorem prod_three_le (N : ℕ) :
    ∏ l ∈ Finset.Icc 3 N, (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ l) ≤ 1.398 := by
  rcases le_total N 8 with h | h
  · exact (prod_three_eight N h).trans (by norm_num)
  · obtain ⟨n, rfl⟩ : ∃ n, N = n + 8 := ⟨N - 8, by omega⟩
    refine (prod_three_tail n).trans ?_
    have hx : (0 : ℝ) ≤ (1 / 2) ^ n := by positivity
    nlinarith

theorem prod_two_lt (N : ℕ) :
    ∏ l ∈ Finset.Icc 2 N, (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ l) < 2.3 := by
  rcases lt_or_ge N 2 with h | h
  · rw [Finset.Icc_eq_empty (by omega)]
    norm_num
  · have e : Finset.Icc 2 N = insert 2 (Finset.Icc 3 N) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [e, Finset.prod_insert (by simp)]
    refine (mul_le_mul zeta_two_le (prod_three_le N)
      (Finset.prod_nonneg fun l _ => zeta_nonneg l) (by norm_num)).trans_lt ?_
    norm_num

theorem sphere_le (l : ℕ) (hl : 1 ≤ l) :
    2 * Real.pi ^ l / ((l - 1).factorial : ℝ) ≤ 32.5 := by
  have h1 := Real.pi_lt_d4
  have h0 := Real.pi_pos
  have hp : ∀ k : ℕ, π ^ k ≤ (3.1416 : ℝ) ^ k := fun k => pow_le_pow_left₀ h0.le h1.le k
  have tail : ∀ n : ℕ, 2 * Real.pi ^ (n + 4) / ((n + 3).factorial : ℝ) ≤ 32.5 := by
    intro n
    induction n with
    | zero =>
      have := hp 4
      norm_num [Nat.factorial] at this ⊢
      linarith
    | succ n ih =>
      refine le_trans ?_ ih
      have hf : (0 : ℝ) < ((n + 3).factorial : ℝ) := by positivity
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      rw [show n + 1 + 3 = (n + 3) + 1 by ring, Nat.factorial_succ,
        show n + 1 + 4 = (n + 4) + 1 by ring, pow_succ]
      push_cast
      rw [div_le_div_iff₀ (by positivity) hf]
      have hq : 0 ≤ 2 * π ^ (n + 4) * ((n + 3).factorial : ℝ) := by positivity
      have : π ≤ (n : ℝ) + 3 + 1 := by linarith
      nlinarith [mul_le_mul_of_nonneg_left this hq]
  rcases le_or_gt 4 l with h | h
  · obtain ⟨n, rfl⟩ : ∃ n, l = n + 4 := ⟨l - 4, by omega⟩
    exact tail n
  · have := hp l
    interval_cases l <;> norm_num [Nat.factorial] at this ⊢ <;> linarith

end ZetaProd

theorem zetaProd_sphereVolume_bounds :
    (∀ N : ℕ, ∏ l ∈ Finset.Icc 2 N, (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ l) < 2.3) ∧
    (∀ N : ℕ, ∏ l ∈ Finset.Icc 3 N, (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ l) < 1.4) ∧
    ∀ l : ℕ, 1 ≤ l → 2 * Real.pi ^ l / ((l - 1).factorial : ℝ) ≤ 32.5 :=
  ⟨ZetaProd.prod_two_lt, fun N => (ZetaProd.prod_three_le N).trans_lt (by norm_num),
    ZetaProd.sphere_le⟩

end GlobalTheory
