import Mathlib

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf.ValuationPow

open Finset

variable {LL : Type} [Field LL] (v : AddValuation LL (WithTop ℚ))

theorem v_nat_nonneg (k : ℕ) : (0 : WithTop ℚ) ≤ v (k : LL) := by
  induction k with
  | zero => simp
  | succ n ih =>
    push_cast
    exact le_trans (le_min ih (by simp)) (AddValuation.map_add v (n : LL) 1)

theorem v_int_nonneg (a : ℤ) : (0 : WithTop ℚ) ≤ v (a : LL) := by
  cases a with
  | ofNat n => simpa using v_nat_nonneg v n
  | negSucc n =>
    first
    | (rw [Int.cast_negSucc, AddValuation.map_neg]; exact v_nat_nonneg v (n + 1))
    | simpa [Int.cast_negSucc] using v_nat_nonneg v (n + 1)

private theorem withTop_rat_add_pos_of_nonneg_of_pos {a b : WithTop ℚ} (ha : 0 ≤ a) (hb : 0 < b) : 0 < a + b :=
  lt_of_lt_of_le hb (le_add_of_nonneg_left ha)

private theorem exists_int_bezout_of_coprime (p m : ℕ) (h : Nat.Coprime p m) :
    ∃ a b : ℤ, a * (p : ℤ) + b * (m : ℤ) = 1 := by
  refine ⟨Nat.gcdA p m, Nat.gcdB p m, ?_⟩
  have h2 := Nat.gcd_eq_gcd_ab p m
  rw [Nat.Coprime.gcd_eq_one h] at h2
  push_cast at h2
  first
  | linear_combination -h2
  | linarith
  | nlinarith

theorem v_nat_eq_zero (p : ℕ) (hp : p.Prime) (hvp : 0 < v (p : LL)) (m : ℕ) (hm : ¬ p ∣ m) :
    v (m : LL) = 0 := by
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hm
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * (p : ℤ) + b * (m : ℤ) = 1 := by
    first
    | exact Nat.isCoprime_iff_coprime.mpr hcop
    | exact exists_int_bezout_of_coprime p m hcop
  have h1 : (a : LL) * (p : LL) + (b : LL) * (m : LL) = 1 := by
    first
    | exact_mod_cast congrArg (Int.cast : ℤ → LL) hab
    | (have h := congrArg (Int.cast : ℤ → LL) hab; push_cast at h; exact h)
  refine le_antisymm ?_ (v_nat_nonneg v m)
  by_contra hlt
  push_neg at hlt
  have hA : 0 < v ((a : LL) * (p : LL)) := by
    rw [AddValuation.map_mul]; exact withTop_rat_add_pos_of_nonneg_of_pos (v_int_nonneg v a) hvp
  have hB : 0 < v ((b : LL) * (m : LL)) := by
    rw [AddValuation.map_mul]; exact withTop_rat_add_pos_of_nonneg_of_pos (v_int_nonneg v b) hlt
  have h2 := AddValuation.map_add v ((a : LL) * (p : LL)) ((b : LL) * (m : LL))
  rw [h1, AddValuation.map_one] at h2
  exact absurd (lt_of_lt_of_le (lt_min hA hB) h2) (lt_irrefl 0)

theorem v_nonneg_of (w : LL) (hw : 0 < v (w - 1)) : (0 : WithTop ℚ) ≤ v w := by
  have h := AddValuation.map_add v (w - 1) 1
  rw [sub_add_cancel, AddValuation.map_one] at h
  exact le_trans (le_min hw.le le_rfl) h

private theorem val_pow_nonneg_of_nonneg (w : LL) (hw : (0 : WithTop ℚ) ≤ v w) (j : ℕ) :
    (0 : WithTop ℚ) ≤ v (w ^ j) := by
  induction j with
  | zero => simp
  | succ n ih => rw [pow_succ, AddValuation.map_mul]; exact add_nonneg ih hw

theorem v_sum_pow_nonneg (w : LL) (hw : (0 : WithTop ℚ) ≤ v w) (i : ℕ) :
    (0 : WithTop ℚ) ≤ v (∑ j ∈ range i, w ^ j) := by
  induction i with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact le_trans (le_min ih (val_pow_nonneg_of_nonneg v w hw n)) (AddValuation.map_add v _ _)

private theorem pow_sub_one_eq_sub_one_mul_geom_sum (w : LL) (n : ℕ) :
    w ^ n - 1 = (w - 1) * ∑ j ∈ Finset.range n, w ^ j := by
  first
  | exact (mul_geom_sum w n).symm
  | (rw [mul_comm]; exact (geom_sum_mul w n).symm)

theorem v_pow_sub_one_ge (w : LL) (hw : (0 : WithTop ℚ) ≤ v w) (i : ℕ) :
    v (w - 1) ≤ v (w ^ i - 1) := by
  rw [pow_sub_one_eq_sub_one_mul_geom_sum w i, AddValuation.map_mul]
  exact le_add_of_nonneg_right (v_sum_pow_nonneg v w hw i)

private theorem geom_sum_sub_card_eq_sum_pow_sub_one (w : LL) (n : ℕ) :
    (∑ j ∈ Finset.range n, w ^ j) - (n : LL) = ∑ j ∈ Finset.range n, (w ^ j - 1) := by
  first
  | (rw [Finset.sum_sub_distrib]; simp)
  | simp [Finset.sum_sub_distrib]

private theorem le_val_sum_range_of_forall_lt (g : WithTop ℚ) (f : ℕ → LL) (n : ℕ) (h : ∀ j, j < n → g ≤ v (f j)) :
    g ≤ v (∑ j ∈ Finset.range n, f j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact le_trans (le_min (ih (fun j hj => h j (by omega))) (h n (by omega)))
      (AddValuation.map_add v _ _)

private theorem val_eq_of_val_lt_val_sub (x y : LL) (h : v y < v (x - y)) : v x = v y := by
  have h1 : v y ≤ v x := by
    have h3 := AddValuation.map_add v (x - y) y
    rw [sub_add_cancel] at h3
    exact le_trans (le_min h.le le_rfl) h3
  have h2 := AddValuation.map_add v x (-(x - y))
  rw [AddValuation.map_neg, show x + -(x - y) = y by ring] at h2
  rcases min_le_iff.mp h2 with h4 | h4
  · exact le_antisymm h4 h1
  · exact absurd h4 (not_le.mpr h)

private theorem val_sub_one_le_val_geom_sum_sub_card (w : LL) (hw : (0 : WithTop ℚ) ≤ v w) (n : ℕ) :
    v (w - 1) ≤ v ((∑ j ∈ Finset.range n, w ^ j) - (n : LL)) := by
  rw [geom_sum_sub_card_eq_sum_pow_sub_one]
  exact le_val_sum_range_of_forall_lt v (v (w - 1)) (fun j => w ^ j - 1) n
    (fun j _ => v_pow_sub_one_ge v w hw j)

theorem v_pow_coprime (p : ℕ) (hp : p.Prime) (hvp : 0 < v (p : LL)) (w : LL) (hw : 0 < v (w - 1))
    (m : ℕ) (hm : ¬ p ∣ m) : v (w ^ m - 1) = v (w - 1) := by
  have hw0 : (0 : WithTop ℚ) ≤ v w := v_nonneg_of v w hw
  have hm0 : v (m : LL) = 0 := v_nat_eq_zero v p hp hvp m hm
  have hlt : v (m : LL) < v ((∑ j ∈ Finset.range m, w ^ j) - (m : LL)) := by
    rw [hm0]; exact lt_of_lt_of_le hw (val_sub_one_le_val_geom_sum_sub_card v w hw0 m)
  have hS : v (∑ j ∈ Finset.range m, w ^ j) = 0 := (val_eq_of_val_lt_val_sub v _ _ hlt).trans hm0
  rw [pow_sub_one_eq_sub_one_mul_geom_sum w m, AddValuation.map_mul, hS, add_zero]

private theorem withTop_rat_zero_lt_one : (0 : WithTop ℚ) < 1 := by
  first
  | exact WithTop.coe_lt_coe.mpr zero_lt_one
  | exact_mod_cast (zero_lt_one : (0 : ℚ) < 1)
  | simp
  | decide

private theorem withTop_rat_one_lt_one_add_one : (1 : WithTop ℚ) < 1 + 1 := by
  first
  | exact WithTop.coe_lt_coe.mpr (by norm_num : (1 : ℚ) < 1 + 1)
  | exact_mod_cast (by norm_num : (1 : ℚ) < 1 + 1)
  | (rw [← WithTop.coe_one, ← WithTop.coe_add, WithTop.coe_lt_coe]; norm_num)
  | simp
  | decide

private theorem exists_eq_two_mul_add_one_of_prime_ne_two (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) : ∃ k, p = 2 * k + 1 := by
  rcases hp.eq_two_or_odd with h | h
  · exact absurd h hodd
  · exact ⟨p / 2, by omega⟩

private theorem sum_range_two_mul_add_one_eq (k : ℕ) : ∑ i ∈ Finset.range (2 * k + 1), i = (2 * k + 1) * k := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih]
    ring

private theorem geom_sum_sub_card_eq_sub_one_mul (w : LL) (n : ℕ) :
    (∑ j ∈ Finset.range n, w ^ j) - (n : LL) =
      (w - 1) * ((∑ j ∈ Finset.range n, (j : LL)) +
        ∑ j ∈ Finset.range n, ((∑ i ∈ Finset.range j, w ^ i) - (j : LL))) := by
  rw [geom_sum_sub_card_eq_sum_pow_sub_one, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [pow_sub_one_eq_sub_one_mul_geom_sum w j]
  ring

theorem v_pow_prime (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) (hvp : v (p : LL) = 1) (w : LL)
    (hw : 1 ≤ v (w - 1)) : v (w ^ p - 1) = v (w - 1) + 1 := by
  obtain ⟨k, hpk⟩ : ∃ k, p = 2 * k + 1 := exists_eq_two_mul_add_one_of_prime_ne_two p hp hodd
  have hw1 : 0 < v (w - 1) := lt_of_lt_of_le withTop_rat_zero_lt_one hw
  have hw0 : (0 : WithTop ℚ) ≤ v w := v_nonneg_of v w hw1
  have hN : ∑ j ∈ Finset.range p, j = p * k := by rw [hpk]; exact sum_range_two_mul_add_one_eq k
  have hA : (∑ j ∈ Finset.range p, (j : LL)) = (p : LL) * (k : LL) := by
    first
    | exact_mod_cast congrArg (Nat.cast : ℕ → LL) hN
    | (have h := congrArg (Nat.cast : ℕ → LL) hN; push_cast at h; exact h)
  have hvA : 1 ≤ v (∑ j ∈ Finset.range p, (j : LL)) := by
    rw [hA, AddValuation.map_mul, hvp]
    exact le_add_of_nonneg_right (v_nat_nonneg v k)
  have hvE : v (w - 1) ≤
      v (∑ j ∈ Finset.range p, ((∑ i ∈ Finset.range j, w ^ i) - (j : LL))) :=
    le_val_sum_range_of_forall_lt v (v (w - 1)) (fun j => (∑ i ∈ Finset.range j, w ^ i) - (j : LL)) p
      (fun j _ => val_sub_one_le_val_geom_sum_sub_card v w hw0 j)
  have hvAE : 1 ≤ v ((∑ j ∈ Finset.range p, (j : LL)) +
      ∑ j ∈ Finset.range p, ((∑ i ∈ Finset.range j, w ^ i) - (j : LL))) :=
    le_trans (le_min hvA (le_trans hw hvE)) (AddValuation.map_add v _ _)
  have hlt : v (p : LL) < v ((∑ j ∈ Finset.range p, w ^ j) - (p : LL)) := by
    rw [geom_sum_sub_card_eq_sub_one_mul w p, AddValuation.map_mul, hvp]
    exact lt_of_lt_of_le withTop_rat_one_lt_one_add_one (add_le_add hw hvAE)
  have hS : v (∑ j ∈ Finset.range p, w ^ j) = 1 := (val_eq_of_val_lt_val_sub v _ _ hlt).trans hvp
  rw [pow_sub_one_eq_sub_one_mul_geom_sum w p, AddValuation.map_mul, hS]

theorem v_pow_prime_pow (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) (hvp : v (p : LL) = 1) (w : LL) (c : ℚ)
    (hc : 1 ≤ c) (hw : v (w - 1) = (c : WithTop ℚ)) (a : ℕ) :
    v (w ^ (p ^ a) - 1) = ((c + a : ℚ) : WithTop ℚ) := by
  induction a with
  | zero => simp [hw]
  | succ n ih =>
    have hpow : w ^ (p ^ (n + 1)) = (w ^ (p ^ n)) ^ p := by
      first
      | rw [pow_succ, pow_mul]
      | rw [← pow_mul, ← pow_succ]
    have h1 : 1 ≤ v (w ^ (p ^ n) - 1) := by
      rw [ih]
      first
      | (rw [← WithTop.coe_one, WithTop.coe_le_coe]
         have h0 : (0 : ℚ) ≤ n := Nat.cast_nonneg n
         linarith)
      | (have h0 : (0 : ℚ) ≤ n := Nat.cast_nonneg n
         exact_mod_cast (by linarith : (1 : ℚ) ≤ c + n))
    rw [hpow, v_pow_prime v p hp hodd hvp (w ^ (p ^ n)) h1, ih]
    have e' : (c + ((n + 1 : ℕ) : ℚ)) = (c + n) + 1 := by push_cast; ring
    rw [e']
    first
    | rfl
    | (rw [WithTop.coe_add (c + n) 1, WithTop.coe_one])
    | norm_cast

private theorem exists_eq_prime_pow_mul_not_dvd' (p : ℕ) (hp : p.Prime) (k : ℕ) (hk : 0 < k) :
    ∃ a m : ℕ, ¬ p ∣ m ∧ k = p ^ a * m := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hdvd : p ∣ k
    · obtain ⟨j, hj⟩ := hdvd
      have hjpos : 0 < j := by
        rcases Nat.eq_zero_or_pos j with h0 | h0
        · rw [h0, mul_zero] at hj; omega
        · exact h0
      have hjlt : j < k := by
        have h2 := hp.two_le
        rw [hj]; nlinarith
      obtain ⟨a, m, hm, hjm⟩ := ih j hjlt hjpos
      exact ⟨a + 1, m, hm, by rw [hj, hjm]; ring⟩
    · exact ⟨0, k, hdvd, by simp⟩

theorem pow_ne_one (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) (hvp : v (p : LL) = 1) (u : LL)
    (hu : v (u - 1) = 1) (k : ℕ) (hk : 0 < k) : u ^ k ≠ 1 := by
  obtain ⟨a, m, hm, hkm⟩ := exists_eq_prime_pow_mul_not_dvd' p hp k hk
  have hvp' : 0 < v (p : LL) := by rw [hvp]; exact withTop_rat_zero_lt_one
  have hu' : v (u - 1) = ((1 : ℚ) : WithTop ℚ) := by
    first
    | exact hu.trans WithTop.coe_one.symm
    | (rw [hu]; rfl)
    | simp [hu]
  have h1 : v (u ^ (p ^ a) - 1) = ((1 + a : ℚ) : WithTop ℚ) :=
    v_pow_prime_pow v p hp hodd hvp u 1 le_rfl hu' a
  have h2 : 0 < v (u ^ (p ^ a) - 1) := by
    rw [h1]
    first
    | (rw [← WithTop.coe_zero, WithTop.coe_lt_coe]; positivity)
    | exact_mod_cast (by positivity : (0 : ℚ) < 1 + a)
  have h3 : v ((u ^ (p ^ a)) ^ m - 1) = v (u ^ (p ^ a) - 1) :=
    v_pow_coprime v p hp hvp' (u ^ (p ^ a)) h2 m hm
  intro heq
  have h4 : v (u ^ k - 1) = ((1 + a : ℚ) : WithTop ℚ) := by
    rw [hkm, pow_mul, h3, h1]
  rw [heq, sub_self, AddValuation.map_zero] at h4
  exact WithTop.top_ne_coe h4

theorem zpow_ne_one (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) (hvp : v (p : LL) = 1) (u : LL)
    (hu : v (u - 1) = 1) (k : ℤ) (hk : k ≠ 0) : u ^ k ≠ 1 := by
  have hn : 0 < k.natAbs := Int.natAbs_pos.mpr hk
  rcases Int.natAbs_eq k with h | h
  · rw [h, zpow_natCast]
    exact pow_ne_one v p hp hodd hvp u hu _ hn
  · rw [h, zpow_neg, zpow_natCast]
    intro h'
    exact pow_ne_one v p hp hodd hvp u hu _ hn (inv_eq_one.mp h')

end Formalism.MainNotions.N.Ln03.Pf.ValuationPow
