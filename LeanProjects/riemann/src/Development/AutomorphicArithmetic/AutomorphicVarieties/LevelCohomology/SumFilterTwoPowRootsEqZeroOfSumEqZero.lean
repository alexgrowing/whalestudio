import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.ExistsPowDvdSubOfTwoPowDvdSubOne

theorem UpperTheory.sum_filter_two_pow_roots_eq_zero_of_sum_eq_zero :
    ∀ (k : Type) [Field k] (l : ℕ) [Fact l.Prime] [CharP k l], l ≠ 2 → ∀ (d e n : ℕ) (a : ℤ), 2 ≤ e → Odd a → ((l ^ d : ℕ) : ℤ) = 1 + 2 ^ e * a → ∀ (ι : Type) [Fintype ι] [DecidableEq k] (z g : ι → k), (∀ i, z i = 0 ∨ z i ^ (2 ^ n) = 1) → (∀ i, g i ^ (l ^ d) = g i) → ∑ i, z i * g i = 0 → ∑ i ∈ Finset.univ.filter (fun i => z i ^ (2 ^ e) = 1), z i * g i = 0 := by
  intro k _ l _ _ hl2 d e n a he ha hq ι _ _ z g hz hg hsum
  have hlp : l.Prime := Fact.out
  set N := n + e with hN
  have hzN : ∀ i, z i = 0 ∨ z i ^ (2 ^ N) = 1 := by
    intro i
    rcases hz i with h | h
    · exact Or.inl h
    · right
      rw [hN, pow_add, pow_mul, h, one_pow]
  have hgj : ∀ (j : ℕ) (i : ι), g i ^ ((l ^ d) ^ j) = g i := by
    intro j i
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, pow_mul, ih, hg]
  have hA : ∀ m : ℕ, ∑ i, z i ^ (1 + 2 ^ e * m) * g i = 0 := by
    intro m
    obtain ⟨j, hj⟩ := UpperTheory.exists_pow_dvd_sub_of_two_pow_dvd_sub_one ((l ^ d : ℕ) : ℤ) a (1 + 2 ^ e * (m : ℤ)) e N he ha hq (by simp)
    have e1 : (l ^ d) ^ j = l ^ (d * j) := (pow_mul l d j).symm
    have hpow : (∑ i, z i * g i) ^ ((l ^ d) ^ j) = ∑ i, z i ^ ((l ^ d) ^ j) * g i := by
      rw [e1, sum_pow_char_pow]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_pow, ← e1, hgj]
    have hzero : ∑ i, z i ^ ((l ^ d) ^ j) * g i = 0 := by
      rw [← hpow, hsum, zero_pow (pow_ne_zero _ (pow_ne_zero _ hlp.ne_zero))]
    rw [← hzero]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rcases hzN i with h | h
    · rw [h, zero_pow (by positivity), zero_pow (pow_ne_zero _ (pow_ne_zero _ hlp.ne_zero))]
    · have hord : orderOf (z i) ∣ 2 ^ N := orderOf_dvd_of_pow_eq_one h
      have hmod : (1 + 2 ^ e * m) ≡ (l ^ d) ^ j [MOD orderOf (z i)] := by
        apply Nat.ModEq.of_dvd hord
        rw [Nat.modEq_iff_dvd]
        push_cast
        exact hj
      rw [← pow_mod_orderOf, show (1 + 2 ^ e * m) % orderOf (z i) = (l ^ d) ^ j % orderOf (z i) from hmod, pow_mod_orderOf]
  have hB : ∀ i, ∑ m ∈ Finset.range (2 ^ n), z i ^ (1 + 2 ^ e * m) = if z i ^ (2 ^ e) = 1 then (2 ^ n : k) * z i else 0 := by
    intro i
    have hterm : ∀ m : ℕ, z i ^ (1 + 2 ^ e * m) = z i * (z i ^ 2 ^ e) ^ m := by
      intro m
      rw [pow_add, pow_one, pow_mul]
    simp_rw [hterm, ← Finset.mul_sum]
    split_ifs with h
    · simp [h, mul_comm]
    · rcases hzN i with h0 | h1
      · simp [h0]
      · have hw : (z i ^ 2 ^ e) ^ (2 ^ n) = 1 := by
          rw [← pow_mul, ← pow_add, add_comm]
          exact h1
        rw [geom_sum_eq h, hw, sub_self, zero_div, mul_zero]
  have htot : ∑ m ∈ Finset.range (2 ^ n), ∑ i, z i ^ (1 + 2 ^ e * m) * g i = 0 :=
    Finset.sum_eq_zero fun m _ => hA m
  rw [Finset.sum_comm] at htot
  simp_rw [← Finset.sum_mul, hB, ite_mul, zero_mul] at htot
  rw [← Finset.sum_filter] at htot
  simp_rw [mul_assoc] at htot
  rw [← Finset.mul_sum] at htot
  have h2 : (2 : k) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : k) = 0 := by exact_mod_cast h
    have := (CharP.cast_eq_zero_iff k l 2).mp h'
    exact hl2 ((Nat.prime_dvd_prime_iff_eq hlp Nat.prime_two).mp this)
  exact (mul_eq_zero.mp htot).resolve_left (pow_ne_zero _ h2)
