import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem sepIneq_four_mul_add_five_le (k : ℕ) (hk : 5 ≤ k) : 4 * k + 5 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih => rw [pow_succ]; omega

theorem sepIneq_sum_lt (q n : ℕ) (hq : 2 ≤ q) :
    ∑ p ∈ n.primeFactors, (q ^ (n / p) - 2) < q ^ (n / 2 + 1) := by
  have hinj : Set.InjOn (fun p => n / p) (n.primeFactors : Set ℕ) := by
    intro a ha b hb hab
    have ha' := Nat.mem_primeFactors.1 (Finset.mem_coe.1 ha)
    have hb' := Nat.mem_primeFactors.1 (Finset.mem_coe.1 hb)
    have h1 := Nat.div_div_self ha'.2.1 ha'.2.2
    have h2 := Nat.div_div_self hb'.2.1 hb'.2.2
    simp only at hab
    rw [← h1, ← h2, hab]
  calc ∑ p ∈ n.primeFactors, (q ^ (n / p) - 2) ≤ ∑ p ∈ n.primeFactors, q ^ (n / p) :=
        Finset.sum_le_sum fun p _ => Nat.sub_le _ _
    _ = ∑ k ∈ n.primeFactors.image (fun p => n / p), q ^ k :=
        (Finset.sum_image (f := fun k => q ^ k) hinj).symm
    _ < q ^ (n / 2 + 1) := by
        apply Nat.geomSum_lt hq
        intro k hk
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hk
        have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
        exact Nat.lt_succ_of_le (Nat.div_le_div_left hp2 (by norm_num))

theorem sepIneq_large (q n : ℕ) (hq : 2 ≤ q) (hn : 11 ≤ n) :
    (n - 1) ^ 2 + 4 * n ^ 2 * ∑ p ∈ n.primeFactors, (q ^ (n / p) - 2) < 2 * n * (q ^ n - 1) := by
  have hS := sepIneq_sum_lt q n hq
  set S := ∑ p ∈ n.primeFactors, (q ^ (n / p) - 2)
  obtain ⟨k, hk⟩ : ∃ k, n = (n / 2 + 1) + k := ⟨n - (n / 2 + 1), by omega⟩
  have hk5 : 5 ≤ k := by omega
  have h1 : 2 * n + 1 ≤ q ^ k := by
    have := sepIneq_four_mul_add_five_le k hk5
    have h2 : 2 ^ k ≤ q ^ k := Nat.pow_le_pow_left hq k
    omega
  have h2 : q ^ k ≤ q ^ (n / 2 + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : q ^ n = q ^ (n / 2 + 1) * q ^ k := by rw [← pow_add, ← hk]
  rw [h3]
  set Q := q ^ (n / 2 + 1)
  set R := q ^ k
  have h4 : Q * (2 * n + 1) ≤ Q * R := Nat.mul_le_mul_left _ h1
  obtain ⟨T, hT⟩ : ∃ T, Q * R = T + 1 := ⟨Q * R - 1, by
    have : 0 < Q * R := Nat.mul_pos (by omega) (by omega)
    omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [hT] at h4 ⊢
  simp only [Nat.add_sub_cancel]
  have h5 : 2 * (m + 1) + 1 ≤ Q := le_trans h1 h2
  have h6 : 2 * (m + 1) * (Q * (2 * (m + 1) + 1)) ≤ 2 * (m + 1) * (T + 1) := Nat.mul_le_mul_left _ h4
  have h7 : 4 * (m + 1) ^ 2 * S ≤ 4 * (m + 1) ^ 2 * Q := Nat.mul_le_mul_left _ hS.le
  have h8 : 2 * (m + 1) * (2 * (m + 1) + 1) ≤ 2 * (m + 1) * Q := Nat.mul_le_mul_left _ h5
  nlinarith

theorem sepIneq_sub (t k c : ℕ) (hc : c ≤ 2) (hk : 0 < k) : (((2 + t) ^ k - c : ℕ) : ℤ) = (2 + (t : ℤ)) ^ k - c := by
  have : 2 ≤ (2 + t) ^ k := le_trans (by omega) (Nat.le_self_pow hk.ne' _)
  rw [Nat.cast_sub (by omega)]
  push_cast
  rfl

theorem sep_numerical_ineq : ∀ q n : ℕ, 2 ≤ q → 0 < n → ¬ (q = 2 ∧ (n = 4 ∨ n = 6)) → (n - 1) ^ 2 + 4 * n ^ 2 * ∑ p ∈ n.primeFactors, (q ^ (n / p) - 2) < 2 * n * (q ^ n - 1) := by
  intro q n hq hn hex
  rcases le_or_gt 11 n with h | h
  · exact sepIneq_large q n hq h
  obtain ⟨t, rfl⟩ : ∃ t, q = 2 + t := ⟨q - 2, by omega⟩
  have e1 : Nat.primeFactors 1 = ∅ := by simp
  have e2 : Nat.primeFactors 2 = {2} := by decide +kernel
  have e3 : Nat.primeFactors 3 = {3} := by decide +kernel
  have e4 : Nat.primeFactors 4 = {2} := by decide +kernel
  have e5 : Nat.primeFactors 5 = {5} := by decide +kernel
  have e6 : Nat.primeFactors 6 = {2, 3} := by decide +kernel
  have e7 : Nat.primeFactors 7 = {7} := by decide +kernel
  have e8 : Nat.primeFactors 8 = {2} := by decide +kernel
  have e9 : Nat.primeFactors 9 = {3} := by decide +kernel
  have e10 : Nat.primeFactors 10 = {2, 5} := by decide +kernel
  have ht : (0 : ℤ) ≤ t := by positivity
  have s1 := fun k hk => sepIneq_sub t k 1 (by omega) hk
  have s2 := fun k hk => sepIneq_sub t k 2 (by omega) hk
  have ht1 : n = 4 ∨ n = 6 → (1 : ℤ) ≤ t := by omega
  have p2 : (0:ℤ) ≤ t^2 := by positivity
  have p3 : (0:ℤ) ≤ t^3 := by positivity
  have p4 : (0:ℤ) ≤ t^4 := by positivity
  have p5 : (0:ℤ) ≤ t^5 := by positivity
  have p6 : (0:ℤ) ≤ t^6 := by positivity
  have p7 : (0:ℤ) ≤ t^7 := by positivity
  have p8 : (0:ℤ) ≤ t^8 := by positivity
  have p9 : (0:ℤ) ≤ t^9 := by positivity
  have p10 : (0:ℤ) ≤ t^10 := by positivity
  interval_cases n
  · rw [e1]; simp
  · rw [e2, Finset.sum_singleton]; zify; rw [s1 _ (by norm_num), s2 _ (by norm_num)]; norm_num
    nlinarith [sq_nonneg ((t:ℤ))]
  · rw [e3, Finset.sum_singleton]; zify; rw [s1 _ (by norm_num), s2 _ (by norm_num)]; norm_num
    nlinarith
  · rw [e4, Finset.sum_singleton]; zify; rw [s1 _ (by norm_num), s2 _ (by norm_num)]; norm_num
    have := ht1 (by norm_num)
    nlinarith
  · rw [e5, Finset.sum_singleton]; zify; rw [s1 _ (by norm_num), s2 _ (by norm_num)]; norm_num
    nlinarith
  · rw [e6, Finset.sum_pair (by norm_num)]; zify; rw [s1 _ (by norm_num), s2 _ (by norm_num), s2 _ (by norm_num)]; norm_num
    have := ht1 (by norm_num)
    nlinarith
  · rw [e7, Finset.sum_singleton]; zify; rw [s1 _ (by norm_num), s2 _ (by norm_num)]; norm_num
    nlinarith
  · rw [e8, Finset.sum_singleton]; zify; rw [s1 _ (by norm_num), s2 _ (by norm_num)]; norm_num
    nlinarith
  · rw [e9, Finset.sum_singleton]; zify; rw [s1 _ (by norm_num), s2 _ (by norm_num)]; norm_num
    nlinarith
  · rw [e10, Finset.sum_pair (by norm_num)]; zify; rw [s1 _ (by norm_num), s2 _ (by norm_num), s2 _ (by norm_num)]; norm_num
    nlinarith

end GlobalTheory.CuspGL
