import Mathlib
import Formalism.TameInertiaTowers.StatementGroup

namespace Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation

lemma vEq (z : ℤ) (hz : z ≠ 0) : (padicValInt 2 z : ℕ∞) = emultiplicity (2 : ℤ) z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [show padicValInt 2 z = padicValNat 2 z.natAbs from rfl,
    padicValNat_eq_emultiplicity (Int.natAbs_ne_zero.mpr hz), Int.emultiplicity_natAbs]
  rfl

lemma vNat (e : ℕ) (he : e ≠ 0) : (padicValNat 2 e : ℕ∞) = emultiplicity (2 : ℤ) (e : ℤ) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [padicValNat_eq_emultiplicity he, ← Int.natCast_emultiplicity]
  rfl

lemma pow_sub_one_ne (a : ℤ) (ha2 : a ^ 2 ≠ 1) (e : ℕ) (he : 0 < e) : a ^ e - 1 ≠ 0 := by
  intro h
  apply ha2
  have h1 : |a| ^ e = 1 := by rw [pow_abs, sub_eq_zero.mp h, abs_one]
  have h2 : |a| = 1 := (pow_eq_one_iff_of_nonneg (abs_nonneg a) he.ne').mp h1
  rw [← sq_abs, h2, one_pow]

lemma geom_odd (a : ℤ) (ha : Odd a) (n : ℕ) : (Odd (∑ i ∈ Finset.range n, a ^ i) ↔ Odd n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : ¬ Even (a ^ n) := Int.not_even_iff_odd.mpr (ha.pow)
    rw [Finset.sum_range_succ, Int.odd_add, ih]
    simp [hp, Nat.odd_add_one]

lemma sq_split (a : ℤ) (ha2 : a ^ 2 ≠ 1) :
    padicValInt 2 (a ^ 2 - 1) = padicValInt 2 (a - 1) + padicValInt 2 (a + 1) := by
  have h1 : a - 1 ≠ 0 := by
    intro h; apply ha2; rw [sub_eq_zero.mp h]; norm_num
  have h2 : a + 1 ≠ 0 := by
    intro h; apply ha2; rw [show a = -1 by linarith]; norm_num
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [show a ^ 2 - 1 = (a - 1) * (a + 1) by ring, padicValInt.mul h1 h2]

lemma val_even (a : ℤ) (ha : Odd a) (ha2 : a ^ 2 ≠ 1) (e : ℕ) (he : 0 < e) (hev : Even e) :
    padicValInt 2 (a ^ e - 1) + 1 = padicValInt 2 (a ^ 2 - 1) + padicValNat 2 e := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne := pow_sub_one_ne a ha2 e he
  have h1 : a - 1 ≠ 0 := by
    intro h; apply ha2; rw [sub_eq_zero.mp h]; norm_num
  have h2 : a + 1 ≠ 0 := by
    intro h; apply ha2; rw [show a = -1 by linarith]; norm_num
  have hdiv : (2 : ℤ) ∣ a - 1 := by
    obtain ⟨k, rfl⟩ := ha; exact ⟨k, by ring⟩
  have hnd : ¬ (2 : ℤ) ∣ a := by
    rw [← even_iff_two_dvd]; exact Int.not_even_iff_odd.mpr ha
  have key := Int.two_pow_sub_pow (y := 1) (n := e) hdiv hnd hev
  rw [one_pow, ← vEq _ hne, ← vEq _ h2, ← vEq _ h1, ← vNat _ he.ne'] at key
  rw [sq_split a ha2]
  norm_cast at key
  omega

lemma val_odd (a : ℤ) (ha : Odd a) (ha2 : a ^ 2 ≠ 1) (e : ℕ) (hod : Odd e) :
    padicValInt 2 (a ^ e - 1) = padicValInt 2 (a - 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : a - 1 ≠ 0 := by
    intro h; apply ha2; rw [sub_eq_zero.mp h]; norm_num
  have hs : Odd (∑ i ∈ Finset.range e, a ^ i) := (geom_odd a ha e).mpr hod
  have hs0 : (∑ i ∈ Finset.range e, a ^ i) ≠ 0 := fun h => by
    rw [h] at hs; exact Int.not_even_iff_odd.mpr hs ⟨0, by norm_num⟩
  have hnd : ¬ ((2 : ℕ) : ℤ) ∣ ∑ i ∈ Finset.range e, a ^ i := by
    intro hd
    exact Int.not_even_iff_odd.mpr hs (even_iff_two_dvd.mpr (by exact_mod_cast hd))
  rw [← mul_geom_sum, padicValInt.mul h1 hs0, padicValInt.eq_zero_of_not_dvd hnd, add_zero]

lemma powEq (N m : ℕ) (a : ℤ) (hz : a ^ m - 1 ≠ 0) :
    (a : ZMod (2 ^ N)) ^ m = 1 ↔ N ≤ padicValInt 2 (a ^ m - 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h0 : ((a : ZMod (2 ^ N)) ^ m = 1) ↔ (((a ^ m - 1 : ℤ)) : ZMod (2 ^ N)) = 0 := by
    push_cast; exact sub_eq_zero.symm
  rw [h0, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h2 := padicValInt_dvd_iff (p := 2) N (a ^ m - 1)
  push_cast at h2 ⊢
  rw [h2, or_iff_right hz]

end Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation

namespace Formalism.TwoAdicCyclotomicDecomposition

open TwoAdicValuation in
theorem twoAdicVal : TwoAdicVal := by
  intro a ha ha2 e he
  by_cases hev : Even e
  · have h := val_even a ha ha2 e he hev
    have hl : padicValNat 2 e ≤ Nat.log 2 e := padicValNat_le_nat_log e
    rw [if_pos hev]
    constructor <;> omega
  · have hod : Odd e := Nat.not_even_iff_odd.mp hev
    have h := val_odd a ha ha2 e hod
    have hs := sq_split a ha2
    rw [if_neg hev]
    constructor <;> omega

open TwoAdicValuation in
theorem twoAdicOrder : TwoAdicOrder := by
  intro N a ha ha2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  split_ifs with h1
  · rw [h1, orderOf_one]
  · have hv : ∀ j : ℕ, 1 ≤ j →
        padicValInt 2 (a ^ 2 ^ j - 1) + 1 = padicValInt 2 (a ^ 2 - 1) + j := by
      intro j hj
      have := val_even a ha ha2 (2 ^ j) (by positivity) (Nat.even_pow.mpr ⟨even_two, by omega⟩)
      rwa [padicValNat.prime_pow] at this
    have hpow : ∀ j : ℕ,
        ((a : ZMod (2 ^ N)) ^ 2 ^ j = 1 ↔ N ≤ padicValInt 2 (a ^ 2 ^ j - 1)) := fun j =>
      powEq N (2 ^ j) a (pow_sub_one_ne a ha2 _ (by positivity))
    set K := max 1 (N + 1 - padicValInt 2 (a ^ 2 - 1)) with hK
    have hK1 : 1 ≤ K := le_max_left _ _
    have hK2 : N + 1 - padicValInt 2 (a ^ 2 - 1) ≤ K := le_max_right _ _
    have hK3 : K = 1 ∨ K = N + 1 - padicValInt 2 (a ^ 2 - 1) := max_choice _ _
    clear_value K
    obtain ⟨n, rfl⟩ : ∃ n, K = n + 1 := ⟨K - 1, by omega⟩
    apply orderOf_eq_prime_pow
    · rcases Nat.eq_zero_or_pos n with h0 | h0
      · rw [h0, pow_zero, pow_one]; exact h1
      · rw [hpow]
        have := hv n h0
        omega
    · rw [hpow]
      have := hv (n + 1) (by omega)
      omega

end Formalism.TwoAdicCyclotomicDecomposition
