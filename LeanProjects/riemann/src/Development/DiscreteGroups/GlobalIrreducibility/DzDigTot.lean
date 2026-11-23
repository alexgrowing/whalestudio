import Mathlib

namespace DiscreteGroups.sglob.DzDig

open Finset

theorem card_primes_le {s : Finset ℕ} {a : ℕ} (hs : ∀ q ∈ s, q.Prime) (ha : ∀ q ∈ s, q ≤ a)
    (h2 : 2 ≤ a) : 2 * #s ≤ a + 1 := by
  have h : #s ≤ #(range ((a - 1) / 2 + 1)) := by
    apply card_le_card_of_injOn (fun x => (x - 1) / 2)
    · intro x hx
      have := ha x (mem_coe.mp hx)
      simp only [mem_coe, mem_range]
      omega
    · intro x hx y hy hxy
      have hx2 := (hs x (mem_coe.mp hx)).two_le
      have hy2 := (hs y (mem_coe.mp hy)).two_le
      have ox := (hs x (mem_coe.mp hx)).eq_two_or_odd
      have oy := (hs y (mem_coe.mp hy)).eq_two_or_odd
      simp only at hxy
      omega
  rw [card_range] at h
  omega

theorem prod_sq_le : ∀ s : Finset ℕ, (∀ q ∈ s, q.Prime) → s.Nonempty →
    (∏ q ∈ s, q) ^ 2 ≤ 4 * (2 * #s - 1) * (∏ q ∈ s, (q - 1)) ^ 2 := by
  intro s
  induction s using Finset.induction_on_max
  · intro _ hne
    exact absurd hne (by simp)
  next a s hlt ih =>
    intro hs _
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have ha2 := (hs a (mem_insert_self a s)).two_le
    have hle : ∀ q ∈ insert a s, q ≤ a := by
      intro q hq
      rcases mem_insert.mp hq with h | h
      · omega
      · exact (hlt q h).le
    have hcard := card_primes_le hs hle ha2
    rw [prod_insert ha, prod_insert ha, card_insert_of_notMem ha]
    rw [card_insert_of_notMem ha] at hcard
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    rw [show b + 1 - 1 = b by omega]
    rcases s.eq_empty_or_nonempty with hs0 | hsne
    · subst hs0
      rw [prod_empty, prod_empty, card_empty]
      norm_num <;> nlinarith [ha2]
    · have hs' : ∀ q ∈ s, q.Prime := fun q hq => hs q (mem_insert_of_mem hq)
      have ih' := ih hs' hsne
      have hs1 : 1 ≤ #s := card_pos.mpr hsne
      obtain ⟨m, hm⟩ : ∃ m, #s = m + 1 := ⟨#s - 1, by omega⟩
      rw [hm] at ih' hcard
      rw [hm]
      rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega] at ih'
      rw [show 2 * (m + 1 + 1) - 1 = 2 * m + 3 by omega]
      have hb : 2 * m + 2 ≤ b := by omega
      have h2 : (b + 1) ^ 2 * (2 * m + 1) ≤ (2 * m + 3) * b ^ 2 := by
        have := Nat.mul_le_mul_right b hb
        nlinarith
      calc ((b + 1) * ∏ q ∈ s, q) ^ 2 = (b + 1) ^ 2 * (∏ q ∈ s, q) ^ 2 := by ring
        _ ≤ (b + 1) ^ 2 * (4 * (2 * m + 1) * (∏ q ∈ s, (q - 1)) ^ 2) := Nat.mul_le_mul_left _ ih'
        _ = 4 * ((b + 1) ^ 2 * (2 * m + 1)) * (∏ q ∈ s, (q - 1)) ^ 2 := by ring
        _ ≤ 4 * ((2 * m + 3) * b ^ 2) * (∏ q ∈ s, (q - 1)) ^ 2 :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h2)
        _ = 4 * (2 * m + 3) * (b * ∏ q ∈ s, (q - 1)) ^ 2 := by ring

theorem pow_bound : ∀ t, 4 ≤ t → (t + 1) * t ≤ 4 * 2 ^ t := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih =>
    rw [pow_succ]
    nlinarith

theorem pow_le_two_pow {p n : ℕ} (hn : 1 ≤ n) (h16 : 16 * n ^ 2 < p) : p ^ (2 * n) ≤ 2 ^ p := by
  have hs : 0 < 2 * n := by omega
  have ht : 4 * (2 * n) ≤ p / (2 * n) := by
    rw [Nat.le_div_iff_mul_le hs]
    nlinarith
  have hp1 : p < (p / (2 * n) + 1) * (2 * n) := by
    nlinarith [Nat.div_add_mod p (2 * n), Nat.mod_lt p hs]
  have ht4 : 4 ≤ p / (2 * n) := by omega
  have hpt : p ≤ 2 ^ (p / (2 * n)) := by
    nlinarith [Nat.mul_le_mul_left (p / (2 * n) + 1) ht, pow_bound (p / (2 * n)) ht4]
  calc p ^ (2 * n) ≤ (2 ^ (p / (2 * n))) ^ (2 * n) := Nat.pow_le_pow_left hpt _
    _ = 2 ^ (p / (2 * n) * (2 * n)) := (pow_mul 2 _ _).symm
    _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) (Nat.div_mul_le_self p (2 * n))

theorem sq_le_totient {N : ℕ} (hN : 2 ≤ N) :
    N ^ 2 ≤ 4 * (2 * #N.primeFactors - 1) * N.totient ^ 2 := by
  have hNpos : 0 < N := by omega
  have hSp : ∀ q ∈ N.primeFactors, q.Prime := fun q hq => Nat.prime_of_mem_primeFactors hq
  have hSne : N.primeFactors.Nonempty := by
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd (show N ≠ 1 by omega)
    exact ⟨q, Nat.mem_primeFactors.mpr ⟨hq, hqd, by omega⟩⟩
  have key := prod_sq_le N.primeFactors hSp hSne
  have htot := Nat.totient_mul_prod_primeFactors N
  have hQ : 0 < ∏ q ∈ N.primeFactors, (q - 1) :=
    prod_pos (fun q hq => by have := (hSp q hq).two_le; omega)
  have h1 : (N * ∏ q ∈ N.primeFactors, (q - 1)) ^ 2
      ≤ (4 * (2 * #N.primeFactors - 1) * N.totient ^ 2) * (∏ q ∈ N.primeFactors, (q - 1)) ^ 2 := by
    rw [← htot]
    calc (N.totient * ∏ q ∈ N.primeFactors, q) ^ 2
        = N.totient ^ 2 * (∏ q ∈ N.primeFactors, q) ^ 2 := by ring
      _ ≤ N.totient ^ 2 * (4 * (2 * #N.primeFactors - 1) * (∏ q ∈ N.primeFactors, (q - 1)) ^ 2) :=
          Nat.mul_le_mul_left _ key
      _ = _ := by ring
  rw [mul_pow] at h1
  exact Nat.le_of_mul_le_mul_right h1 (pow_pos hQ 2)

theorem card_primeFactors_pos {N : ℕ} (hN : 2 ≤ N) : 1 ≤ #N.primeFactors := by
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd (show N ≠ 1 by omega)
  exact card_pos.mpr ⟨q, Nat.mem_primeFactors.mpr ⟨hq, hqd, by omega⟩⟩

theorem two_pow_card_le {N : ℕ} (hN : 0 < N) : 2 ^ #N.primeFactors ≤ N :=
  (pow_card_le_prod N.primeFactors (fun q => q) 2
      (fun q hq => (Nat.prime_of_mem_primeFactors hq).two_le)).trans
    (Nat.le_of_dvd hN (Nat.prod_primeFactors_dvd N))

theorem two_n_N_lt {p n : ℕ} (hp : p.Prime) (hn : 2 ≤ n) (h16 : 16 * n ^ 2 < p) :
    2 * n * (p ^ n - 1) < (p - 1) * (p ^ n - 1).totient := by
  have hp2 := hp.two_le
  have hpn : p ^ 2 ≤ p ^ n := Nat.pow_le_pow_right (by omega) hn
  have hp4 : 4 ≤ p ^ 2 := by nlinarith
  have hN2 : 2 ≤ p ^ n - 1 := by omega
  have hsq := sq_le_totient hN2
  have hw1 := card_primeFactors_pos hN2
  have hω := two_pow_card_le (show 0 < p ^ n - 1 by omega)
  have hφ : 0 < (p ^ n - 1).totient := Nat.totient_pos.mpr (by omega)
  have hwp : 2 * #(p ^ n - 1).primeFactors < p := by
    by_contra hc
    push_neg at hc
    have : 2 ^ p < 2 ^ p :=
      calc 2 ^ p ≤ 2 ^ (2 * #(p ^ n - 1).primeFactors) := Nat.pow_le_pow_right (by norm_num) hc
        _ = (2 ^ #(p ^ n - 1).primeFactors) ^ 2 := by ring
        _ ≤ (p ^ n - 1) ^ 2 := Nat.pow_le_pow_left hω 2
        _ < (p ^ n) ^ 2 := Nat.pow_lt_pow_left (by omega) (by norm_num)
        _ = p ^ (2 * n) := by ring
        _ ≤ 2 ^ p := pow_le_two_pow (by omega) h16
    exact lt_irrefl _ this
  have h16' : 16 * n ^ 2 ≤ p - 1 := by omega
  have hw2 : 2 * #(p ^ n - 1).primeFactors - 1 < p - 1 := by omega
  have hlt : 16 * n ^ 2 * (2 * #(p ^ n - 1).primeFactors - 1) < (p - 1) * (p - 1) :=
    calc 16 * n ^ 2 * (2 * #(p ^ n - 1).primeFactors - 1)
        ≤ (p - 1) * (2 * #(p ^ n - 1).primeFactors - 1) := Nat.mul_le_mul_right _ h16'
      _ < (p - 1) * (p - 1) := Nat.mul_lt_mul_of_pos_left hw2 (by omega)
  have hsq2 : (2 * n * (p ^ n - 1)) ^ 2 < ((p - 1) * (p ^ n - 1).totient) ^ 2 :=
    calc (2 * n * (p ^ n - 1)) ^ 2 = 4 * n ^ 2 * (p ^ n - 1) ^ 2 := by ring
      _ ≤ 4 * n ^ 2 * (4 * (2 * #(p ^ n - 1).primeFactors - 1) * (p ^ n - 1).totient ^ 2) :=
          Nat.mul_le_mul_left _ hsq
      _ = (16 * n ^ 2 * (2 * #(p ^ n - 1).primeFactors - 1)) * (p ^ n - 1).totient ^ 2 := by ring
      _ < ((p - 1) * (p - 1)) * (p ^ n - 1).totient ^ 2 :=
          Nat.mul_lt_mul_of_pos_right hlt (pow_pos hφ 2)
      _ = ((p - 1) * (p ^ n - 1).totient) ^ 2 := by ring
  by_contra hc
  push_neg at hc
  exact absurd hsq2 (not_lt.mpr (Nat.pow_le_pow_left hc 2))

end DiscreteGroups.sglob.DzDig
