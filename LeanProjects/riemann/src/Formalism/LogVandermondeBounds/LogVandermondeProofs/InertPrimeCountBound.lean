import Formalism.LogVandermondeBounds.LogVandermondeVariationUnbounded

namespace Formalism.LogVandermondeBounds.StandardLattice

open Finset

section Inert

variable {L : Type} [Field L] [Fintype L] [DecidableEq L] {q : ℕ}

lemma q_two_le (hq : Fintype.card L = q ^ 2) : 2 ≤ q := by
  have h := Fintype.one_lt_card (α := L)
  rw [hq] at h
  by_contra h'
  push Not at h'
  interval_cases q <;> simp at h

lemma frob_sub (hq : Fintype.card L = q ^ 2) (a b : L) : (a - b) ^ q = a ^ q - b ^ q := by
  obtain ⟨n, hp, hn⟩ := FiniteField.card L (ringChar L)
  have hd : q ∣ ringChar L ^ (n : ℕ) := by
    rw [← hn, hq]; exact Dvd.intro _ (pow_two q).symm
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 hd
  subst hk
  have : Fact (ringChar L).Prime := ⟨hp⟩
  exact sub_pow_char_pow a b k

lemma pow_q_sq (hq : Fintype.card L = q ^ 2) (x : L) : x ^ (q ^ 2) = x := by
  rw [← hq]; exact FiniteField.pow_card x

lemma norm_fixed (hq : Fintype.card L = q ^ 2) (x : L) : (x ^ (q + 1)) ^ q = x ^ (q + 1) := by
  rw [← pow_mul, show (q + 1) * q = q ^ 2 + q by ring, pow_add, pow_q_sq hq, ← pow_succ']

lemma root_bound (d : ℕ) (hd : 0 < d) (c : L) : (univ.filter (fun x : L => x ^ d = c)).card ≤ d := by
  calc _ ≤ (Polynomial.nthRoots d c).toFinset.card := by
        apply card_le_card
        intro x hx
        simp only [mem_filter, mem_univ, true_and] at hx
        simp [Multiset.mem_toFinset, Polynomial.mem_nthRoots hd, hx]
    _ ≤ Multiset.card (Polynomial.nthRoots d c) := Multiset.toFinset_card_le _
    _ ≤ d := Polynomial.card_nthRoots d c

def Sfix (L : Type) [Field L] [Fintype L] [DecidableEq L] (q : ℕ) : Finset L :=
  univ.filter (fun c : L => c ≠ 0 ∧ c ^ q = c)

def fib (q : ℕ) (d : L) : Finset L := (univ.erase 0).filter (fun u : L => u ^ (q + 1) = d)

lemma norm_maps (hq : Fintype.card L = q ^ 2) :
    ((univ.erase (0 : L) : Finset L) : Set L).MapsTo (fun u => u ^ (q + 1)) (Sfix L q) := by
  intro u hu
  simp only [coe_erase, coe_univ, Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and] at hu
  simp only [Sfix, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
  exact ⟨pow_ne_zero _ hu, norm_fixed hq u⟩

lemma pigeon (hq : Fintype.card L = q ^ 2) :
    (Sfix L q).card = q - 1 ∧ ∀ d ∈ Sfix L q, (fib q d).card = q + 1 := by
  have h2 := q_two_le hq
  have htot := card_eq_sum_card_fiberwise (norm_maps hq)
  rw [card_erase_of_mem (mem_univ _), card_univ, hq] at htot
  have hfib : ∀ d ∈ Sfix L q, (fib q d).card ≤ q + 1 := by
    intro d _
    calc (fib q d).card ≤ (univ.filter (fun x : L => x ^ (q + 1) = d)).card := by
          apply card_le_card
          intro x
          simp only [fib, mem_filter, mem_erase, mem_univ, and_true, true_and]
          exact fun h => h.2
      _ ≤ q + 1 := root_bound _ (by omega) d
  have hS : (Sfix L q).card ≤ q - 1 := by
    calc _ ≤ (univ.filter (fun x : L => x ^ (q - 1) = 1)).card := by
          apply card_le_card
          intro c hc
          simp only [Sfix, mem_filter, mem_univ, true_and] at hc ⊢
          obtain ⟨h0, h1⟩ := hc
          have : c ^ (q - 1) * c = 1 * c := by
            rw [← pow_succ, Nat.sub_add_cancel (by omega), h1, one_mul]
          exact mul_right_cancel₀ h0 this
      _ ≤ q - 1 := root_bound _ (by omega) 1
  have hle : ∑ d ∈ Sfix L q, (fib q d).card ≤ ∑ d ∈ Sfix L q, (q + 1) := sum_le_sum hfib
  rw [sum_const, smul_eq_mul] at hle
  have htot' : q ^ 2 - 1 = ∑ d ∈ Sfix L q, (fib q d).card := htot
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 2 := ⟨q - 2, by omega⟩
  have hsq : (r + 2) ^ 2 - 1 = (r + 1) * (r + 3) := by
    have : (r + 2) ^ 2 = (r + 1) * (r + 3) + 1 := by ring
    omega
  have hS' : (Sfix L (r + 2)).card = r + 1 := by
    have h3 : (r + 1) * (r + 3) ≤ (Sfix L (r + 2)).card * (r + 3) := by
      rw [← hsq, htot']; exact hle
    have h4 : (Sfix L (r + 2)).card ≤ r + 1 := by simpa using hS
    have h5 := Nat.le_of_mul_le_mul_right h3 (by omega)
    omega
  refine ⟨by simpa using hS', ?_⟩
  have heq : ∑ d ∈ Sfix L (r + 2), (fib (r + 2) d).card = ∑ d ∈ Sfix L (r + 2), (r + 2 + 1) := by
    rw [← htot', hsq, sum_const, smul_eq_mul, hS']
  exact (sum_eq_sum_iff_of_le hfib).1 heq

def Ncnt (q M : ℕ) (c : L) : ℕ := Fintype.card {x : Fin M → L // ∑ i, x i ^ (q + 1) = c}

def Az (q M : ℕ) : ℤ := (q : ℤ) ^ M * ((q : ℤ) ^ M - (-1) ^ M)

def Zz (q M : ℕ) : ℤ := (q : ℤ) ^ (2 * M) + (-1) ^ M * ((q : ℤ) ^ (M + 1) - (q : ℤ) ^ M)

end Inert

end Formalism.LogVandermondeBounds.StandardLattice
