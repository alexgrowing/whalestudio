import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

namespace GlobalTheory.LevelSums

theorem sum_class {R : Type*} [CommRing R] (x : R) (m k n : ℕ) (hm : 0 < m) :
    ∑ a ∈ Finset.range (m * k), (if a % m = n % m then x ^ a else 0) =
      x ^ (n % m) * ∑ i ∈ Finset.range k, (x ^ m) ^ i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ, mul_add]
    congr 1
    rw [Finset.sum_eq_single (n % m)]
    · rw [if_pos (by simp), pow_add, pow_mul, mul_comm]
    · intro b hb hne
      rw [if_neg]
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (Finset.mem_range.1 hb)]
      exact hne
    · intro h
      exact absurd (Finset.mem_range.2 (Nat.mod_lt _ hm)) h

open Classical in

theorem sum_ind {R : Type*} [CommRing R] [IsDomain R] (l : ℕ) (hl : 0 < l) (x : R) (s j n : ℕ)
    (hj : 1 ≤ j) (hjs : j ≤ s) (hn : ¬ l ∣ n) (hx : x ^ l ^ s = 1) :
    ∑ a ∈ primeTo l s, (((if a % l ^ j = n % l ^ j then 1 else 0 : ℤ)) : R) * x ^ a =
      if x ^ l ^ j = 1 then (l : R) ^ (s - j) * x ^ n else 0 := by
  have hs : l ^ s = l ^ j * l ^ (s - j) := by rw [← pow_add]; congr 1; omega
  have h1 : ∑ a ∈ primeTo l s, (((if a % l ^ j = n % l ^ j then 1 else 0 : ℤ)) : R) * x ^ a =
      ∑ a ∈ Finset.range (l ^ j * l ^ (s - j)), (if a % l ^ j = n % l ^ j then x ^ a else 0) := by
    rw [← hs]
    unfold primeTo
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : a % l ^ j = n % l ^ j
    · have : ¬ l ∣ a := by
        intro ha
        have hd : l ∣ l ^ j := dvd_pow_self l (by omega)
        exact hn (((Nat.ModEq.of_dvd hd h).dvd_iff dvd_rfl).1 ha)
      simp [h, this]
    · simp [h]
  rw [h1, sum_class x _ _ n (pow_pos hl j)]
  split_ifs with h
  · rw [h, ← pow_eq_pow_mod n h]
    simp [mul_comm]
  · have h2 : (x ^ l ^ j) ^ l ^ (s - j) = 1 := by rw [← pow_mul, ← hs, hx]
    have h3 := mul_geom_sum (x ^ l ^ j) (l ^ (s - j))
    rw [h2, sub_self] at h3
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact absurd (sub_eq_zero.1 h4) h
    · rw [h4, mul_zero]

theorem pow_shift {M : Type*} [Monoid M] (l : ℕ) (ζ : ℕ → M) (h : ∀ j, ζ (j + 1) ^ l = ζ j)
    (i j : ℕ) : ζ (i + j) ^ l ^ j = ζ i := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', pow_mul, ← add_assoc, h, ih]

theorem pow_eq_one_iff_le {M : Type*} [Monoid M] (l : ℕ) (ζ : ℕ → M) (h0 : ζ 0 = 1) (h1 : ζ 1 ≠ 1)
    (h : ∀ j, ζ (j + 1) ^ l = ζ j) (i j : ℕ) : ζ i ^ l ^ j = 1 ↔ i ≤ j := by
  constructor
  · intro hij
    by_contra hlt
    obtain ⟨d, rfl⟩ : ∃ d, i = 1 + (j + d) := ⟨i - 1 - j, by omega⟩
    apply h1
    rw [← pow_shift l ζ h 1 (j + d), pow_add, pow_mul, hij, one_pow]
  · intro hij
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
    have := pow_shift l ζ h 0 i
    rw [zero_add] at this
    rw [pow_add, pow_mul, this, h0, one_pow]

theorem exists_weights : ∀ (l : ℕ) [Fact l.Prime] (ζ : ℕ → Om l), ζ 0 = 1 → ζ 1 ≠ 1 → (∀ j, ζ (j + 1) ^ l = ζ j) → ∀ s j n : ℕ, 1 ≤ j → j ≤ s → ¬ l ∣ n → ∃ lam : ℕ → ℤ, (∑ a ∈ primeTo l s, lam a = if j = 1 then (l : ℤ) ^ (s - 1) else 0) ∧ ∀ i, 1 ≤ i → i ≤ s → ∑ a ∈ primeTo l s, (lam a : Om l) * ζ i ^ a = if i = j then (l : Om l) ^ (if j = 1 then s - 1 else s - j + 1) * ζ j ^ n else 0 := by
  intro l hl ζ h0 h1 h s j n hj hjs hn
  have hl0 : 0 < l := hl.out.pos
  have hz : ∀ j, 1 ≤ j → j ≤ s →
      ∑ a ∈ primeTo l s, (if a % l ^ j = n % l ^ j then 1 else 0 : ℤ) = (l : ℤ) ^ (s - j) := by
    intro j hj hjs
    simpa using sum_ind l hl0 (1 : ℤ) s j n hj hjs hn (one_pow _)
  have hv : ∀ i, i ≤ s → ∀ j, 1 ≤ j → j ≤ s →
      ∑ a ∈ primeTo l s, (((if a % l ^ j = n % l ^ j then 1 else 0 : ℤ)) : Om l) * ζ i ^ a =
        if i ≤ j then (l : Om l) ^ (s - j) * ζ i ^ n else 0 := by
    intro i hi j hj hjs
    rw [sum_ind l hl0 (ζ i) s j n hj hjs hn ((pow_eq_one_iff_le l ζ h0 h1 h i s).2 hi)]
    simp only [pow_eq_one_iff_le l ζ h0 h1 h]
  by_cases hj1 : j = 1
  · subst hj1
    refine ⟨fun a => if a % l ^ 1 = n % l ^ 1 then 1 else 0, ?_, fun i hi his => ?_⟩
    · rw [hz 1 le_rfl hjs, if_pos rfl]
    · rw [hv i his 1 le_rfl hjs]
      by_cases e : i = 1
      · subst e; simp
      · rw [if_neg (by omega), if_neg e]
  · have hsj : s - (j - 1) = s - j + 1 := by omega
    refine ⟨fun a => l * (if a % l ^ j = n % l ^ j then 1 else 0) -
      (if a % l ^ (j - 1) = n % l ^ (j - 1) then 1 else 0), ?_, fun i hi his => ?_⟩
    · rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hz j hj hjs, hz (j - 1) (by omega) (by omega),
        if_neg hj1, hsj]
      ring
    · simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, sub_mul, mul_assoc]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hv i his j hj hjs,
        hv i his (j - 1) (by omega) (by omega), if_neg hj1, hsj]
      rcases lt_trichotomy i j with e | e | e
      · rw [if_pos e.le, if_pos (by omega), if_neg e.ne]; ring
      · subst e
        rw [if_pos le_rfl, if_neg (by omega), if_pos rfl]; ring
      · rw [if_neg (by omega), if_neg (by omega), if_neg e.ne']; ring

end GlobalTheory.LevelSums
