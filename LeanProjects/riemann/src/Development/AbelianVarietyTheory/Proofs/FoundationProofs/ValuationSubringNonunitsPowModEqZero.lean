import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory

open Polynomial in

theorem cgA_pow_of_mem_nonunits {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ)
    [hl : Fact l.Prime] (A : ValuationSubring Ω) (hlA : ((l : ℕ) : Ω) ∈ A.nonunits)
    (x : Ω) (hx : x ∈ A.nonunits) : ∃ k : ℕ, CgA A l 1 (x ^ k) 0 := by
  classical
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hl0 : ((l : ℕ) : Ω) ≠ 0 := by exact_mod_cast hl.out.ne_zero
  have hvl : A.valuation (l : Ω) < 1 := (A.mem_nonunits_iff).1 hlA
  have hvx : A.valuation x < 1 := (A.mem_nonunits_iff).1 hx
  have hvl0 : A.valuation (l : Ω) ≠ 0 := by simpa using hl0
  have key : ∀ k : ℕ, A.valuation x ^ k ≤ A.valuation (l : Ω) → CgA A l 1 (x ^ k) 0 := by
    intro k hk
    refine ⟨x ^ k / l, ?_, ?_⟩
    · rw [← A.valuation_le_one_iff, map_div₀, map_pow]
      exact (div_le_one₀ (zero_lt_iff.2 hvl0)).2 hk
    · rw [sub_zero, pow_one]; field_simp
  by_contra H
  push_neg at H
  have hlt : ∀ k : ℕ, A.valuation (l : Ω) < A.valuation x ^ k :=
    fun k => not_le.1 (fun h => H k (key k h))
  have hx0 : x ≠ 0 := by
    intro h
    have := hlt 1
    simp [h] at this
  have hvx0 : A.valuation x ≠ 0 := by simpa using hx0

  have hint : ∀ n : ℤ, A.valuation (n : Ω) ≤ 1 := fun n =>
    (A.valuation_le_one_iff _).2 (intCast_mem A n)
  have hdvd : ∀ n : ℤ, (l : ℤ) ∣ n → A.valuation (n : Ω) ≤ A.valuation (l : Ω) := by
    rintro n ⟨m, rfl⟩
    push_cast
    rw [map_mul]
    exact mul_le_of_le_one_right' (hint m)
  have hpl : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl.out
  have hunit : ∀ n : ℤ, ¬ (l : ℤ) ∣ n → A.valuation (n : Ω) = 1 := by
    intro n hn
    refine le_antisymm (hint n) (not_lt.1 fun h => ?_)
    obtain ⟨a, b, hab⟩ := (Prime.coprime_iff_not_dvd hpl).2 hn
    have h1 : ((a : Ω) * (l : Ω) + (b : Ω) * (n : Ω)) = 1 := by exact_mod_cast hab
    have h2 : A.valuation ((a : Ω) * (l : Ω) + (b : Ω) * (n : Ω)) < 1 := by
      apply Valuation.map_add_lt
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint a)) hvl
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint b)) h
    rw [h1, map_one] at h2
    exact lt_irrefl _ h2

  obtain ⟨p, hp0, hpx⟩ := (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).2 (Algebra.IsAlgebraic.isAlgebraic x)
  set q := p.primPart with hqdef
  have hqprim : q.IsPrimitive := isPrimitive_primPart p
  have hqx : aeval x q = 0 := by
    have hc : p.content ≠ 0 := by
      intro h; exact hp0 ((content_eq_zero_iff).1 h)
    have h := hpx
    rw [eq_C_content_mul_primPart p, map_mul, aeval_C] at h
    rcases mul_eq_zero.1 h with h' | h'
    · exfalso; apply hc; simpa using h'
    · exact h'
  have hex : ∃ i, ¬ (l : ℤ) ∣ q.coeff i := by
    by_contra h
    push_neg at h
    have hu := hqprim (l : ℤ) ((C_dvd_iff_dvd_coeff _ _).2 h)
    exact hpl.not_unit hu
  set i0 := Nat.find hex with hi0
  have hi0spec : ¬ (l : ℤ) ∣ q.coeff i0 := Nat.find_spec hex
  have hi0min : ∀ i < i0, (l : ℤ) ∣ q.coeff i := fun i hi => by
    simpa using Nat.find_min hex hi
  have hi0deg : i0 < q.natDegree + 1 := by
    by_contra h
    apply hi0spec
    rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    exact dvd_zero _
  set f : ℕ → Ω := fun i => (q.coeff i : Ω) * x ^ i with hf
  have hsum : aeval x q = ∑ i ∈ Finset.range (q.natDegree + 1), f i := by
    rw [aeval_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hf, zsmul_eq_mul]
  have hfi0 : A.valuation (f i0) = A.valuation x ^ i0 := by
    simp only [hf, map_mul, map_pow, hunit _ hi0spec, one_mul]
  have hg : A.valuation x ^ i0 ≠ 0 := pow_ne_zero _ hvx0
  have hrest : A.valuation (∑ i ∈ (Finset.range (q.natDegree + 1)).erase i0, f i)
      < A.valuation x ^ i0 := by
    apply Valuation.map_sum_lt _ hg
    intro i hi
    have hne : i ≠ i0 := Finset.ne_of_mem_erase hi
    simp only [hf, map_mul, map_pow]
    rcases lt_or_gt_of_ne hne with h | h
    · calc A.valuation (q.coeff i : Ω) * A.valuation x ^ i
            ≤ A.valuation (l : Ω) * 1 :=
              mul_le_mul' (hdvd _ (hi0min i h)) (pow_le_one₀ zero_le' hvx.le)
        _ = A.valuation (l : Ω) := mul_one _
        _ < A.valuation x ^ i0 := hlt i0
    · calc A.valuation (q.coeff i : Ω) * A.valuation x ^ i
            ≤ 1 * A.valuation x ^ i := mul_le_mul' (hint _) le_rfl
        _ = A.valuation x ^ i := one_mul _
        _ < A.valuation x ^ i0 := pow_lt_pow_right_of_lt_one₀ (zero_lt_iff.2 hvx0) hvx h
  have htot : A.valuation (aeval x q) = A.valuation x ^ i0 := by
    rw [hsum, ← Finset.add_sum_erase _ _ (Finset.mem_range.2 hi0deg),
      Valuation.map_add_eq_of_lt_left _ (by rw [hfi0]; exact hrest), hfi0]
  rw [hqx, map_zero] at htot
  exact hg htot.symm

end GlobalTheory
