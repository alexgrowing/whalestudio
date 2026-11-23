import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

namespace GlobalTheory.CompanionTheory.InertiaEigenvalues.LPow

open Polynomial in

theorem geom_poly {l : ℕ} (hl : l.Prime) :
    ∃ v : ℤ[X], ∑ i ∈ Finset.range l, (1 + (X : ℤ[X])) ^ i
      = X ^ (l - 1) + (l : ℤ[X]) * (1 + X * v) := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hl (1 : ℤ[X]) X
  have hl1 : l - 1 + 1 = l := Nat.sub_add_cancel hl.one_le
  have hg := geom_sum_mul (1 + (X : ℤ[X])) l
  have hs : ∑ i ∈ Finset.range l, (1 + (X : ℤ[X])) ^ i = X ^ (l - 1) + (l : ℤ[X]) * r := by
    apply mul_right_cancel₀ (X_ne_zero (R := ℤ))
    have e : (1 + (X : ℤ[X])) - 1 = X := by ring
    rw [e, hr] at hg
    rw [hg, add_mul, ← pow_succ, hl1]
    ring
  have r0 : r.coeff 0 = 1 := by
    have h := congrArg (Polynomial.eval 0) hs
    have hz : (0 : ℤ) ^ (l - 1) = 0 := zero_pow (by have := hl.two_le; omega)
    simp [Polynomial.eval_finset_sum, hz] at h
    have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne_zero
    rw [Polynomial.coeff_zero_eq_eval_zero]
    have h' : (l : ℤ) * Polynomial.eval 0 r = (l : ℤ) * 1 := by linarith
    exact mul_left_cancel₀ hl0 h'
  obtain ⟨v, hv⟩ := X_dvd_sub_C (p := r)
  refine ⟨v, ?_⟩
  have : r = 1 + X * v := by
    rw [← hv, r0]; simp
  rw [hs, ← this]

theorem geom_ring {R : Type*} [CommRing R] {l : ℕ} (hl : l.Prime) (y : R) :
    ∃ v : R, ∑ i ∈ Finset.range l, (1 + y) ^ i = y ^ (l - 1) + (l : R) * (1 + y * v) := by
  obtain ⟨v, hv⟩ := geom_poly hl
  refine ⟨Polynomial.aeval y v, ?_⟩
  have h := congrArg (Polynomial.aeval y) hv
  simpa [map_sum] using h

theorem pow_mem_span {R : Type*} [CommRing R] (y ξ c v : R) (a k n M : ℕ)
    (hξ : ξ = y ^ a + c * (1 + y * v)) (hM : 1 ≤ M) (hk : k ≤ a * n) :
    c ^ (n + M - 1) ∈ Ideal.span {y ^ k, ξ ^ M} := by
  set I : Ideal R := Ideal.span {y ^ k, ξ ^ M} with hI
  have hy : y ^ k ∈ I := Ideal.subset_span (by simp)
  have hx : ξ ^ M ∈ I := Ideal.subset_span (by simp)
  have hb : (-(y ^ a)) ^ n ∈ I := by
    rw [neg_pow, ← pow_mul]
    refine I.mul_mem_left _ ?_
    have : y ^ (a * n) = y ^ (a * n - k) * y ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hk]
    rw [this]
    exact I.mul_mem_left _ hy
  have h1 : (ξ + -(y ^ a)) ^ (n + M - 1) ∈ I :=
    Ideal.add_pow_mem_of_pow_mem_of_le I hx hb (by omega)
  have e1 : ξ + -(y ^ a) = c * (1 + y * v) := by rw [hξ]; ring
  rw [e1, mul_pow] at h1

  have hs := mul_neg_geom_sum (-(y * v)) k
  have hu : (1 + y * v) * ∑ i ∈ Finset.range k, (-(y * v)) ^ i = 1 - (-(y * v)) ^ k := by
    have := hs
    simpa [sub_neg_eq_add] using this
  have hyk : (-(y * v)) ^ k ∈ I := by
    rw [neg_pow, mul_pow]
    have : (-1 : R) ^ k * (y ^ k * v ^ k) = ((-1 : R) ^ k * v ^ k) * y ^ k := by ring
    rw [this]
    exact I.mul_mem_left _ hy
  rw [← Ideal.Quotient.eq_zero_iff_mem] at h1 hyk ⊢
  rw [map_mul, map_pow, map_pow] at h1
  have hu' := congrArg (Ideal.Quotient.mk I) hu
  rw [map_mul, map_sub, hyk, map_one, sub_zero] at hu'
  have hunit : IsUnit (Ideal.Quotient.mk I (1 + y * v)) := IsUnit.of_mul_eq_one _ hu'
  rw [map_pow]
  exact (hunit.pow _).mul_left_eq_zero.mp h1

theorem l_pow_mem (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (k n M : ℕ)
    (hM : 1 ≤ M) (hk : k ≤ (l - 1) * n) :
    ((l : ℕ) : Ainf l) ^ (n + M - 1) ∈ Ideal.span {AI.π₁ ^ k, AI.ξ ^ M} := by
  obtain ⟨v, hv⟩ := geom_ring (Fact.out : l.Prime) AI.π₁
  have e : 1 + AI.π₁ = WittVector.teichmuller l AI.ε1 := by
    rw [LocAinf.π₁]; ring
  rw [e] at hv
  exact pow_mem_span AI.π₁ AI.ξ (l : Ainf l) v (l - 1) k n M hv hM hk

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (k n M : ℕ), 1 ≤ M → k ≤ (l - 1) * n → ((l : ℕ) : Ainf l) ^ (n + M - 1) ∈ Ideal.span {AI.π₁ ^ k, AI.ξ ^ M} :=
  fun l _ P AI k n M hM hk => l_pow_mem l P AI k n M hM hk

end GlobalTheory.CompanionTheory.InertiaEigenvalues.LPow

end

section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

private theorem xi_eq_sum_choose_mul_pi_pow_lemma_2 {l : ℕ} [Fact l.Prime] {P : _root_.Formalism.BasicNotions.LocPrime l}
    (AI : _root_.Formalism.BasicNotions.LocAinf l P) :
    AI.ξ = ∑ i ∈ Finset.range l, ((l.choose (i + 1) : ℕ) : _root_.Formalism.BasicNotions.Loc.Ainf l) * AI.π₁ ^ i := by
  have h := congrArg (Polynomial.eval AI.π₁)
    (Polynomial.geom_sum_X_comp_X_add_one_eq_sum (R := _root_.Formalism.BasicNotions.Loc.Ainf l) l)
  simp only [Polynomial.eval_comp, Polynomial.eval_finset_sum, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul,
    Polynomial.eval_natCast] at h
  rw [← h]
  unfold _root_.Formalism.BasicNotions.LocAinf.ξ _root_.Formalism.BasicNotions.LocAinf.π₁
  simp

private theorem xi_eq_pi_pow_add_prime_mul_lemma {l : ℕ} [hl : Fact l.Prime] {P : _root_.Formalism.BasicNotions.LocPrime l}
    (AI : _root_.Formalism.BasicNotions.LocAinf l P) :
    ∃ w, AI.ξ = AI.π₁ ^ (l - 1) + (l : _root_.Formalism.BasicNotions.Loc.Ainf l) * (1 + AI.π₁ * w) := by
  have hp := hl.out
  obtain ⟨m, hm⟩ : ∃ m, l = m + 2 := ⟨l - 2, by have := hp.two_le; omega⟩
  refine ⟨∑ i ∈ Finset.range m, ((l.choose (i + 2) / l : ℕ) : _root_.Formalism.BasicNotions.Loc.Ainf l) * AI.π₁ ^ i, ?_⟩
  rw [xi_eq_sum_choose_mul_pi_pow_lemma_2, show Finset.range l = Finset.range (m + 1 + 1) by rw [hm],
    Finset.sum_range_succ, Finset.sum_range_succ',
    show l.choose (m + 1 + 1) = 1 by rw [show m + 1 + 1 = l by omega]; simp]
  have hd : ∀ i ∈ Finset.range m, ((l.choose (i + 1 + 1) : ℕ) : _root_.Formalism.BasicNotions.Loc.Ainf l) * AI.π₁ ^ (i + 1) =
      (l : _root_.Formalism.BasicNotions.Loc.Ainf l) * (AI.π₁ * (((l.choose (i + 2) / l : ℕ) : _root_.Formalism.BasicNotions.Loc.Ainf l) * AI.π₁ ^ i)) := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    have hdvd : l ∣ l.choose (i + 2) := hp.dvd_choose_self (by omega) (by omega)
    rw [show ((l.choose (i + 1 + 1) : ℕ) : _root_.Formalism.BasicNotions.Loc.Ainf l) =
        ((l * (l.choose (i + 2) / l) : ℕ) : _root_.Formalism.BasicNotions.Loc.Ainf l) by rw [Nat.mul_div_cancel' hdvd]]
    push_cast
    ring
  rw [Finset.sum_congr rfl hd, ← Finset.mul_sum, ← Finset.mul_sum]
  simp only [zero_add, Nat.choose_one_right, pow_zero, mul_one, Nat.cast_one, one_mul]
  rw [show m + 1 = l - 1 by omega]
  ring

theorem _root_.GlobalTheory.Adopt.ainf_invPi_mod_xi_pow_bounded_denominator : ∀ (l : ℕ) [Fact l.Prime] (P : _root_.Formalism.BasicNotions.LocPrime l)
    (AI : _root_.Formalism.BasicNotions.LocAinf l P) (k n M : ℕ), 1 ≤ M → k ≤ (l - 1) * n →
    ((l : ℕ) : _root_.Formalism.BasicNotions.Loc.Ainf l) ^ (n + M - 1) ∈ Ideal.span {AI.π₁ ^ k, AI.ξ ^ M} := by
  intro l _ P AI k n M hM hk
  obtain ⟨w, hw⟩ := xi_eq_pi_pow_add_prime_mul_lemma AI
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  set q := Ideal.Quotient.mk (Ideal.span {AI.π₁ ^ k, AI.ξ ^ M})
  have hπ : q AI.π₁ ^ k = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (by simp)
  have hξ : q AI.ξ ^ M = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (by simp)
  have hu : IsUnit (q (1 + AI.π₁ * w)) := by
    rw [map_add, map_one, map_mul]
    exact IsNilpotent.isUnit_one_add ⟨k, by rw [mul_pow, hπ, zero_mul]⟩
  have hneg : (-(q AI.π₁ ^ (l - 1))) ^ n = 0 := by
    rw [neg_pow, ← pow_mul, pow_eq_zero_of_le hk hπ, mul_zero]
  have hsum := (Commute.all (q AI.ξ) (-(q AI.π₁ ^ (l - 1)))).add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero
    hξ hneg (k := n + M - 1) (by omega)
  rw [← sub_eq_add_neg, congrArg q hw, map_add, map_pow, add_sub_cancel_left, map_mul,
    mul_pow] at hsum
  rw [map_pow, map_natCast]
  exact ((hu.pow _).mul_left_eq_zero).1 hsum

end
