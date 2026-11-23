import Mathlib
import GroundTheory.GlobalFields.AnalyticClassNumber.QuadraticLegendre
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open NumberField GroundTheory.Global.Quadratic

variable {K : Type} [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]

theorem absNorm_span_natCast_quadratic (n : ℕ) :
    Ideal.absNorm (Ideal.span {(n : 𝓞 K)}) = n ^ 2 := by
  rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, Algebra.IsQuadraticExtension.finrank_eq_two]

theorem ramified_eq_span_sqrtDiscr {d : ℕ} (hd : d.Prime) (hdisc : discr K = -(d : ℤ))
    (𝔭 : Ideal (𝓞 K)) [h𝔭 : 𝔭.IsPrime] (hN : (Ideal.absNorm 𝔭).Prime)
    (h2 : 𝔭 ^ 2 = Ideal.span {((Ideal.absNorm 𝔭 : ℕ) : 𝓞 K)}) :
    𝔭 = Ideal.span {sqrtDiscr K} := by
  set p := Ideal.absNorm 𝔭 with hp
  have h𝔭top : 𝔭 ≠ ⊤ := h𝔭.ne_top
  have hconj : ∀ x ∈ 𝔭, conjRing K x ∈ 𝔭 := by
    intro x hx
    have hx2 : x ^ 2 ∈ Ideal.span {(p : 𝓞 K)} := by
      rw [← h2]
      exact Ideal.pow_mem_pow hx 2
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hx2
    have hp𝔭 : (p : 𝓞 K) ∈ 𝔭 := by
      have : (p : 𝓞 K) ∈ 𝔭 ^ 2 := by
        rw [h2]
        exact Ideal.mem_span_singleton_self _
      exact Ideal.pow_le_self two_ne_zero this
    have hsq : (conjRing K x) ^ 2 ∈ 𝔭 := by
      have e : (conjRing K x) ^ 2 = conjRing K y * (p : 𝓞 K) := by
        rw [← map_pow, ← hy, map_mul, map_natCast]
      rw [e]
      exact Ideal.mul_mem_left _ _ hp𝔭
    exact h𝔭.mem_of_pow_mem 2 hsq
  have hres : ∀ x : 𝓞 K, ∃ n : ℤ, x - n ∈ 𝔭 := by
    intro x
    have hcard : Nat.card (𝓞 K ⧸ 𝔭) = p := by
      rw [hp, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    have : Fact (Nat.card (𝓞 K ⧸ 𝔭)).Prime := ⟨hcard ▸ hN⟩
    have h1 : (1 : 𝓞 K ⧸ 𝔭) ≠ 0 := by
      rw [ne_eq, ← map_one (Ideal.Quotient.mk 𝔭), Ideal.Quotient.eq_zero_iff_mem]
      exact fun h ↦ h𝔭top ((Ideal.eq_top_iff_one _).2 h)
    have htop : AddSubgroup.zmultiples (1 : 𝓞 K ⧸ 𝔭) = ⊤ := by
      rcases AddSubgroup.eq_bot_or_eq_top_of_prime_card
          (AddSubgroup.zmultiples (1 : 𝓞 K ⧸ 𝔭)) with h | h
      · exfalso
        apply h1
        have : (1 : 𝓞 K ⧸ 𝔭) ∈ AddSubgroup.zmultiples (1 : 𝓞 K ⧸ 𝔭) :=
          AddSubgroup.mem_zmultiples 1
        rw [h] at this
        exact (AddSubgroup.mem_bot).1 this
      · exact h
    have hx : Ideal.Quotient.mk 𝔭 x ∈ AddSubgroup.zmultiples (1 : 𝓞 K ⧸ 𝔭) := by
      rw [htop]
      trivial
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 hx
    refine ⟨n, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hn, map_intCast, zsmul_one, sub_self]
  have hsub : ∀ x : 𝓞 K, conjRing K x - x ∈ 𝔭 := by
    intro x
    obtain ⟨n, hn⟩ := hres x
    have hc := hconj _ hn
    rw [map_sub, map_intCast] at hc
    have := 𝔭.sub_mem hc hn
    rwa [sub_sub_sub_cancel_right] at this
  have hδ : sqrtDiscr K ∈ 𝔭 := by
    have e : sqrtDiscr K = intBasis K 0 * (conjRing K (intBasis K 1) - intBasis K 1) -
        intBasis K 1 * (conjRing K (intBasis K 0) - intBasis K 0) := by
      rw [sqrtDiscr]
      ring
    rw [e]
    exact 𝔭.sub_mem (𝔭.mul_mem_left _ (hsub _)) (𝔭.mul_mem_left _ (hsub _))
  have hnormsq : Ideal.absNorm (Ideal.span {sqrtDiscr K}) ^ 2 = d ^ 2 := by
    rw [← map_pow, Ideal.span_singleton_pow, sqrtDiscr_sq', hdisc, Int.cast_neg, Int.cast_natCast,
      Ideal.span_singleton_neg, absNorm_span_natCast_quadratic]
  have hnorm : Ideal.absNorm (Ideal.span {sqrtDiscr K}) = d :=
    Nat.pow_left_injective two_ne_zero hnormsq
  have hmax : (Ideal.span {sqrtDiscr K}).IsMaximal :=
    (Ideal.isPrime_of_irreducible_absNorm (hnorm ▸ hd)).isMaximal
      (by rw [ne_eq, Ideal.span_singleton_eq_bot]; exact sqrtDiscr_ne_zero K)
  exact (hmax.eq_of_le h𝔭top ((Ideal.span_singleton_le_iff_mem _).2 hδ)).symm

theorem prime_cases {d : ℕ} (hd : d.Prime) (hdisc : discr K = -(d : ℤ))
    (𝔭 : Ideal (𝓞 K)) [h𝔭 : 𝔭.IsPrime] (h0 : 𝔭 ≠ ⊥) :
    (∃ a : 𝓞 K, 𝔭 = Ideal.span {a}) ∨
      ∃ p : ℕ, p.Prime ∧ Ideal.absNorm 𝔭 = p ∧ ∃ 𝔮 : Ideal (𝓞 K), 𝔮.IsPrime ∧
        Ideal.absNorm 𝔮 = p ∧ 𝔭 * 𝔮 = Ideal.span {(p : 𝓞 K)} ∧ 𝔮 ≠ 𝔭 := by
  have : 𝔭.IsMaximal := h𝔭.isMaximal h0
  obtain ⟨p, k, hk, hpmem, hpp, hNk⟩ := Ideal.exists_prime_and_absNorm_eq_pow 𝔭
  have hle : Ideal.span {(p : 𝓞 K)} ≤ 𝔭 := (Ideal.span_singleton_le_iff_mem _).2 hpmem
  have hdvdN : p ^ k ∣ p ^ 2 := by
    rw [← hNk, ← absNorm_span_natCast_quadratic (K := K)]
    exact Ideal.absNorm_dvd_absNorm_of_le hle
  have hk2 : k ≤ 2 := (Nat.pow_dvd_pow_iff_le_right hpp.one_lt).1 hdvdN
  obtain ⟨𝔮, h𝔮⟩ : 𝔭 ∣ Ideal.span {(p : 𝓞 K)} := Ideal.dvd_iff_le.2 hle
  have hN𝔮 : Ideal.absNorm 𝔭 * Ideal.absNorm 𝔮 = p ^ 2 := by
    rw [← map_mul, ← h𝔮, absNorm_span_natCast_quadratic]
  have hp0 : 0 < p := hpp.pos
  interval_cases k
  · rw [hNk, pow_one, sq] at hN𝔮
    have hq : Ideal.absNorm 𝔮 = p := Nat.eq_of_mul_eq_mul_left hp0 hN𝔮
    have h𝔮p : 𝔮.IsPrime := Ideal.isPrime_of_irreducible_absNorm (hq ▸ hpp)
    by_cases he : 𝔮 = 𝔭
    · left
      refine ⟨sqrtDiscr K, ramified_eq_span_sqrtDiscr hd hdisc 𝔭 (by rw [hNk, pow_one]; exact hpp) ?_⟩
      rw [hNk, pow_one, sq, h𝔮, he]
    · right
      exact ⟨p, hpp, by rw [hNk, pow_one], 𝔮, h𝔮p, hq, h𝔮.symm, he⟩
  · rw [hNk] at hN𝔮
    have hq : Ideal.absNorm 𝔮 = 1 := by
      have h' : p ^ 2 * Ideal.absNorm 𝔮 = p ^ 2 * 1 := by rw [mul_one]; exact hN𝔮
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hp0 2) h'
    rw [Ideal.absNorm_eq_one_iff] at hq
    left
    exact ⟨p, by rw [h𝔮, hq, Ideal.mul_top]⟩

end GroundTheory.Heights₂.Heights.ChowlaSelberg
