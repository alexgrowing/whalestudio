import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.IdemLift

theorem sub_pow_three_eq {R : Type*} [CommRing R] {a b : R}
    (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) : (a - b) ^ 3 = a - b := by
  have ha' : a * a = a := ha
  have hb' : b * b = b := hb
  linear_combination (a + 1 - 3 * b) * ha' + (3 * a - b - 1) * hb'

theorem eq_of_isNilpotent_sub {R : Type*} [CommRing R] {a b : R}
    (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) (h : IsNilpotent (a - b)) : a = b := by
  obtain ⟨n, hn⟩ := h
  have h3 := sub_pow_three_eq ha hb
  have hpow : ∀ m : ℕ, (a - b) ^ (2 * m + 1) = a - b := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc (a - b) ^ (2 * (m + 1) + 1) = (a - b) ^ (2 * m + 1) * (a - b) ^ 2 := by ring
        _ = (a - b) ^ 3 := by rw [ih]; ring
        _ = a - b := h3
  have h0 : a - b = 0 := by
    rw [← hpow n, show 2 * n + 1 = n + (n + 1) by ring, pow_add, hn, zero_mul]
  exact sub_eq_zero.1 h0

theorem eq_of_sub_mem_jacobson {R : Type*} [CommRing R] {a b : R}
    (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (h : a - b ∈ Ideal.jacobson (⊥ : Ideal R)) : a = b := by
  have hu : IsUnit ((a - b) * (-(a - b)) + 1) := Ideal.mem_jacobson_bot.1 h _
  have h3 := sub_pow_three_eq ha hb
  have hz : (a - b) * ((a - b) * (-(a - b)) + 1) = 0 := by
    linear_combination -h3
  exact sub_eq_zero.1 ((hu.mul_left_eq_zero).1 hz)

theorem existsUnique_idempotent_lift {S : Type} [CommRing S] (ϖ : S)
    [IsAdicComplete (Ideal.span {ϖ}) S] (k : ℕ) (hk : k ≠ 0)
    (e : S ⧸ Ideal.span {ϖ ^ k}) (he : IsIdempotentElem e) :
    ∃! e' : S, IsIdempotentElem e' ∧ Ideal.Quotient.mk (Ideal.span {ϖ ^ k}) e' = e := by
  have hJI : Ideal.span {ϖ ^ k} ≤ Ideal.span {ϖ} := by
    rw [Ideal.span_singleton_le_span_singleton]
    exact dvd_pow_self ϖ hk
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective e
  have haJ : a * a - a ∈ Ideal.span {ϖ ^ k} := by
    apply Ideal.Quotient.eq_zero_iff_mem.1
    have he' : Ideal.Quotient.mk (Ideal.span {ϖ ^ k}) a * Ideal.Quotient.mk _ a
        = Ideal.Quotient.mk _ a := he
    rw [map_sub, map_mul, he', sub_self]
  have haI : a * a - a ∈ Ideal.span {ϖ} := hJI haJ
  have hH : HenselianRing S (Ideal.span {ϖ}) := IsAdicComplete.henselianRing S _
  have hmon : ((Polynomial.X : Polynomial S) ^ 2 - Polynomial.X).Monic := by
    apply Polynomial.monic_X_pow_sub
    simpa using lt_of_le_of_lt Polynomial.degree_X_le (by norm_num : (1 : WithBot ℕ) < 2)
  have heval : ((Polynomial.X : Polynomial S) ^ 2 - Polynomial.X).eval a ∈ Ideal.span {ϖ} := by
    have : ((Polynomial.X : Polynomial S) ^ 2 - Polynomial.X).eval a = a * a - a := by
      simp [sq]
    rwa [this]
  have hunit : IsUnit (Ideal.Quotient.mk (Ideal.span {ϖ})
      (Polynomial.derivative ((Polynomial.X : Polynomial S) ^ 2 - Polynomial.X) |>.eval a)) := by
    have hd : (Polynomial.derivative ((Polynomial.X : Polynomial S) ^ 2 - Polynomial.X)).eval a
        = 2 * a - 1 := by
      simp
      ring
    rw [hd]
    have hsq : Ideal.Quotient.mk (Ideal.span {ϖ}) (2 * a - 1)
        * Ideal.Quotient.mk (Ideal.span {ϖ}) (2 * a - 1) = 1 := by
      rw [← map_mul, ← map_one (Ideal.Quotient.mk (Ideal.span {ϖ}))]
      apply Ideal.Quotient.eq.2
      have : (2 * a - 1) * (2 * a - 1) - 1 = 4 * (a * a - a) := by ring
      rw [this]
      exact Ideal.mul_mem_left _ _ haI
    exact IsUnit.of_mul_eq_one _ hsq
  obtain ⟨y, hy, hya⟩ := hH.is_henselian _ hmon a heval hunit
  have hyid : IsIdempotentElem y := by
    have : y ^ 2 - y = 0 := by simpa [Polynomial.IsRoot] using hy
    have h2 : y * y - y = 0 := by rw [← sq]; exact this
    exact sub_eq_zero.1 h2
  have hlift : Ideal.Quotient.mk (Ideal.span {ϖ ^ k}) y = Ideal.Quotient.mk _ a := by
    apply eq_of_isNilpotent_sub (hyid.map (Ideal.Quotient.mk _)) he
    refine ⟨k, ?_⟩
    rw [← map_sub, ← map_pow]
    apply Ideal.Quotient.eq_zero_iff_mem.2
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 hya
    rw [hc, mul_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  refine ⟨y, ⟨hyid, hlift⟩, ?_⟩
  rintro z ⟨hz, hza⟩
  apply eq_of_sub_mem_jacobson hz hyid
  apply IsAdicComplete.le_jacobson_bot (Ideal.span {ϖ})
  apply hJI
  apply Ideal.Quotient.eq.1
  rw [hza, hlift]

end GlobalTheory.CompanionTheory.IdemLift
