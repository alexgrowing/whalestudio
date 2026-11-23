import Mathlib

namespace GlobalTheory.SpanPowerSupremum

theorem span_sup_sq_eq {A : Type} [CommRing A] [IsDedekindDomain A] {Q : Ideal A} [Q.IsPrime]
    (hQ : Q ≠ ⊥) {π : A} (h1 : π ∈ Q) (h2 : π ∉ Q ^ 2) :
    Ideal.span {π} ⊔ Q ^ 2 = Q := by
  have hp : Prime Q := Ideal.prime_of_isPrime hQ ‹_›
  have hle : Ideal.span {π} ⊔ Q ^ 2 ≤ Q :=
    sup_le ((Ideal.span_singleton_le_iff_mem Q).mpr h1) (Ideal.pow_le_self two_ne_zero)
  have hdvd : Ideal.span {π} ⊔ Q ^ 2 ∣ Q ^ 2 := Ideal.dvd_iff_le.mpr le_sup_right
  obtain ⟨i, hi, hassoc⟩ := (dvd_prime_pow hp 2).mp hdvd
  have heq : Ideal.span {π} ⊔ Q ^ 2 = Q ^ i := associated_iff_eq.mp hassoc
  interval_cases i
  ·
    rw [pow_zero, Ideal.one_eq_top] at heq
    rw [heq, top_le_iff] at hle
    exact (Ideal.IsPrime.ne_top ‹_› hle).elim
  · rw [pow_one] at heq
    exact heq
  ·
    have hmem : π ∈ Ideal.span {π} ⊔ Q ^ 2 := Ideal.mem_sup_left (Ideal.mem_span_singleton_self π)
    rw [heq] at hmem
    exact (h2 hmem).elim

theorem pow_le_span_pow_sup {A : Type} [CommRing A] [IsDedekindDomain A] {Q : Ideal A}
    [Q.IsPrime] (hQ : Q ≠ ⊥) {π : A} (h1 : π ∈ Q) (h2 : π ∉ Q ^ (2 : ℕ)) (m : ℕ) :
    Q ^ m ≤ Ideal.span {π ^ m} ⊔ Q ^ (m + (1 : ℕ)) := by
  have hπ : Ideal.span {π} ≤ Q := (Ideal.span_singleton_le_iff_mem Q).mpr h1
  induction m with
  | zero => simp
  | succ m ih =>
    have hπm : Ideal.span {π ^ m} ≤ Q ^ m := by
      rw [← Ideal.span_singleton_pow]
      exact Ideal.pow_right_mono hπ m
    calc Q ^ (m + 1) = Q ^ m * Q := pow_succ Q m
      _ ≤ (Ideal.span {π ^ m} ⊔ Q ^ (m + 1)) * (Ideal.span {π} ⊔ Q ^ 2) :=
          Ideal.mul_mono ih (span_sup_sq_eq hQ h1 h2).ge
      _ ≤ Ideal.span {π ^ (m + 1)} ⊔ Q ^ (m + 1 + 1) := by
          rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
          refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
          · rw [Ideal.span_singleton_mul_span_singleton, ← pow_succ]
            exact le_sup_left
          · refine le_sup_of_le_right ?_
            calc Ideal.span {π ^ m} * Q ^ 2 ≤ Q ^ m * Q ^ 2 := Ideal.mul_mono_left hπm
              _ = Q ^ (m + 1 + 1) := by rw [← pow_add]
          · refine le_sup_of_le_right ?_
            calc Q ^ (m + 1) * Ideal.span {π} ≤ Q ^ (m + 1) * Q := Ideal.mul_mono_right hπ
              _ = Q ^ (m + 1 + 1) := (pow_succ Q (m + 1)).symm
          · refine le_sup_of_le_right ?_
            calc Q ^ (m + 1) * Q ^ 2 ≤ Q ^ (m + 1) * Q := Ideal.mul_mono_right (Ideal.pow_le_self two_ne_zero)
              _ = Q ^ (m + 1 + 1) := (pow_succ Q (m + 1)).symm

end GlobalTheory.SpanPowerSupremum
