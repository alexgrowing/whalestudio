import Mathlib
import Formalism.PeriodIntegrals.ClassNumImQ
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticDedekindZeta.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticDedekindZeta.SpanNatCastSupEqTop

open NumberField

namespace PI.ClassNumImQ.ZetaNonvanishing₂

variable {K : Type} [Field K] [NumberField K]

theorem absNorm_span_two (h2 : Module.finrank ℚ K = 2) (p : ℕ) :
    Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ 2 := by
  rw [Ideal.absNorm_span_singleton]
  have hn : Algebra.norm ℤ ((p : 𝓞 K)) = (p : ℤ) ^ 2 := by
    rw [show ((p : 𝓞 K)) = algebraMap ℤ (𝓞 K) (p : ℤ) by simp, Algebra.norm_algebraMap,
      NumberField.RingOfIntegers.rank, h2]
  rw [hn, Int.natAbs_pow, Int.natAbs_natCast]

theorem dvd_span_pow_of_absNorm {p k : ℕ} {I : Ideal (𝓞 K)} (hI : Ideal.absNorm I = p ^ k) :
    I ∣ Ideal.span {(p : 𝓞 K)} ^ k := by
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem]
  have hm := Ideal.absNorm_mem I
  rw [hI] at hm
  simpa using hm

theorem isPrime_of_absNorm_prime {p : ℕ} (hp : p.Prime) {P : Ideal (𝓞 K)}
    (hP : Ideal.absNorm P = p) : P.IsPrime :=
  Ideal.isPrime_of_irreducible_absNorm (by rw [hP]; exact (Nat.prime_iff.mp hp).irreducible)

theorem ne_bot_of_absNorm {P : Ideal (𝓞 K)} {n : ℕ} (hP : Ideal.absNorm P = n) (hn : n ≠ 0) :
    P ≠ ⊥ := by
  rintro rfl
  rw [Ideal.absNorm_bot] at hP
  exact hn hP.symm

theorem eq_pow_of_dvd_pow {P : Ideal (𝓞 K)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) {I : Ideal (𝓞 K)}
    {n : ℕ} (h : I ∣ P ^ n) : ∃ i ≤ n, I = P ^ i := by
  obtain ⟨i, hi, h'⟩ := (dvd_prime_pow (Ideal.prime_of_isPrime hP0 hP) n).1 h
  exact ⟨i, hi, associated_iff_eq.1 h'⟩

theorem cnt_eq_one_of {n : ℕ} (X : Ideal (𝓞 K)) (hX : Ideal.absNorm X = n)
    (h : ∀ I : Ideal (𝓞 K), Ideal.absNorm I = n → I = X) : cnt K n = 1 := by
  unfold cnt
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun a b => Subtype.ext ((h a.1 a.2).trans (h b.1 b.2).symm)⟩, ⟨⟨X, hX⟩⟩⟩

theorem cnt_eq_zero_of {n : ℕ} (h : ∀ I : Ideal (𝓞 K), Ideal.absNorm I ≠ n) : cnt K n = 0 := by
  unfold cnt
  haveI : IsEmpty { I : Ideal (𝓞 K) // Ideal.absNorm I = n } := ⟨fun x => h x.1 x.2⟩
  exact Nat.card_of_isEmpty

end PI.ClassNumImQ.ZetaNonvanishing₂
