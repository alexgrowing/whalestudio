import Mathlib

namespace GlobalTheory.PrimeNatCastMembership

theorem exists_prime_natCast_mem {A : Type} [inst : CommRing A] (P : Ideal A) (hP : Ideal.IsPrime P)
    (n : ℕ) (hn : n ≠ (0 : ℕ)) (hmem : (↑n : A) ∈ P) :
    ∃ (q : ℕ), Nat.Prime q ∧ (↑q : A) ∈ P := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h1 : n = 1
    · subst h1
      exact absurd ((Ideal.eq_top_iff_one P).2 (by simpa using hmem)) hP.ne_top
    · obtain ⟨q, hq, m, hm⟩ := Nat.exists_prime_and_dvd h1
      have hm0 : m ≠ 0 := by
        rintro rfl
        exact hn (by simpa using hm)
      have hlt : m < n := by
        have h2 := hq.two_le
        have h3 := Nat.pos_of_ne_zero hm0
        rw [hm]
        nlinarith
      have hprod : (q : A) * (m : A) ∈ P := by
        rw [← Nat.cast_mul, ← hm]
        exact hmem
      rcases hP.mem_or_mem hprod with h | h
      · exact ⟨q, hq, h⟩
      · exact ih m hlt hm0 h

end GlobalTheory.PrimeNatCastMembership
