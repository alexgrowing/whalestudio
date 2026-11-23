import Mathlib

namespace GlobalTheory.ExistsPrimeMem

theorem exists_prime_mem {A : Type} [inst : CommRing A] (P : Ideal A) (hP : Ideal.IsPrime P) :
    ∀ (n : ℕ), n ≠ (0 : ℕ) → (↑n : A) ∈ P → ∃ (ℓ : ℕ), Nat.Prime ℓ ∧ (↑ℓ : A) ∈ P := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hnP
    by_cases h1 : n = 1
    · subst h1
      exact absurd ((Ideal.eq_top_iff_one P).2 (by simpa using hnP)) hP.ne_top
    · have hp := Nat.minFac_prime h1
      have hpos : 0 < n := Nat.pos_of_ne_zero hn
      have hsplit : ((n : ℕ) : A) = (n.minFac : A) * ((n / n.minFac : ℕ) : A) := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' (Nat.minFac_dvd n)]
      rw [hsplit] at hnP
      rcases hP.mem_or_mem hnP with h | h
      · exact ⟨n.minFac, hp, h⟩
      · exact ih (n / n.minFac) (Nat.div_lt_self hpos hp.one_lt)
          (Nat.div_pos (Nat.minFac_le hpos) (Nat.minFac_pos n)).ne' h

end GlobalTheory.ExistsPrimeMem
