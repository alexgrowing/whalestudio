import Mathlib

namespace GlobalTheory.PrimeDvdNatCastMem

theorem exists_prime_dvd_natCast_mem {O : Type} [CommRing O] (P : Ideal O) [hP : Ideal.IsPrime P]
    (m : ℕ) : m ≠ (0 : ℕ) → (↑m : O) ∈ P → ∃ (p : ℕ), Nat.Prime p ∧ p ∣ m ∧ (↑p : O) ∈ P := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm0 hm
    by_cases h1 : m = 1
    · subst h1
      exact absurd ((Ideal.eq_top_iff_one P).2 (by simpa using hm)) hP.ne_top
    · obtain ⟨q, hq, k, hk⟩ := Nat.exists_prime_and_dvd h1
      have hk0 : k ≠ 0 := by
        rintro rfl
        exact hm0 (by simpa using hk)
      have hmul : (q : O) * (k : O) ∈ P := by
        have := hm
        rw [hk, Nat.cast_mul] at this
        exact this
      rcases hP.mem_or_mem hmul with h | h
      · exact ⟨q, hq, ⟨k, hk⟩, h⟩
      · have hlt : k < m := by
          have h2 := hq.two_le
          have h3 : 0 < k := Nat.pos_of_ne_zero hk0
          rw [hk]
          nlinarith
        obtain ⟨p, hp, hpk, hpP⟩ := ih k hlt hk0 h
        exact ⟨p, hp, hk ▸ Dvd.dvd.mul_left hpk q, hpP⟩

end GlobalTheory.PrimeDvdNatCastMem
