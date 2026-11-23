import Mathlib

namespace GlobalTheory.CuspFormEvaluationSupplement

universe u_1

theorem main : ∀ {R : Type u_1} [inst : CommRing R] {P : Ideal R}, Ideal.IsPrime P → ∀ (N : ℕ), N ≠ (0 : ℕ) → (↑N : R) ∈ P → ∃ (p : ℕ), Nat.Prime p ∧ p ∣ N ∧ (↑p : R) ∈ P := by
  intro R _ P hP N
  induction N using induction_on_primes with
  | zero => intro h; exact absurd rfl h
  | one =>
    intro _ h1
    exact absurd ((Ideal.eq_top_iff_one P).mpr (by simpa using h1)) hP.ne_top
  | prime_mul p a hp ih =>
    intro hN hmem
    have ha : a ≠ 0 := by rintro rfl; simp at hN
    push_cast at hmem
    rcases hP.mem_or_mem hmem with h | h
    · exact ⟨p, hp, dvd_mul_right p a, h⟩
    · obtain ⟨q, hq, hqa, hqP⟩ := ih ha h
      exact ⟨q, hq, dvd_mul_of_dvd_right hqa p, hqP⟩

end GlobalTheory.CuspFormEvaluationSupplement
