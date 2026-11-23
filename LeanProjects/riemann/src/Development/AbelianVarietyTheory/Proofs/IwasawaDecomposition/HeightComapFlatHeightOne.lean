import Mathlib
open IsLocalRing

namespace GlobalTheory

theorem height_comap_eq_one_of_flat :
    ∀ {A R : Type} [CommRing A] [IsDomain A] [CommRing R] (φ : A →+* R), φ.Flat →
      ∀ (Q : Ideal R) [Q.IsPrime], Q.height = 1 → Q.comap φ ≠ ⊥ → (Q.comap φ).height = 1 := by
  intro A R _ _ _ φ hφ Q _ hQ hne
  letI := φ.toAlgebra
  haveI : Module.Flat A R := hφ
  haveI : Algebra.HasGoingDown A R := Algebra.HasGoingDown.of_flat
  set p : Ideal A := Q.comap φ with hp
  haveI : p.IsPrime := Ideal.comap_isPrime φ Q
  haveI : Q.LiesOver p := ⟨rfl⟩
  apply le_antisymm
  · rw [show ((1 : ℕ∞)) = ((1 : ℕ) : ℕ∞) from rfl, Ideal.height_le_iff]
    intro q hq hqp
    by_contra hcon
    have hq0 : q ≠ ⊥ := by
      rintro rfl
      simp at hcon
    haveI := hq
    obtain ⟨P₁, hP₁Q, hP₁, hP₁o⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (p := q) (q := p) Q hqp
    haveI := hP₁
    haveI : (⊥ : Ideal A).IsPrime := Ideal.bot_prime
    obtain ⟨P₀, hP₀P₁, hP₀, -⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (p := ⊥) (q := q) P₁
      (bot_lt_iff_ne_bot.mpr hq0)
    haveI := hP₀
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hP₀P₁
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hP₁Q
    rw [hQ] at h2
    have h4 : (1 : ℕ∞) ≤ P₁.height := le_trans le_add_self h1
    have h3 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (by gcongr) h2
    exact absurd h3 (by decide)
  · haveI : (⊥ : Ideal A).IsPrime := Ideal.bot_prime
    have := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hne)
    simpa using this

end GlobalTheory
