import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
open GlobalTheory.LatJet
open scoped Classical

namespace GlobalTheory.LatJet.ProdZero

theorem b_mul_prod_eq_zero {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ}
    (J : JetRing R I n) (l : List I) :
    ∀ ν : Idx I n, n + 1 < (∑ i, (ν : I → ℕ) i) + l.length →
      J.b ν * (l.map J.t).prod = 0 := by
  induction l with
  | nil =>
    intro ν h
    exact absurd ν.2 (by simpa using h)
  | cons a l ih =>
    intro ν h
    rw [List.map_cons, List.prod_cons, ← mul_assoc]
    have hm := J.mul ν ⟨Pi.single a 1, by
      rw [Finset.sum_pi_single']; simp⟩
    have ht : J.t a = J.b ⟨Pi.single a 1, by rw [Finset.sum_pi_single']; simp⟩ := rfl
    rw [ht, hm]
    by_cases hle : ∑ i, ((ν : I → ℕ) + (Pi.single a 1 : I → ℕ)) i ≤ n + 1
    · rw [dif_pos hle, smul_mul_assoc, ih _ ?_, smul_zero]
      have hs : ∑ i, ((ν : I → ℕ) + (Pi.single a 1 : I → ℕ)) i = (∑ i, (ν : I → ℕ) i) + 1 := by
        simp only [Pi.add_apply]
        rw [Finset.sum_add_distrib, Finset.sum_pi_single']
        simp
      show n + 1 < (∑ i, ((ν : I → ℕ) + (Pi.single a 1 : I → ℕ)) i) + l.length
      rw [hs]
      simp only [List.length_cons] at h
      omega
    · rw [dif_neg hle, zero_mul]

theorem prod_eq_zero {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ}
    (J : JetRing R I n) (l : List I) (h : n + 1 < l.length) :
    (l.map J.t).prod = 0 := by
  have := b_mul_prod_eq_zero J l ⟨0, by simp⟩ (by simpa using h)
  rwa [J.one, one_mul] at this

end GlobalTheory.LatJet.ProdZero
