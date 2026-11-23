import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectQuotient

theorem exists_frobenius_iterate (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (h : (p : R) = 0) (k : ℕ) : ∃ f : R →+* R, ∀ x, f x = x ^ p ^ k := by
  rcases subsingleton_or_nontrivial R with hs | hn
  · exact ⟨RingHom.id R, fun x => Subsingleton.elim _ _⟩
  · haveI : CharP R p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 h
    exact ⟨iterateFrobenius R p k, fun x => iterateFrobenius_def p k x⟩

theorem solv_pow : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](S : Type) [CommRing S] [Algebra A S] (B : Type) [CommRing B] [Algebra A B] (i : S →ₐ[A] B) (I : Ideal S) (m n : ℕ) (a : Fin m → Fin n → A) (c : Fin m → A), (p : A) = 0 → PQ p (i : S →+* B) I → Solv B a c → ∃ (k : ℕ) (s : Fin n → S), ∀ t, ∑ j, a t j ^ p ^ k • s j - algebraMap A S (c t ^ p ^ k) ∈ I := by
  intro p _ A _ S _ _ B _ _ i I m n a c hp hPQ hS
  obtain ⟨y, hy⟩ := hS
  have hpS : (p : S) = 0 := by
    have := congrArg (algebraMap A S) hp
    simpa using this
  choose k₀ x hx using fun j => hPQ.pow (y j)
  obtain ⟨K, hK⟩ : ∃ K, K = Finset.univ.sup k₀ := ⟨_, rfl⟩
  let s : Fin n → S := fun j => x j ^ p ^ (K - k₀ j)
  have hs : ∀ j, y j ^ p ^ K = i (s j) := by
    intro j
    have hle : k₀ j ≤ K := hK ▸ Finset.le_sup (Finset.mem_univ j)
    have hpow : p ^ K = p ^ k₀ j * p ^ (K - k₀ j) := by
      rw [← pow_add]; congr 1; omega
    have hxj : y j ^ p ^ k₀ j = i (x j) := hx j
    rw [hpow, pow_mul, hxj]
    simp [s, map_pow]
  obtain ⟨fB, hfB⟩ := exists_frobenius_iterate p B hPQ.pf.char K
  have he : ∀ t, i (∑ j, a t j ^ p ^ K • s j - algebraMap A S (c t ^ p ^ K)) = 0 := by
    intro t
    have h1 := congrArg fB (hy t)
    rw [map_sum] at h1
    have h2 : ∀ j, fB (a t j • y j) = a t j ^ p ^ K • i (s j) := by
      intro j
      rw [hfB, smul_pow, hs]
    simp only [h2] at h1
    rw [hfB, ← map_pow] at h1
    rw [map_sub, map_sum, AlgHom.commutes, sub_eq_zero, ← h1]
    exact Finset.sum_congr rfl fun j _ => map_smul i _ _
  choose k₁ hk₁ using fun t => (hPQ.ker _).1 (he t)
  obtain ⟨L, hL⟩ : ∃ L, L = Finset.univ.sup k₁ := ⟨_, rfl⟩
  obtain ⟨fS, hfS⟩ := exists_frobenius_iterate p S hpS L
  refine ⟨K + L, fun j => s j ^ p ^ L, fun t => ?_⟩
  have hle : k₁ t ≤ L := hL ▸ Finset.le_sup (Finset.mem_univ t)
  have hpow : p ^ L = p ^ k₁ t * p ^ (L - k₁ t) := by
    rw [← pow_add]; congr 1; omega
  have hmem : (∑ j, a t j ^ p ^ K • s j - algebraMap A S (c t ^ p ^ K)) ^ p ^ L ∈ I := by
    rw [hpow, pow_mul]
    exact I.pow_mem_of_mem (hk₁ t) _ (pow_pos (Fact.out : p.Prime).pos _)
  rw [← hfS, map_sub, map_sum] at hmem
  have h3 : ∀ j, fS (a t j ^ p ^ K • s j) = a t j ^ p ^ (K + L) • s j ^ p ^ L := by
    intro j
    rw [hfS, smul_pow, ← pow_mul, ← pow_add]
  simp only [h3] at hmem
  rw [hfS, ← map_pow, ← pow_mul, ← pow_add] at hmem
  exact hmem

end GlobalTheory.CompanionTheory.PerfectQuotient
