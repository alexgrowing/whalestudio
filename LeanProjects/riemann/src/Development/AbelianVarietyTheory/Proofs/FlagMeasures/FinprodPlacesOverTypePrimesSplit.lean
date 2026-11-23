import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

namespace GlobalTheory.TypedPlacesProduct

theorem finite_over {K : Type*} [Field K] [NumberField K] {n : ℕ} (hn : n ≠ 0) :
    {v : HeightOneSpectrum (𝓞 K) | ((n : ℕ) : 𝓞 K) ∈ v.asIdeal}.Finite := by
  have hI : Ideal.span {((n : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.mpr hn
  refine (Ideal.finite_factors hI).subset ?_
  intro v hv
  simp only [Set.mem_setOf_eq] at hv ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem finprod_over {K : Type*} [Field K] [NumberField K] {n f : ℕ} (hn : n ≠ 0) (φ : ℝ → ℝ)
    (hc : Nat.card {v : HeightOneSpectrum (𝓞 K) // ((n : ℕ) : 𝓞 K) ∈ v.asIdeal} = f)
    (hq : ∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal →
      Nat.card (𝓞 K ⧸ v.asIdeal) = n) :
    (∏ᶠ p ∈ {p : HeightOneSpectrum (𝓞 K) | ((n : ℕ) : 𝓞 K) ∈ p.asIdeal},
      φ (Ideal.absNorm p.asIdeal : ℝ)) = φ n ^ f := by
  have hs := finite_over (K := K) hn
  have hnorm : ∀ p ∈ {p : HeightOneSpectrum (𝓞 K) | ((n : ℕ) : 𝓞 K) ∈ p.asIdeal},
      φ (Ideal.absNorm p.asIdeal : ℝ) = φ n := by
    intro p hp
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, hq p hp]
  rw [finprod_mem_congr rfl hnorm, finprod_mem_eq_finite_toFinset_prod _ hs, Finset.prod_const,
    ← Nat.card_eq_card_finite_toFinset hs]
  exact congrArg _ hc

private lemma disjoint_primes_dvd_of_coprime {K : Type*} [Field K] [NumberField K] {a b : ℕ} (hab : Nat.Coprime a b) :
    Disjoint {p : HeightOneSpectrum (𝓞 K) | ((a : ℕ) : 𝓞 K) ∈ p.asIdeal}
      {p : HeightOneSpectrum (𝓞 K) | ((b : ℕ) : 𝓞 K) ∈ p.asIdeal} := by
  rw [Set.disjoint_left]
  intro p ha hb
  obtain ⟨u, w, huw⟩ := (Nat.isCoprime_iff_coprime.mpr hab).map (Int.castRingHom (𝓞 K))
  have h1 : (1 : 𝓞 K) ∈ p.asIdeal := by
    rw [← huw]
    simp only [eq_intCast, Int.cast_natCast]
    exact p.asIdeal.add_mem (p.asIdeal.mul_mem_left _ ha) (p.asIdeal.mul_mem_left _ hb)
  exact p.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

theorem finprod_typed_places : ∀ (D : D7) (φ : ℝ → ℝ), (∀ i, StandardLattice.SplitsF D (D.host.g i)) → (∏ᶠ p ∈ {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g 0 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal ∨ ((D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal}, φ (Ideal.absNorm p.asIdeal : ℝ)) = φ (D.host.g 0) ^ D.R.f * φ (D.host.g 1) ^ D.R.f := by
  intro D φ hs
  have hp := D.host.g_prime
  have hne : D.host.g 0 ≠ D.host.g 1 := D.host.g_ne
  have hcop : Nat.Coprime (D.host.g 0) (D.host.g 1) := (Nat.coprime_primes (hp 0) (hp 1)).mpr hne
  rw [Set.setOf_or, finprod_mem_union (disjoint_primes_dvd_of_coprime hcop) (finite_over (hp 0).ne_zero)
    (finite_over (hp 1).ne_zero), finprod_over (hp 0).ne_zero φ (hs 0).1 (hs 0).2,
    finprod_over (hp 1).ne_zero φ (hs 1).1 (hs 1).2]

end GlobalTheory.TypedPlacesProduct
