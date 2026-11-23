import Mathlib

open NumberField

namespace GlobalTheory

theorem eq_of_le_of_multiset_prod_eq_pow_card {g : ℕ} (hg : 0 < g) (s : Multiset ℕ)
    (hle : ∀ a ∈ s, g ≤ a) (hprod : s.prod = g ^ s.card) : ∀ a ∈ s, a = g := by
  intro a ha
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem ha
  have ht : g ^ t.card ≤ t.prod :=
    Multiset.pow_card_le_prod (fun b hb => hle b (Multiset.mem_cons_of_mem hb))
  rw [Multiset.prod_cons, Multiset.card_cons, pow_succ'] at hprod
  have hpos : 0 < g ^ t.card := pow_pos hg _
  have h1 : a * g ^ t.card ≤ g * g ^ t.card := hprod ▸ Nat.mul_le_mul_left a ht
  exact le_antisymm (Nat.le_of_mul_le_mul_right h1 hpos) (hle a (Multiset.mem_cons_self _ _))

theorem pow_sub_self_mem_span_of_splits_completely (E : Type) [Field E] [NumberField E] (g : ℕ)
    (hg : g.Prime)
    (hcard : (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).card =
      Module.finrank ℚ E)
    (hnd : (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).Nodup)
    (x : 𝓞 E) : x ^ g - x ∈ Ideal.span {(g : 𝓞 E)} := by
  classical
  set I : Ideal (𝓞 E) := Ideal.span {(g : 𝓞 E)} with hI
  set s := UniqueFactorizationMonoid.normalizedFactors I with hs
  have hI0 : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hg.ne_zero
  have hprod : s.prod = I := Ideal.prod_normalizedFactors_eq_self hI0
  have hprime : ∀ P ∈ s, Prime P := fun P hP =>
    UniqueFactorizationMonoid.prime_of_normalized_factor P hP
  have hN : Ideal.absNorm I = g ^ Module.finrank ℚ E := by
    rw [hI, Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  have hle : ∀ a ∈ s.map Ideal.absNorm, g ≤ a := by
    intro a ha
    obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp ha
    have hdvd : Ideal.absNorm P ∣ g ^ Module.finrank ℚ E := by
      rw [← hN, ← hprod]
      exact map_dvd _ (Multiset.dvd_prod hP)
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hg).mp hdvd
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, Ideal.absNorm_eq_one_iff] at hk
      exact (hprime P hP).ne_one (by rw [hk, Ideal.one_eq_top])
    rw [hk]
    exact Nat.le_self_pow hk0 g
  have hall : ∀ a ∈ s.map Ideal.absNorm, a = g := by
    refine eq_of_le_of_multiset_prod_eq_pow_card hg.pos _ hle ?_
    rw [← map_multiset_prod, hprod, hN, Multiset.card_map, hcard]
  have hmem : ∀ P ∈ s, x ^ g - x ∈ P := by
    intro P hP
    have hNP : Ideal.absNorm P = g := hall _ (Multiset.mem_map_of_mem _ hP)
    have hPp : P.IsPrime := Ideal.isPrime_of_prime (hprime P hP)
    have hPm : P.IsMaximal := hPp.isMaximal (hprime P hP).ne_zero
    have hc : Nat.card (𝓞 E ⧸ P) = g := by
      rw [← hNP, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    have hfin : Finite (𝓞 E ⧸ P) := Nat.finite_of_card_ne_zero (hc ▸ hg.ne_zero)
    let := Fintype.ofFinite (𝓞 E ⧸ P)
    let := Ideal.Quotient.field P
    rw [← Ideal.Quotient.eq, map_pow, ← hc, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card _
  have hdvd : (∏ P ∈ (⟨s, hnd⟩ : Finset (Ideal (𝓞 E))), P) ∣ Ideal.span {x ^ g - x} :=
    Finset.prod_primes_dvd _ hprime fun P hP =>
      Ideal.dvd_span_singleton.mpr (hmem P hP)
  have he : (∏ P ∈ (⟨s, hnd⟩ : Finset (Ideal (𝓞 E))), P) = I := by
    rw [← hprod, Finset.prod_mk, Multiset.map_id']
  rw [he] at hdvd
  exact Ideal.dvd_span_singleton.mp hdvd

end GlobalTheory
