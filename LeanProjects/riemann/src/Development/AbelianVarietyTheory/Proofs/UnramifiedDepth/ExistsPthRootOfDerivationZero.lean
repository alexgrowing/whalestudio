import Mathlib

open scoped BigOperators
open Polynomial IntermediateField

namespace GlobalTheory

theorem minpoly_eq_X_pow_sub_C_of_pow_mem {K : Type} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (M : Subfield K) (hM : ∀ y : K, y ^ p ∈ M) (x : K) (hx : x ∉ M) :
    minpoly M x = X ^ p - C (⟨x ^ p, hM x⟩ : M) := by
  have hp : p.Prime := Fact.out
  symm
  apply minpoly.eq_of_irreducible_of_monic
  · apply X_pow_sub_C_irreducible_of_prime hp
    intro b hb
    apply hx
    have h1 : (b : K) ^ p = x ^ p := by
      have := congrArg (fun z : M => (z : K)) hb
      simpa using this
    have h2 : (b : K) = x := frobenius_inj K p (by simpa [frobenius_def] using h1)
    rw [← h2]; exact b.2
  · simp only [map_sub, map_pow, aeval_X, aeval_C]
    exact sub_self _
  · exact monic_X_pow_sub_C _ hp.ne_zero

theorem isIntegral_of_pow_mem_subfield {K : Type} [Field K] (p : ℕ) [Fact p.Prime]
    (M : Subfield K) (hM : ∀ y : K, y ^ p ∈ M) (x : K) : IsIntegral M x := by
  have hp : p.Prime := Fact.out
  refine ⟨X ^ p - C (⟨x ^ p, hM x⟩ : M), monic_X_pow_sub_C _ hp.ne_zero, ?_⟩
  rw [← aeval_def]
  simp only [map_sub, map_pow, aeval_X, aeval_C]
  exact sub_self _

theorem exists_pow_eq_of_forall_derivation_eq_zero (K : Type) [Field K] (p : ℕ) [Fact p.Prime]
    [CharP K p] (f : K) (hf : ∀ D : Derivation ℤ K K, D f = 0) : ∃ h : K, h ^ p = f := by
  have hp : p.Prime := Fact.out
  by_contra hne
  let S : Set (Subfield K) := {M | (∀ y : K, y ^ p ∈ M) ∧ f ∉ M}
  have h0 : (frobenius K p).fieldRange ∈ S := by
    refine ⟨fun y => ⟨y, rfl⟩, ?_⟩
    rintro ⟨y, hy⟩
    exact hne ⟨y, hy⟩
  obtain ⟨M, -, hM⟩ := zorn_le_nonempty₀ S (fun c hcS hc y hy => by
    refine ⟨sSup c, ⟨fun z => (le_sSup hy : y ≤ sSup c) ((hcS hy).1 z), ?_⟩,
      fun z hz => le_sSup hz⟩
    rw [Subfield.mem_sSup_of_directedOn ⟨y, hy⟩ hc.directedOn]
    rintro ⟨z, hz, hfz⟩
    exact (hcS hz).2 hfz) _ h0
  obtain ⟨hMp, hMf⟩ := hM.prop
  have hrank : ∀ x : K, x ∉ M → Module.finrank M M⟮x⟯ = p := by
    intro x hx
    rw [adjoin.finrank (isIntegral_of_pow_mem_subfield p M hMp x),
      minpoly_eq_X_pow_sub_C_of_pow_mem p M hMp x hx, natDegree_X_pow_sub_C]
  have htop : ∀ x : K, x ∈ M⟮f⟯ := by
    intro x
    by_cases hx : x ∈ M
    · exact (M⟮f⟯).algebraMap_mem ⟨x, hx⟩
    have hle : M ≤ (M⟮x⟯).toSubfield := fun z hz => (M⟮x⟯).algebraMap_mem ⟨z, hz⟩
    have hfx : f ∈ M⟮x⟯ := by
      by_contra hcon
      have h1 : (M⟮x⟯).toSubfield ∈ S := ⟨fun y => hle (hMp y), hcon⟩
      exact hx (hM.le_of_ge h1 hle (mem_adjoin_simple_self M x))
    haveI := adjoin.finiteDimensional (isIntegral_of_pow_mem_subfield p M hMp x)
    have heq : M⟮f⟯ = M⟮x⟯ :=
      eq_of_le_of_finrank_eq (adjoin_simple_le_iff.mpr hfx) (by rw [hrank f hMf, hrank x hx])
    rw [heq]; exact mem_adjoin_simple_self M x
  have hsurj : Function.Surjective (aeval f : M[X] →ₐ[M] K) := by
    intro x
    have h1 : x ∈ (M⟮f⟯).toSubalgebra := htop x
    rw [adjoin_simple_toSubalgebra_of_isAlgebraic
      (isIntegral_of_pow_mem_subfield p M hMp f).isAlgebraic,
      Algebra.adjoin_singleton_eq_range_aeval] at h1
    exact h1
  have hd : ∀ q : M[X], aeval f q = 0 → aeval f ((derivative' : Derivation M M[X] M[X]) q) = 0 := by
    intro q hq
    obtain ⟨r, rfl⟩ := minpoly.dvd M f hq
    have h1 : aeval f (derivative (minpoly M f)) = 0 := by
      rw [minpoly_eq_X_pow_sub_C_of_pow_mem p M hMp f hMf]
      simp [derivative_X_pow]
    simp [derivative'_apply, derivative_mul, h1]
  have h2 := hf ((Derivation.liftOfSurjective hsurj hd).restrictScalars ℤ)
  have h3 := Derivation.liftOfSurjective_apply hsurj hd X
  rw [Derivation.restrictScalars_apply] at h2
  simp only [aeval_X, derivative'_apply, derivative_X, map_one] at h3
  exact one_ne_zero (h3.symm.trans h2)

end GlobalTheory
