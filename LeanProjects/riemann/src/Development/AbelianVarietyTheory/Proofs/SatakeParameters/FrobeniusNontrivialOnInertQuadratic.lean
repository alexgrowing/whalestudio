import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.BasicNotions

namespace GlobalTheory

theorem frobenius_moves_quadratic_subfield_of_inert :
    ∀ (E : Type) [Field E] [NumberField E] (M : Subfield E) (p : ℕ) (Q : HeightOneSpectrum (𝓞 E)) (φ : E ≃ₐ[ℚ] E), p.Prime → Module.finrank ℚ M = 2 → (Ideal.span {((p : ℕ) : 𝓞 M)}).IsPrime → ((p : ℕ) : 𝓞 E) ∈ Q.asIdeal → (∀ x : 𝓞 E, φ • x - x ^ p ∈ Q.asIdeal) → ∃ x ∈ M, φ x ≠ x := by
  intro E _ _ M p Q φ hp hM hP hQ hφ
  by_contra h
  push_neg at h
  haveI : FiniteDimensional ℚ M := Module.finite_of_finrank_pos (by omega)
  haveI : NumberField M := {}
  let f : 𝓞 M →+* 𝓞 E := RingOfIntegers.mapRingHom M.subtype
  have hp0 : ((p : ℕ) : 𝓞 M) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hcard : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 M)}) = p ^ 2 := by
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, hM]
  set P : Ideal (𝓞 M) := Ideal.span {((p : ℕ) : 𝓞 M)} with hPdef
  have hne : P ≠ ⊥ := by
    rw [hPdef, Ne, Ideal.span_singleton_eq_bot]; exact hp0
  have hmax : P.IsMaximal := hP.isMaximal hne
  have hcom : P = Q.asIdeal.comap f := by
    refine hmax.eq_of_le (Ideal.comap_ne_top f Q.isPrime.ne_top) ?_
    rw [hPdef, Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
    exact hQ
  have key : ∀ x : 𝓞 M ⧸ P, x ^ p = x := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← map_pow, eq_comm, Ideal.Quotient.eq, hcom, Ideal.mem_comap, map_sub, map_pow]
    have h1 : φ • f y = f y := by
      apply Subtype.ext
      exact h _ (y : M).2
    have h2 := hφ (f y)
    rwa [h1] at h2
  haveI : Finite (𝓞 M ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hne
  letI : Fintype (𝓞 M ⧸ P) := Fintype.ofFinite _
  haveI : IsDomain (𝓞 M ⧸ P) := Ideal.Quotient.isDomain P
  have hc : Fintype.card (𝓞 M ⧸ P) = p ^ 2 := by
    rw [← hcard, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  classical
  have h1 : 1 < p := hp.one_lt
  have hdeg : (Polynomial.X ^ p - Polynomial.X : Polynomial (𝓞 M ⧸ P)).natDegree = p := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> simp [h1]
  have hnz : (Polynomial.X ^ p - Polynomial.X : Polynomial (𝓞 M ⧸ P)) ≠ 0 := by
    intro h0
    rw [h0] at hdeg
    simp at hdeg
    omega
  have hle : (Finset.univ : Finset (𝓞 M ⧸ P)).card ≤ p := by
    refine le_trans ?_ hdeg.le
    apply Polynomial.card_le_degree_of_subset_roots
    intro x _
    rw [Polynomial.mem_roots hnz]
    simp [key x]
  rw [Finset.card_univ, hc] at hle
  nlinarith

end GlobalTheory
