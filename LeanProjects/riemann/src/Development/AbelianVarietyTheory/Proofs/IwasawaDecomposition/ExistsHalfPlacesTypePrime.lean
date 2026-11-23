import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodChi
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTupleConditionOfIdempotentZero

noncomputable section

namespace GlobalTheory.MemN.HalfPlaces

open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory.Mem.GaloisStage
open scoped Pointwise

theorem exists_transversal_cover {S : Type} [Fintype S] (c : S → S) (hc : ∀ x, c (c x) = x)
    (hne : ∀ x, c x ≠ x) {n : ℕ} (hn : Fintype.card S = 2 * n) :
    ∃ e : Fin n → S, Function.Injective e ∧ (∀ i j, c (e i) ≠ e j) ∧ ∀ x, ∃ i, x = e i ∨ x = c (e i) := by
  classical
  obtain ⟨e, he, he'⟩ := exists_transversal c hc hne hn
  refine ⟨e, he, he', fun x => ?_⟩
  have hinj : Function.Injective (Sum.elim e (fun i => c (e i)) : Fin n ⊕ Fin n → S) := by
    rintro (i | i) (j | j) h
    · exact congrArg _ (he h)
    · exact absurd h.symm (he' j i)
    · exact absurd h (he' i j)
    · have h' : c (e i) = c (e j) := h
      have : e i = e j := by rw [← hc (e i), h', hc]
      exact congrArg _ (he this)
  have hbij := (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, by simp [hn, two_mul]⟩
  obtain ⟨i | i, h⟩ := hbij.2 x
  · exact ⟨i, Or.inl h.symm⟩
  · exact ⟨i, Or.inr h.symm⟩

variable {R : Ranks}

theorem isConjPl_iff (H : Host R) (w w' : PlE H) :
    IsConjPl H w w' ↔ H.conj • w.asIdeal = w'.asIdeal := by
  constructor
  · intro h
    ext y
    have := h (H.conj⁻¹ • y) y (by rw [← Formalism.TwoAdicCyclotomicDecomposition.odd_coe_smul, smul_inv_smul])
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    exact this
  · intro h x y hxy
    have hy : y = H.conj • x := by
      apply Subtype.ext
      exact hxy
    rw [← h, hy, Ideal.smul_mem_pointwise_smul_iff]

theorem exists_places_cover (H : Host R) {p : ℕ} (hp : p.Prime)
    (hs : (placesOver H.E p).ncard = Module.finrank ℚ H.E) :
    ∃ e : Fin R.f → PlE H, (∀ i, e i ∈ placesOver H.E p) ∧ Function.Injective e ∧
      (∀ i j, ¬ IsConjPl H (e i) (e j)) ∧ ∀ w ∈ placesOver H.E p, ∃ v, w = e v ∨ IsConjPl H (e v) w := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hG : IsGalois ℚ H.E := H.galois
  have := Formalism.FrobeniusOrbits.SplitK.span_prime p
  have : IsGaloisGroup (H.E ≃ₐ[ℚ] H.E) ℤ (𝓞 H.E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ H.E
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  obtain ⟨⟨P, hP1, hP2⟩⟩ := (inferInstance : Nonempty (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 H.E)))
  have hr : Set.range (fun σ : H.E ≃ₐ[ℚ] H.E => σ • P) = Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 H.E) := by
    ext Q
    constructor
    · rintro ⟨σ, rfl⟩
      exact ⟨inferInstance, inferInstance⟩
    · rintro ⟨hQ1, hQ2⟩
      exact Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) P Q (H.E ≃ₐ[ℚ] H.E)
  have hinj : Function.Injective (fun σ : H.E ≃ₐ[ℚ] H.E => σ • P) := by
    rw [GlobalTheory.HostSplit.ncard_placesOver H.E hp, ← hr, ← IsGalois.card_aut_eq_finrank, ← Set.image_univ,
      ← Set.ncard_univ] at hs
    exact Set.injOn_univ.1 (Set.injOn_of_ncard_image_eq hs)
  have hcard : Fintype.card (H.E ≃ₐ[ℚ] H.E) = 2 * R.f := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank,
      H.finrank_cmField, Ranks.f, Ranks.n]
    ring
  obtain ⟨e, he, he', hcov⟩ := exists_transversal_cover (fun σ => H.conj * σ)
    (fun σ => by rw [← mul_assoc, conj_mul_conj, one_mul])
    (fun σ h => conj_ne_one H (mul_eq_right.1 h)) hcard
  refine ⟨fun i => ⟨e i • P, inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot hp0 _⟩, fun i => ?_,
    fun i j h => he (hinj (congrArg HeightOneSpectrum.asIdeal h)), fun i j h => he' i j (hinj ?_),
    fun w hw => ?_⟩
  · have h3 : (p : ℤ) ∈ (e i • P).under ℤ := by
      rw [← Ideal.over_def (e i • P) (Ideal.span {(p : ℤ)})]
      exact Ideal.mem_span_singleton_self _
    have h4 : algebraMap ℤ (𝓞 H.E) ((p : ℕ) : ℤ) ∈ e i • P := h3
    rw [map_natCast] at h4
    exact h4
  · show (H.conj * e i) • P = e j • P
    rw [mul_smul]
    have h' := (isConjPl_iff H _ _).1 h
    dsimp only at h'
    exact h'
  · have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
    have hwp := w.isPrime
    have hw' : w.asIdeal ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 H.E) := by
      refine ⟨hwp, ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩⟩
      rw [Ideal.span_singleton_le_iff_mem]
      show algebraMap ℤ (𝓞 H.E) ((p : ℕ) : ℤ) ∈ w.asIdeal
      rw [map_natCast]
      exact hw
    rw [← hr] at hw'
    obtain ⟨σ, hσ⟩ := hw'
    have hσ' : σ • P = w.asIdeal := hσ
    obtain ⟨i, h | h⟩ := hcov σ
    · exact ⟨i, Or.inl (HeightOneSpectrum.ext (by rw [← hσ', h]))⟩
    · refine ⟨i, Or.inr ?_⟩
      rw [isConjPl_iff]
      dsimp only
      rw [← hσ', h, mul_smul]

end GlobalTheory.MemN.HalfPlaces

end
