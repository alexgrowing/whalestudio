import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
open scoped TensorProduct
open Function

namespace GlobalTheory

theorem exists_isLocalRing_quotient_pairwise_isCoprime_iInf_eq_bot_padicInt :
    ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] [Module.Finite ℤ_[ℓ] A],
      ∃ (ι : Type) (_ : Fintype ι) (I : ι → Ideal A),
        (∀ i, IsLocalRing (A ⧸ I i)) ∧ Pairwise (IsCoprime on I) ∧ ⨅ i, I i = ⊥ := by
  intro ℓ _ A _ _ _
  classical
  have : HenselianLocalRing ℤ_[ℓ] := henselianLocalRing_of_henselianRing ℤ_[ℓ]
  have := finite_maximalSpectrum_of_finite_of_isLocalRing ℤ_[ℓ] A
  letI := Fintype.ofFinite (MaximalSpectrum A)
  obtain ⟨e, he, H⟩ := exists_completeOrthogonalIdempotents_of_henselian ℤ_[ℓ] A
  refine ⟨MaximalSpectrum A, inferInstance, fun q ↦ Ideal.span {1 - e q}, fun q ↦ ?_, ?_, ?_⟩
  · have := q.isMaximal
    exact isLocalRing_quotient_one_sub (he.idem q) q.asIdeal (H q)
  · intro i j hij
    change IsCoprime (Ideal.span {1 - e i}) (Ideal.span {1 - e j})
    rw [Ideal.isCoprime_span_singleton_iff]
    have h0 : e i * e j = 0 := he.ortho hij
    exact ⟨1, e i, by linear_combination (-1 : A) * h0⟩
  · refine eq_bot_iff.2 fun x hx ↦ ?_
    rw [Submodule.mem_iInf] at hx
    rw [Ideal.mem_bot, ← one_mul x, ← he.complete, Finset.sum_mul]
    refine Finset.sum_eq_zero fun q _ ↦ ?_
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (hx q)
    rw [← hw]
    linear_combination (-w) * (he.idem q).eq

end GlobalTheory
