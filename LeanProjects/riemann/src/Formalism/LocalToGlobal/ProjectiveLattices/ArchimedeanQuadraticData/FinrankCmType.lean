import Mathlib

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.FundamentalDomainD5

open NumberField Matrix
open scoped ComplexConjugate

lemma conj_conj_emb {K : Type} [Field K] (φ : K →+* ℂ) :
    ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ :=
  star_star φ

def cmEquiv {K : Type} [Field K] {ι : Type} (σ : ι → K →+* ℂ) (hinj : Function.Injective σ)
    (hcm : ∀ τ : K →+* ℂ, (∃ i, σ i = τ) ↔ ¬ ∃ i, σ i = ComplexEmbedding.conjugate τ) :
    ι ⊕ ι ≃ (K →+* ℂ) :=
  Equiv.ofBijective (Sum.elim σ fun i => ComplexEmbedding.conjugate (σ i)) (by
    constructor
    · rintro (i | i) (j | j) h
      · exact congrArg Sum.inl (hinj h)
      · exfalso
        have h1 : ∃ i', σ i' = σ i := ⟨i, rfl⟩
        exact (hcm (σ i)).1 h1 ⟨j, by
          have := congrArg ComplexEmbedding.conjugate h
          simp only [Sum.elim_inl, Sum.elim_inr] at this
          rw [this, conj_conj_emb]⟩
      · exfalso
        have h1 : ∃ i', σ i' = σ j := ⟨j, rfl⟩
        exact (hcm (σ j)).1 h1 ⟨i, by
          have := congrArg ComplexEmbedding.conjugate h
          simp only [Sum.elim_inl, Sum.elim_inr] at this
          rw [← this, conj_conj_emb]⟩
      · have := congrArg ComplexEmbedding.conjugate h
        simp only [Sum.elim_inr, conj_conj_emb] at this
        exact congrArg Sum.inr (hinj this)
    · intro τ
      by_cases h : ∃ i, σ i = τ
      · obtain ⟨i, hi⟩ := h
        exact ⟨Sum.inl i, hi⟩
      · have h2 : ∃ i, σ i = ComplexEmbedding.conjugate τ := by
          by_contra h3
          exact h ((hcm τ).2 h3)
        obtain ⟨i, hi⟩ := h2
        refine ⟨Sum.inr i, ?_⟩
        simp only [Sum.elim_inr, hi, conj_conj_emb])

theorem sum_re_cmType {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] (σ : ι → K →+* ℂ)
    (hinj : Function.Injective σ)
    (hcm : ∀ τ : K →+* ℂ, (∃ i, σ i = τ) ↔ ¬ ∃ i, σ i = ComplexEmbedding.conjugate τ) (z : K) :
    ∑ i, (σ i z).re = (1 / 2 : ℝ) * ((Algebra.trace ℚ K z : ℚ) : ℝ) := by
  have h1 : (algebraMap ℚ ℂ) (Algebra.trace ℚ K z) = ∑ τ : K →+* ℂ, τ z := by
    rw [trace_eq_sum_embeddings ℂ (x := z)]
    exact Fintype.sum_equiv (RingHom.equivRatAlgHom (R := K) (S := ℂ)).symm _ _ (fun _ => rfl)
  have h2 : ∑ τ : K →+* ℂ, τ z = ∑ i, σ i z + ∑ i, conj (σ i z) := by
    rw [← Equiv.sum_comp (cmEquiv σ hinj hcm), Fintype.sum_sum_type]
    rfl
  have h3 := congrArg Complex.re (h1.trans h2)
  simp only [Complex.add_re, Complex.re_sum, Complex.conj_re] at h3
  have h4 : ((algebraMap ℚ ℂ) (Algebra.trace ℚ K z)).re = ((Algebra.trace ℚ K z : ℚ) : ℝ) := by
    simp
  rw [h4] at h3
  linarith

theorem finrank_cmType {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] (σ : ι → K →+* ℂ)
    (hinj : Function.Injective σ)
    (hcm : ∀ τ : K →+* ℂ, (∃ i, σ i = τ) ↔ ¬ ∃ i, σ i = ComplexEmbedding.conjugate τ) :
    Module.finrank ℚ K = 2 * Fintype.card ι := by
  rw [← NumberField.Embeddings.card K ℂ, ← Fintype.card_congr (cmEquiv σ hinj hcm), Fintype.card_sum]
  ring

end Formalism.L2.Pj.FundamentalDomainD5
