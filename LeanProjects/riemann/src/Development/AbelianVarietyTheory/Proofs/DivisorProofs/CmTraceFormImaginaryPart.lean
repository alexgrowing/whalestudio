import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
open NumberField GlobalTheory.CMVal GlobalTheory.LatJet GlobalTheory.RealMult
open GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex (latMod polMod dualLat TrInt bar)

namespace GlobalTheory.CMTrace

theorem sum_embeddings_cmType {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I]
    (φ : I → E →+* ℂ) (hφ : IsCMType φ) (g : (E →+* ℂ) → ℂ) :
    ∑ σ : E →+* ℂ, g σ = ∑ i, (g (φ i) + g (ComplexEmbedding.conjugate (φ i))) := by
  have hnr : ∀ i, ComplexEmbedding.conjugate (φ i) ≠ φ i := fun i h =>
    InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk (φ i)))
      (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 h))
  let f : I ⊕ I → (E →+* ℂ) := Sum.elim φ (fun i => ComplexEmbedding.conjugate (φ i))
  have hf : Function.Bijective f := by
    constructor
    · rintro (i | i) (j | j) h
      · simp only [f, Sum.elim_inl] at h
        obtain ⟨k, _, hk⟩ := hφ (φ i)
        rw [hk i (Or.inl rfl), hk j (Or.inl h)]
      · simp only [f, Sum.elim_inl, Sum.elim_inr] at h
        obtain ⟨k, _, hk⟩ := hφ (φ i)
        have hi := hk i (Or.inl rfl)
        have hj := hk j (Or.inr h)
        subst hi; subst hj
        exact absurd h.symm (hnr _)
      · simp only [f, Sum.elim_inl, Sum.elim_inr] at h
        obtain ⟨k, _, hk⟩ := hφ (φ j)
        have hi := hk i (Or.inr h.symm)
        have hj := hk j (Or.inl rfl)
        subst hi; subst hj
        exact absurd h (hnr _)
      · simp only [f, Sum.elim_inr] at h
        have h' : φ i = φ j := by
          have := congrArg ComplexEmbedding.conjugate h
          simpa using this
        obtain ⟨k, _, hk⟩ := hφ (φ i)
        rw [hk i (Or.inl rfl), hk j (Or.inl h')]
    · intro σ
      obtain ⟨i, hi, _⟩ := hφ σ
      rcases hi with h | h
      · exact ⟨Sum.inl i, h.symm⟩
      · exact ⟨Sum.inr i, h.symm⟩
  rw [← Fintype.sum_bijective f hf (g ∘ f) g (fun _ => rfl), Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  rfl

theorem trace_eq_sum_re {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I]
    (φ : I → E →+* ℂ) (hφ : IsCMType φ) (w : E) :
    ((Algebra.trace ℚ E w : ℚ) : ℝ) = ∑ i, 2 * (φ i w).re := by
  have h1 : ((Algebra.trace ℚ E w : ℚ) : ℂ) = ∑ σ : E →ₐ[ℚ] ℂ, σ w := by
    rw [← trace_eq_sum_embeddings (K := ℚ) (L := E) (E := ℂ)]
    simp
  have h2 : ∑ σ : E →ₐ[ℚ] ℂ, σ w = ∑ σ : E →+* ℂ, σ w :=
    (Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun _ => rfl))
  have h3 := sum_embeddings_cmType φ hφ (fun σ => σ w)
  apply Complex.ofReal_injective
  rw [Complex.ofReal_ratCast, h1, h2, h3]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ComplexEmbedding.conjugate_coe_eq, Complex.add_conj]
  push_cast; ring

end GlobalTheory.CMTrace

open GlobalTheory.CMTrace in
theorem GlobalTheory.trace_riemannForm_eq_im : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (n : ℕ) (e : Fin n ≃ I) (t₁ : E) (ρ : ℝ), (∀ i, φ i t₁ = -Complex.I * ((ρ / 2 : ℝ) : ℂ)) →
    ∀ (a : FR E) (x y : E), ((Algebra.trace ℚ E ((a : E) * t₁ * x * bar y) : ℚ) : ℝ) =
      (∑ j, (φ (e j) (a : E) * (ρ : ℂ)) * φ (e j) x * starRingEnd ℂ (φ (e j) y)).im := by
  intro E _ _ _ I _ φ hφ n e t₁ ρ ht a x y
  rw [trace_eq_sum_re φ hφ, Complex.im_sum, Equiv.sum_comp e (fun i => ((φ i (a : E) * (ρ : ℂ)) * φ i x * starRingEnd ℂ (φ i y)).im)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have ha : starRingEnd ℂ (φ i (a : E)) = φ i (a : E) := by
    rw [← IsCMField.complexEmbedding_complexConj]
    congr 1
    exact (IsCMField.complexConj E).commutes a
  have hre : φ i (a : E) = ((φ i (a : E)).re : ℂ) := (Complex.conj_eq_iff_re.1 ha).symm
  have hb : φ i (bar y) = starRingEnd ℂ (φ i y) := IsCMField.complexEmbedding_complexConj E (φ i) y
  rw [map_mul, map_mul, map_mul, hb, ht i, hre]
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  ring
