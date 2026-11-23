import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
open NumberField ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory

theorem sum_re_cmType_eq_half_trace (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : Data E r) (ν₀ : E) :
    ∑ τ : X.Ψ, (τ.1 ν₀).re = ((Algebra.trace ℚ E ν₀ : ℚ) : ℝ) / 2 := by
  classical
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ :=
    fun τ => ComplexEmbedding.involutive_conjugate E τ
  have h1 : ((Algebra.trace ℚ E ν₀ : ℚ) : ℝ) = ∑ τ : E →+* ℂ, (τ ν₀).re := by
    have h := trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := ν₀)
    rw [← (RingHom.equivRatAlgHom (R := E) (S := ℂ)).sum_comp] at h
    have h' := congrArg Complex.re h
    rw [Complex.re_sum] at h'
    simpa using h'
  have h2 : ∑ τ : {τ : E →+* ℂ // τ ∉ X.Ψ}, (τ.1 ν₀).re = ∑ τ : X.Ψ, (τ.1 ν₀).re := by
    let e : {τ : E →+* ℂ // τ ∉ X.Ψ} ≃ X.Ψ :=
      { toFun := fun τ => ⟨ComplexEmbedding.conjugate τ.1, by
          rw [X.cmType, hcc]; exact τ.2⟩
        invFun := fun τ => ⟨ComplexEmbedding.conjugate τ.1, (X.cmType _).1 τ.2⟩
        left_inv := fun τ => Subtype.ext (hcc _)
        right_inv := fun τ => Subtype.ext (hcc _) }
    refine Fintype.sum_equiv e _ _ fun τ => ?_
    change _ = (ComplexEmbedding.conjugate τ.1 ν₀).re
    rw [ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]
  have h3 := Fintype.sum_subtype_add_sum_subtype (fun τ : E →+* ℂ => τ ∈ X.Ψ)
    (fun τ => (τ ν₀).re)
  have h4 : ∑ τ : X.Ψ, (τ.1 ν₀).re + ∑ τ : {τ : E →+* ℂ // τ ∉ X.Ψ}, (τ.1 ν₀).re
      = ∑ τ : E →+* ℂ, (τ ν₀).re := by
    convert h3
  rw [h1, ← h4, h2]
  ring

end GlobalTheory
