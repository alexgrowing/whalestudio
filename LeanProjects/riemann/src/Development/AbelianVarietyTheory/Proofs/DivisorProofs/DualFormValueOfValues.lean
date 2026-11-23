import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DTermOrigin

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum

namespace GlobalTheory.DualFormOrtho

theorem bilin_eq_zero_of_span {V : Type} [AddCommGroup V] [Module ℂ V] (B : LinearMap.BilinForm ℂ V) {s t : Set V}
    (h : ∀ u ∈ s, ∀ v ∈ t, B u v = 0) {a b : V} (ha : a ∈ Submodule.span ℂ s) (hb : b ∈ Submodule.span ℂ t) : B a b = 0 := by
  induction ha using Submodule.span_induction with
  | mem u hu =>
    induction hb using Submodule.span_induction with
    | mem v hv => exact h u hu v hv
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul c x _ hx => simp [hx]
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

theorem dualFormValue_of_values : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I]
    (φ : I → E →+* ℂ), IsCMType φ → (∀ ξ : E, ξ ≠ 0 → ∃! B : LinearMap.BilinForm ℂ (Coh E), IsDualForm ξ B) →
    (∀ ξ : E, ξ ≠ 0 → IsCMField.complexConj E ξ = -ξ → ∀ B : LinearMap.BilinForm ℂ (Coh E), IsDualForm ξ B →
      ∀ ρ ρ' : E →+* ℂ, (ρ' = ComplexEmbedding.conjugate ρ → B ρ.toRatAlgHom.toLinearMap ρ'.toRatAlgHom.toLinearMap = (ρ ξ)⁻¹) ∧
        (ρ' ≠ ComplexEmbedding.conjugate ρ → B ρ.toRatAlgHom.toLinearMap ρ'.toRatAlgHom.toLinearMap = 0)) →
    DualFormValue φ := by
  intro E _ _ _ I _ _ φ hφ hex hval ξ hξ hc
  refine ⟨hex ξ hξ, fun B hB ε => ?_⟩
  have hv := hval ξ hξ hc B hB
  have key : ∀ i j, i ≠ j → ∀ σ : E →+* ℂ, (σ = φ i ∨ σ = ComplexEmbedding.conjugate (φ i)) →
      (σ = φ j ∨ σ = ComplexEmbedding.conjugate (φ j)) → False :=
    fun i j hij σ h1 h2 => hij ((hφ σ).unique h1 h2)
  have gen : ∀ i j, i ≠ j → ∀ u ∈ ({eCl φ i, fCl φ i} : Set (Coh E)), ∀ v ∈ ({eCl φ j, fCl φ j} : Set (Coh E)), B u v = 0 := by
    rintro i j hij u (rfl | rfl) v (rfl | rfl)
    · exact (hv (φ i) (φ j)).2 fun h => key i j hij (φ j) (Or.inr h) (Or.inl rfl)
    · exact (hv (φ i) (ComplexEmbedding.conjugate (φ j))).2 fun h =>
        key i j hij (ComplexEmbedding.conjugate (φ j)) (Or.inr h) (Or.inr rfl)
    · refine (hv (ComplexEmbedding.conjugate (φ i)) (φ j)).2 fun h => ?_
      rw [ComplexEmbedding.involutive_conjugate E (φ i)] at h
      exact key i j hij (φ j) (Or.inl h) (Or.inl rfl)
    · refine (hv (ComplexEmbedding.conjugate (φ i)) (ComplexEmbedding.conjugate (φ j))).2 fun h => ?_
      rw [ComplexEmbedding.involutive_conjugate E (φ i)] at h
      exact key i j hij (ComplexEmbedding.conjugate (φ j)) (Or.inl h) (Or.inr rfl)
  refine ⟨fun i j hij a ha b hb => ?_, fun i => ?_⟩
  · have h0 : B a b = 0 := bilin_eq_zero_of_span B (gen i j hij) ha hb
    rw [pairing, h0, mul_zero]
  · have h1 : B (eCl φ i) (fCl φ i) = (φ i ξ)⁻¹ := (hv (φ i) (ComplexEmbedding.conjugate (φ i))).1 rfl
    rw [pairing, h1, div_eq_mul_inv]
    ring

end GlobalTheory.DualFormOrtho
