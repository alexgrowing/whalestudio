import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DTermOrigin

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum

namespace GlobalTheory.DualFormValues

variable {E : Type} [Field E] [NumberField E]

theorem trace_eq_sum (x : E) : ((Algebra.trace ℚ E x : ℚ) : ℂ) = ∑ σ : E →+* ℂ, σ x := by
  have h := trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := x)
  rw [eq_ratCast] at h
  rw [h]
  exact (Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) (fun σ : E →+* ℂ => σ x) _ (fun σ => rfl)).symm

theorem coeff_eq_zero (c : (E →+* ℂ) → (E →+* ℂ) → ℂ)
    (h : ∀ x y : E, ∑ τ₁, ∑ τ₂, c τ₁ τ₂ * (τ₁ x * τ₂ y) = 0) (τ₁ τ₂ : E →+* ℂ) : c τ₁ τ₂ = 0 := by
  have hli : LinearIndependent ℂ (fun (τ : E →+* ℂ) => (fun x => τ x : E → ℂ)) := by
    have h0 := linearIndependent_monoidHom E ℂ
    have hinj : Function.Injective (fun τ : E →+* ℂ => (τ : E →* ℂ)) := by
      intro a b hab
      ext x
      exact DFunLike.congr_fun hab x
    exact h0.comp _ hinj
  rw [Fintype.linearIndependent_iff] at hli
  have h1 : ∀ y : E, ∀ a : E →+* ℂ, ∑ b, c a b * b y = 0 := by
    intro y
    refine hli (fun a => ∑ b, c a b * b y) ?_
    funext x
    have := h x y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Finset.sum_mul]
    rw [← this]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  exact hli (c τ₁) (by
    funext y
    simpa [mul_comm] using h1 y τ₁) τ₂

variable [IsCMField E]

theorem riemannCl_eq_sum (ξ x : E) :
    riemannCl ξ x = ∑ σ : E →+* ℂ, σ (ξ * x) • (ComplexEmbedding.conjugate σ).toRatAlgHom.toLinearMap := by
  ext y
  simp only [riemannCl, riemann, LinearMap.coe_mk, AddHom.coe_mk, trace_eq_sum, LinearMap.sum_apply,
    LinearMap.smul_apply, map_mul, smul_eq_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp [IsCMField.complexEmbedding_complexConj, ComplexEmbedding.conjugate_coe_eq]

theorem dualForm_values (E : Type) [Field E] [NumberField E] [IsCMField E] (ξ : E) (hξ : ξ ≠ 0)
    (_hc : IsCMField.complexConj E ξ = -ξ) (B : LinearMap.BilinForm ℂ (Coh E)) (hB : IsDualForm ξ B)
    (ρ ρ' : E →+* ℂ) :
    (ρ' = ComplexEmbedding.conjugate ρ →
      B ρ.toRatAlgHom.toLinearMap ρ'.toRatAlgHom.toLinearMap = (ρ ξ)⁻¹) ∧
    (ρ' ≠ ComplexEmbedding.conjugate ρ → B ρ.toRatAlgHom.toLinearMap ρ'.toRatAlgHom.toLinearMap = 0) := by
  classical
  let b : (E →+* ℂ) → (E →+* ℂ) → ℂ := fun a a' => B a.toRatAlgHom.toLinearMap a'.toRatAlgHom.toLinearMap
  let c : (E →+* ℂ) → (E →+* ℂ) → ℂ := fun τ₁ τ₂ =>
    τ₁ ξ * τ₂ ξ * b (ComplexEmbedding.conjugate τ₁) (ComplexEmbedding.conjugate τ₂) -
      if τ₂ = ComplexEmbedding.conjugate τ₁ then τ₁ ξ else 0
  have hz : ∀ τ : E →+* ℂ, τ ξ ≠ 0 := fun τ => by simpa using hξ
  have hsum : ∀ x y : E, ∑ τ₁, ∑ τ₂, c τ₁ τ₂ * (τ₁ x * τ₂ y) = 0 := by
    intro x y
    have h1 := hB x y
    rw [riemannCl_eq_sum, riemannCl_eq_sum] at h1
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at h1
    have h2 : ((riemann ξ x y : ℚ) : ℂ) = ∑ σ : E →+* ℂ, σ ξ * σ x * ComplexEmbedding.conjugate σ y := by
      simp only [riemann, trace_eq_sum, map_mul]
      refine Finset.sum_congr rfl fun σ _ => ?_
      simp [IsCMField.complexEmbedding_complexConj, ComplexEmbedding.conjugate_coe_eq]
    rw [h2] at h1
    simp only [c, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    rw [sub_eq_zero]
    have h3 : ∑ τ₁, ∑ τ₂, τ₁ ξ * τ₂ ξ * b (ComplexEmbedding.conjugate τ₁) (ComplexEmbedding.conjugate τ₂) *
        (τ₁ x * τ₂ y) = ∑ σ : E →+* ℂ, σ ξ * σ x * ComplexEmbedding.conjugate σ y := by
      rw [← h1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun τ₂ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ₁ _ => ?_
      simp only [b, map_mul]
      ring
    rw [h3]
    refine Finset.sum_congr rfl fun σ _ => ?_
    ring
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := by
    intro τ
    ext x
    simp [ComplexEmbedding.conjugate_coe_eq]
  have hc := coeff_eq_zero c hsum (ComplexEmbedding.conjugate ρ) (ComplexEmbedding.conjugate ρ')
  simp only [c, b, hcc] at hc
  constructor
  · rintro rfl
    rw [hcc, if_pos rfl] at hc
    have h0 := hz (ComplexEmbedding.conjugate ρ)
    have h4 : ComplexEmbedding.conjugate ρ ξ *
        (ρ ξ * B ρ.toRatAlgHom.toLinearMap (ComplexEmbedding.conjugate ρ).toRatAlgHom.toLinearMap - 1) = 0 := by
      linear_combination hc
    have h5 := (mul_eq_zero.1 h4).resolve_left h0
    exact eq_inv_of_mul_eq_one_right (sub_eq_zero.1 h5)
  · intro hne
    have hne' : ComplexEmbedding.conjugate ρ' ≠ ρ := fun h => hne (by rw [← h, hcc])
    rw [if_neg hne', sub_zero] at hc
    exact (mul_eq_zero.1 hc).resolve_left (mul_ne_zero (hz _) (hz _))

end GlobalTheory.DualFormValues
