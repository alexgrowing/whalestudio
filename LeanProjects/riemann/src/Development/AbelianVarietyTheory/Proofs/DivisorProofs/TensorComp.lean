import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial

set_option autoImplicit false

noncomputable section

open TopologicalSpace TensorProduct

namespace GlobalTheory.AnPer

theorem Step.tensor_comp {I I₀ : Type} [Fintype I] [Fintype I₀] {g : ℕ} {D C : Type} [CommRing D] [Algebra ℂ D]
    [CommRing C] [Algebra ℂ C] {W : Opens (Tot I g)} {W₀ : Opens (Tot I₀ g)} (Ta : Hol W →ₐ[ℂ] D ⊗[ℂ] Hol W₀)
    (hT : ∀ a h, Ta (dw a h) = LinearMap.lTensor D (dw a).toLinearMap (Ta h)) (J : Ideal C) (J' : Ideal (D ⊗[ℂ] C))
    (hJ : ∀ c ∈ J, (1 : D) ⊗ₜ[ℂ] c ∈ J') (ρ₁ ρ₂ : Hol W₀ →ₐ[ℂ] C)
    (s : Step J (ρ₁ : Hol W₀ →+* C) (ρ₂ : Hol W₀ →+* C)) :
    Step J' ((Algebra.TensorProduct.map (AlgHom.id ℂ D) ρ₁).comp Ta).toRingHom
      ((Algebra.TensorProduct.map (AlgHom.id ℂ D) ρ₂).comp Ta).toRingHom := by
  obtain ⟨n, h1, h2, h3⟩ := s
  refine ⟨fun a ↦ (1 : D) ⊗ₜ[ℂ] n a, fun a ↦ hJ _ (h1 a), fun a b ↦ by simp [h2], fun f ↦ ?_⟩
  have key : ∀ x : D ⊗[ℂ] Hol W₀, Algebra.TensorProduct.map (AlgHom.id ℂ D) ρ₂ x =
      Algebra.TensorProduct.map (AlgHom.id ℂ D) ρ₁ x +
        ∑ a, Algebra.TensorProduct.map (AlgHom.id ℂ D) ρ₁ (LinearMap.lTensor D (dw a).toLinearMap x) *
          (1 : D) ⊗ₜ[ℂ] n a := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul d h =>
      have := h3 h
      simp only [RingHom.coe_coe] at this
      simp [this, tmul_add, tmul_sum]
    | add x y hx hy =>
      simp only [map_add, hx, hy, add_mul, Finset.sum_add_distrib]
      abel
  simpa [hT] using key (Ta f)

theorem Close.tensor_comp {I I₀ : Type} [Fintype I] [Fintype I₀] {g : ℕ} {D C : Type} [CommRing D] [Algebra ℂ D]
    [CommRing C] [Algebra ℂ C] {W : Opens (Tot I g)} {W₀ : Opens (Tot I₀ g)} (Ta : Hol W →ₐ[ℂ] D ⊗[ℂ] Hol W₀)
    (hT : ∀ a h, Ta (dw a h) = LinearMap.lTensor D (dw a).toLinearMap (Ta h)) (J : Ideal C) (J' : Ideal (D ⊗[ℂ] C))
    (hJ : ∀ c ∈ J, (1 : D) ⊗ₜ[ℂ] c ∈ J') (ρ₁ ρ₂ : Hol W₀ →ₐ[ℂ] C)
    (h : Close J (ρ₁ : Hol W₀ →+* C) (ρ₂ : Hol W₀ →+* C)) :
    Close J' ((Algebra.TensorProduct.map (AlgHom.id ℂ D) ρ₁).comp Ta).toRingHom
      ((Algebra.TensorProduct.map (AlgHom.id ℂ D) ρ₂).comp Ta).toRingHom := by
  have key : ∀ ρ : Hol W₀ →+* C, Close J (ρ₁ : Hol W₀ →+* C) ρ → ∃ σ : Hol W₀ →ₐ[ℂ] C, (σ : Hol W₀ →+* C) = ρ ∧
      Close J' ((Algebra.TensorProduct.map (AlgHom.id ℂ D) ρ₁).comp Ta).toRingHom
        ((Algebra.TensorProduct.map (AlgHom.id ℂ D) σ).comp Ta).toRingHom := by
    intro ρ hρ
    induction hρ with
    | refl => exact ⟨ρ₁, rfl, Relation.ReflTransGen.refl⟩
    | @tail b c _ s ih =>
      obtain ⟨σ, rfl, ih⟩ := ih
      have hc : ∀ z : ℂ, c (algebraMap ℂ (Hol W₀) z) = algebraMap ℂ C z := by
        intro z
        obtain ⟨n, -, -, h3⟩ := s
        rw [h3]
        simp [Derivation.map_algebraMap]
      exact ⟨{ c with commutes' := hc }, rfl,
        Relation.ReflTransGen.tail ih (Step.tensor_comp Ta hT J J' hJ σ { c with commutes' := hc } s)⟩
  obtain ⟨σ, hσ, h'⟩ := key _ h
  obtain rfl : σ = ρ₂ := AlgHom.coe_ringHom_injective hσ
  exact h'

end GlobalTheory.AnPer
