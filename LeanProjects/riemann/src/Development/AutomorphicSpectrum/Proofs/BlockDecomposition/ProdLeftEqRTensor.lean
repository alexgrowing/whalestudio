import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulSmulMemRange

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.SnakeCov

theorem prodLeft_eq_rTensor {A B₁ B₂ K : Type} [CommRing A] [AddCommGroup B₁] [Module A B₁]
    [AddCommGroup B₂] [Module A B₂] [AddCommGroup K] [Module A K] (w : (B₁ × B₂) ⊗[A] K) :
    TensorProduct.prodLeft A A B₁ B₂ K w =
      ((LinearMap.fst A B₁ B₂).rTensor K w, (LinearMap.snd A B₁ B₂).rTensor K w) := by
  induction w with
  | zero => rw [map_zero, map_zero, map_zero]; rfl
  | tmul b k =>
    obtain ⟨b₁, b₂⟩ := b
    simp
  | add x y hx hy => simp only [map_add, hx, hy, Prod.mk_add_mk]

theorem tensor_prod_ext {A B₁ B₂ K : Type} [CommRing A] [AddCommGroup B₁] [Module A B₁]
    [AddCommGroup B₂] [Module A B₂] [AddCommGroup K] [Module A K] {w w' : (B₁ × B₂) ⊗[A] K}
    (h₁ : (LinearMap.fst A B₁ B₂).rTensor K w = (LinearMap.fst A B₁ B₂).rTensor K w')
    (h₂ : (LinearMap.snd A B₁ B₂).rTensor K w = (LinearMap.snd A B₁ B₂).rTensor K w') :
    w = w' := by
  apply (TensorProduct.prodLeft A A B₁ B₂ K).injective
  rw [prodLeft_eq_rTensor, prodLeft_eq_rTensor, h₁, h₂]

theorem mv_prod : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B₁ : Type) [CommRing B₁] [Algebra A B₁] (B₂ : Type) [CommRing B₂] [Algebra A B₂] (D : Type) [CommRing D] [Algebra A D] (r : ℕ → A) (ρ₁ : B₁ →ₐ[A] D) (ρ₂ : B₂ →ₐ[A] D), IsRt p r → Pf p D → (∀ y, ∃ b₁ b₂, y = ρ₁ b₁ - ρ₂ b₂) → (∀ (K : Type) [CommRing K] [Algebra A K], Pf p K → (∀ a : K, ((1 : B₁) ⊗ₜ[A] a) = 0 → ((1 : B₂) ⊗ₜ[A] a) = 0 → ∀ k, r k • a = 0) ∧ ∀ (w₁ : B₁ ⊗[A] K) (w₂ : B₂ ⊗[A] K), Algebra.TensorProduct.map ρ₁ (AlgHom.id A K) w₁ = Algebra.TensorProduct.map ρ₂ (AlgHom.id A K) w₂ → ∃ a : K, w₁ = (1 : B₁) ⊗ₜ[A] a ∧ w₂ = (1 : B₂) ⊗ₜ[A] a) → Cov p r (B₁ × B₂) := by
  intro p _ A _ B₁ _ _ B₂ _ _ D _ _ r ρ₁ ρ₂ hr hD hsurj hK
  let ρ : (B₁ × B₂) →ₗ[A] D :=
    ρ₁.toLinearMap ∘ₗ LinearMap.fst A B₁ B₂ - ρ₂.toLinearMap ∘ₗ LinearMap.snd A B₁ B₂
  have hρ : Function.Surjective ρ := by
    intro y
    obtain ⟨b₁, b₂, rfl⟩ := hsurj y
    exact ⟨(b₁, b₂), by simp [ρ]⟩
  have h1 : ρ 1 = 0 := by simp [ρ]
  refine mv_cov p A (B₁ × B₂) D r ρ hr hD hρ h1 ?_
  intro K _ _ hPK
  obtain ⟨hinj, hker⟩ := hK K hPK
  have hf : ∀ a : K, (LinearMap.fst A B₁ B₂).rTensor K ((1 : B₁ × B₂) ⊗ₜ[A] a) = (1 : B₁) ⊗ₜ[A] a := by
    intro a; simp
  have hs : ∀ a : K, (LinearMap.snd A B₁ B₂).rTensor K ((1 : B₁ × B₂) ⊗ₜ[A] a) = (1 : B₂) ⊗ₜ[A] a := by
    intro a; simp
  refine ⟨fun a ha => hinj a ?_ ?_, fun w hw => ?_⟩
  · rw [← hf, ha, map_zero]
  · rw [← hs, ha, map_zero]
  · have hcomm : ∀ t : (B₁ × B₂) ⊗[A] K, ρ.rTensor K t =
        Algebra.TensorProduct.map ρ₁ (AlgHom.id A K) ((LinearMap.fst A B₁ B₂).rTensor K t) -
          Algebra.TensorProduct.map ρ₂ (AlgHom.id A K) ((LinearMap.snd A B₁ B₂).rTensor K t) := by
      intro t
      induction t with
      | zero => simp
      | tmul b k => simp [ρ, TensorProduct.sub_tmul]
      | add x y hx hy =>
        simp only [map_add, hx, hy]
        abel
    have heq := hcomm w
    rw [hw, eq_comm, sub_eq_zero] at heq
    obtain ⟨a, ha₁, ha₂⟩ := hker _ _ heq
    exact ⟨a, tensor_prod_ext (by rw [ha₁, hf]) (by rw [ha₂, hs])⟩

end GlobalTheory.CompanionTheory.SnakeCov
