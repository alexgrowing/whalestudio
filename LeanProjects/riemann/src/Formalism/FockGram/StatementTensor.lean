import Formalism.FockGram.StatementLat

open Matrix LinearMap Module TensorProduct

noncomputable section

namespace Formalism.E

def tensorFunctional (R M₁ M₂ : Type*) [CommRing R] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] :
    (M₁ →ₗ[R] R) →ₗ[R] (M₂ →ₗ[R] R) →ₗ[R] (M₁ ⊗[R] M₂ →ₗ[R] R) :=
  (TensorProduct.mapBilinear (RingHom.id R) M₁ M₂ R R).compr₂
    (LinearMap.llcomp R (M₁ ⊗[R] M₂) (R ⊗[R] R) R (TensorProduct.lid R R).toLinearMap)

def htmul {R M₁ M₂ : Type*} [CommRing R] [StarRing R] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] (B₁ : M₁ →ₗ⋆[R] M₁ →ₗ[R] R) (B₂ : M₂ →ₗ⋆[R] M₂ →ₗ[R] R) :
    (M₁ ⊗[R] M₂) →ₗ⋆[R] (M₁ ⊗[R] M₂) →ₗ[R] R :=
  TensorProduct.lift (((tensorFunctional R M₁ M₂).comp B₁).compl₂ B₂)

def HTmulApply : Prop :=
  ∀ (R M₁ M₂ : Type) [CommRing R] [StarRing R] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] (B₁ : M₁ →ₗ⋆[R] M₁ →ₗ[R] R) (B₂ : M₂ →ₗ⋆[R] M₂ →ₗ[R] R)
    (x₁ y₁ : M₁) (x₂ y₂ : M₂),
    htmul B₁ B₂ (x₁ ⊗ₜ x₂) (y₁ ⊗ₜ y₂) = B₁ x₁ y₁ * B₂ x₂ y₂

def HTmulGram : Prop :=
  ∀ (R M₁ M₂ ι₁ ι₂ : Type) [CommRing R] [StarRing R] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (B₁ : M₁ →ₗ⋆[R] M₁ →ₗ[R] R) (B₂ : M₂ →ₗ⋆[R] M₂ →ₗ[R] R) (v₁ : ι₁ → M₁) (v₂ : ι₂ → M₂),
    sgram (htmul B₁ B₂) (fun p : ι₁ × ι₂ => v₁ p.1 ⊗ₜ[R] v₂ p.2) =
      Matrix.kroneckerMap (· * ·) (sgram B₁ v₁) (sgram B₂ v₂) ∧
    (sgram (htmul B₁ B₂) (fun p : ι₁ × ι₂ => v₁ p.1 ⊗ₜ[R] v₂ p.2)).det =
      (sgram B₁ v₁).det ^ Fintype.card ι₂ * (sgram B₂ v₂).det ^ Fintype.card ι₁

def HTmulHerm : Prop :=
  ∀ (R M₁ M₂ : Type) [CommRing R] [StarRing R] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] (B₁ : M₁ →ₗ⋆[R] M₁ →ₗ[R] R) (B₂ : M₂ →ₗ⋆[R] M₂ →ₗ[R] R),
    B₁.IsSymm → B₂.IsSymm → (htmul B₁ B₂).IsSymm

end Formalism.E
