import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup

noncomputable section

namespace GlobalTheory.StableLatCount

def adE (E : Type) [Field E] {A₁ A₂ : Type} [CommRing A₁] [CommRing A₂] [Algebra E A₁] [Algebra E A₂]
    (g₁ : A₁) (g₂ : A₂) : (A₂ →ₗ[E] A₁) →ₗ[E] (A₂ →ₗ[E] A₁) :=
  LinearMap.llcomp E A₂ A₁ A₁ (LinearMap.mulLeft E g₁) - LinearMap.lcomp E A₁ (LinearMap.mulLeft E g₂)

def homLat (E : Type) [Field E] {O A₁ A₂ : Type} [CommRing O] [Algebra O E] [CommRing A₁] [CommRing A₂]
    [Algebra E A₁] [Algebra E A₂] [Algebra O A₁] [Algebra O A₂] [IsScalarTower O E A₁]
    (M₁ : Submodule O A₁) (M₂ : Submodule O A₂) : Submodule O (A₂ →ₗ[E] A₁) where
  carrier := {ψ | ∀ x ∈ M₂, ψ x ∈ M₁}
  add_mem' := fun ha hb x hx => by simpa using M₁.add_mem (ha x hx) (hb x hx)
  zero_mem' := fun x _ => by simp
  smul_mem' := fun c ψ hψ x hx => by simpa using M₁.smul_mem c (hψ x hx)

theorem adE_apply (E : Type) [Field E] {A₁ A₂ : Type} [CommRing A₁] [CommRing A₂] [Algebra E A₁] [Algebra E A₂]
    (g₁ : A₁) (g₂ : A₂) (ψ : A₂ →ₗ[E] A₁) (x : A₂) : adE E g₁ g₂ ψ x = g₁ * ψ x - ψ (g₂ * x) := rfl

end GlobalTheory.StableLatCount
