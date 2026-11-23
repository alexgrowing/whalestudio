import Formalism.WachLatticeTwists.HerrComplexInjectivity.ExtInputNA
import Formalism.WachLatticeTwists.HerrComplexInjectivity.StatInvWach

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JN

open Formalism.CoboundaryTransfers Formalism.RepresentationBoundsCohomology.N1 Formalism.RepresentationBoundsCohomology.N2

def StatInvSES : Prop :=
  ∀ (O A A₀ : Type) [CommRing O] [CommRing A] [Algebra O A] [CommRing A₀] [Algebra O A₀]
    (S : HidaSetting O A) (B : Base O A₀) (Δ : Type) [Group Δ] [Fintype Δ] [MulSemiringAction Δ A]
    (IB : InvBase S B Δ) (ι : Type) (pr : Equiv.Perm ι) (D₀ D₁ D₂ : Type)
    [AddCommGroup D₀] [Module A D₀] [Module O D₀] [IsScalarTower O A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module O D₁] [IsScalarTower O A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module O D₂] [IsScalarTower O A D₂]
    (W₀ : NData S ι pr D₀) (W₁ : NData S ι pr D₁) (W₂ : NData S ι pr D₂) (E : NSES W₀ W₁ W₂)
    (ρ₀ : ι → Δ →* Module.End O D₀) (ρ₁ : ι → Δ →* Module.End O D₁)
    (ρ₂ : ι → Δ →* Module.End O D₂) (M₀ : ℕ) (D₀' D₁' D₂' : Type)
    [AddCommGroup D₀'] [Module A₀ D₀'] [Module O D₀'] [IsScalarTower O A₀ D₀']
    [AddCommGroup D₁'] [Module A₀ D₁'] [Module O D₁'] [IsScalarTower O A₀ D₁']
    [AddCommGroup D₂'] [Module A₀ D₂'] [Module O D₂'] [IsScalarTower O A₀ D₂']
    (V₀ : WachMod B M₀ D₀') (V₁ : WachMod B M₀ D₁') (V₂ : WachMod B M₀ D₂')
    (J₀ : InvMod IB W₀ ρ₀ V₀) (J₁ : InvMod IB W₁ ρ₁ V₁) (J₂ : InvMod IB W₂ ρ₂ V₂),
    J₀.Compat → J₁.Compat → J₂.Compat →
    (∀ i d x, E.ι.f i (ρ₀ i d x) = ρ₁ i d (E.ι.f i x)) →
    (∀ i d x, E.π.f i (ρ₁ i d x) = ρ₂ i d (E.π.f i x)) →
    (∀ i x, E.ι.f i x ∈ W₁.N i → x ∈ W₀.N i) →
    ∃ Sq : SES V₀ V₁ V₂, (∀ x i, J₁.j (Sq.ι.f x) i = E.ι.f i (J₀.j x i)) ∧
      (∀ x i, J₂.j (Sq.π.f x) i = E.π.f i (J₁.j x i))

def IsInv {O A A₀ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing A₀] [Algebra O A₀]
    {S : HidaSetting O A} {B : Base O A₀} {Δ : Type} [Group Δ] [Fintype Δ] [MulSemiringAction Δ A]
    (IB : InvBase S B Δ) {ι : Type} {pr : Equiv.Perm ι} {D : Type} [AddCommGroup D] [Module A D]
    [Module O D] [IsScalarTower O A D] (W : NData S ι pr D) (ρ : ι → Δ →* Module.End O D)
    {D' : Type} [AddCommGroup D'] [Module A₀ D'] [Module O D'] [IsScalarTower O A₀ D']
    (j : D' →ₗ[O] (ι → D)) (φ' γ' : D' →ₗ[O] D') : Prop :=
  Function.Injective j ∧ (∀ (a : A₀) (x : D') (i : ι), j (a • x) i = IB.j a • j x i) ∧
  (∀ x : ι → D, (∀ i d, ρ i d (x i) = x i) ↔ ∃ x', j x' = x) ∧
  (∀ x i, j (φ' x) i = W.φ i (j x (pr i))) ∧ (∀ x i, j (γ' x) i = W.γ i (j x i)) ∧
  (∀ i d (a : A) x, ρ i d (a • x) = (d • a) • ρ i d x)

def GammaSubOneInvariants {O A A₀ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing A₀] [Algebra O A₀]
    {S : HidaSetting O A} {B : Base O A₀} {Δ : Type} [Group Δ] [Fintype Δ] [MulSemiringAction Δ A]
    (IB : InvBase S B Δ) {ι : Type} {pr : Equiv.Perm ι} {D : Type} [AddCommGroup D] [Module A D]
    [Module O D] [IsScalarTower O A D] (W : NData S ι pr D) (ρ : ι → Δ →* Module.End O D) : Prop :=
  ∀ x : ι → D, (∀ i, x i ∈ W.N i) → (∀ i d, ρ i d (x i) = x i) →
    ∃ x' : ι → D, (∀ i, x' i ∈ W.N i) ∧ (∀ i d, ρ i d (x' i) = x' i) ∧
      ∀ i, W.γ i (x i) - x i = IB.j B.X • x' i

end Formalism.RepresentationBoundsCohomology.JN
