import Formalism.WachLatticeTwists.HerrComplexInjectivity.GammaSubOneInvariants
import Formalism.WachLatticeTwists.HerrComplexInjectivity.StatementH

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JN

open Formalism.CoboundaryTransfers Formalism.RepresentationBoundsCohomology.N1 Formalism.RepresentationBoundsCohomology.N2

def GammaSubOneStatedForm : Prop :=
  ∀ (O A A₀ : Type) [CommRing O] [CommRing A] [Algebra O A] [CommRing A₀] [Algebra O A₀]
    (S : HidaSetting O A) (B : Base O A₀) (Δ : Type) [Group Δ] [Fintype Δ] [MulSemiringAction Δ A]
    (IB : InvBase S B Δ) (ι : Type) (pr : Equiv.Perm ι) (D : Type) [AddCommGroup D] [Module A D]
    [Module O D] [IsScalarTower O A D] (W : NData S ι pr D) (ρ : ι → Δ →* Module.End O D)
    (κ : Type) [Fintype κ] (b : ∀ i, Module.Basis κ A ↥(W.N i)),
    S.s = 1 → W.P2 →
    (∀ i d (a : A) x, ρ i d (a • x) = (d • a) • ρ i d x) →
    (∀ i d, ∀ x ∈ W.N i, ρ i d x ∈ W.N i) →
    (∀ i d k, ρ i d (b i k : D) = (b i k : D)) →
    (∀ i d x, W.γ i (ρ i d x) = ρ i d (W.γ i x)) →
    (∀ a : A, (∀ d : Δ, d • (S.π * a) = S.π * a) →
      ∃ a' : A, (∀ d : Δ, d • a' = a') ∧ S.π * a = IB.j B.X * a') →
    GammaSubOneInvariants IB W ρ

def DeltaN {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {S : HidaSetting O A} {ι : Type}
    {pr : Equiv.Perm ι} {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
    {Δ : Type} [Group Δ] [MulSemiringAction Δ A] (W : NData S ι pr D)
    (ρ : ι → Δ →* Module.End O D) : Prop :=
  (∀ i d (a : A) x, ρ i d (a • x) = (d • a) • ρ i d x) ∧
  (∀ i d x, W.φ i (ρ (pr i) d x) = ρ i d (W.φ i x)) ∧
  (∀ i d x, W.γ i (ρ i d x) = ρ i d (W.γ i x)) ∧
  (∀ i d, ∀ x ∈ W.N i, ∃ x' ∈ W.N i, ρ i d x - x = S.π • x') ∧
  FreeN W

def StatDeltaBasis : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (S : HidaSetting O A) (Δ : Type) [Group Δ]
    [Fintype Δ] [MulSemiringAction Δ A] (ι : Type) (pr : Equiv.Perm ι) (D : Type) [AddCommGroup D]
    [Module A D] [Module O D] [IsScalarTower O A D] (W : NData S ι pr D)
    (ρ : ι → Δ →* Module.End O D),
    S.Rad → IsUnit ((Fintype.card Δ : ℕ) : A) → DeltaN W ρ →
    (∀ i d, ∀ x ∈ W.N i, ρ i d x ∈ W.N i) ∧
    ∃ (κ : Type) (_ : Fintype κ) (b : ∀ i, Module.Basis κ A ↥(W.N i)),
      ∀ i d k, ρ i d (b i k : D) = (b i k : D)

def StatInvExists : Prop :=
  ∀ (O A A₀ : Type) [CommRing O] [CommRing A] [Algebra O A] [CommRing A₀] [Algebra O A₀]
    (S : HidaSetting O A) (B : Base O A₀) (Δ : Type) [Group Δ] [Fintype Δ] [MulSemiringAction Δ A]
    (IB : InvBase S B Δ) (ι : Type) (pr : Equiv.Perm ι) (D : Type) [AddCommGroup D] [Module A D]
    [Module O D] [IsScalarTower O A D] (W : NData S ι pr D) (ρ : ι → Δ →* Module.End O D),
    (∀ i d (a : A) x, ρ i d (a • x) = (d • a) • ρ i d x) →
    (∀ i d x, W.φ i (ρ (pr i) d x) = ρ i d (W.φ i x)) →
    (∀ i d x, W.γ i (ρ i d x) = ρ i d (W.γ i x)) →
    ∃ (D' : Type) (_ : AddCommGroup D') (_ : Module A₀ D') (_ : Module O D')
      (_ : IsScalarTower O A₀ D') (j : D' →ₗ[O] (ι → D)) (φ' γ' : D' →ₗ[O] D'),
      IsInv IB W ρ j φ' γ'

end Formalism.RepresentationBoundsCohomology.JN
