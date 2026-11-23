import Formalism.WachLatticeTwists.HerrComplexInjectivity.StatementA

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JN

open Formalism.CoboundaryTransfers Formalism.RepresentationBoundsCohomology.N1 Formalism.RepresentationBoundsCohomology.N2

def StatInvWach : Prop :=
  ∀ (O A A₀ : Type) [CommRing O] [CommRing A] [Algebra O A] [CommRing A₀] [Algebra O A₀]
    (S : HidaSetting O A) (B : Base O A₀) (Δ : Type) [Group Δ] [Fintype Δ] [MulSemiringAction Δ A]
    (IB : InvBase S B Δ) (ι : Type) (pr : Equiv.Perm ι) (D : Type) [AddCommGroup D] [Module A D]
    [Module O D] [IsScalarTower O A D] (W : NData S ι pr D) (ρ : ι → Δ →* Module.End O D)
    (M h : ι → ℕ) (M₀ : ℕ) (D' : Type) [AddCommGroup D'] [Module A₀ D'] [Module O D']
    [IsScalarTower O A₀ D'] (j : D' →ₗ[O] (ι → D)) (φ' γ' : D' →ₗ[O] D'),
    S.s = 1 → DeltaRing IB → B.GammaQ → W.P5 M h → (∀ i, M i ≤ M₀) →
    Function.Injective j → (∀ (a : A₀) (x : D') (i : ι), j (a • x) i = IB.j a • j x i) →
    (∀ x : ι → D, (∀ i d, ρ i d (x i) = x i) ↔ ∃ x', j x' = x) →
    (∀ x i, j (φ' x) i = W.φ i (j x (pr i))) → (∀ x i, j (γ' x) i = W.γ i (j x i)) →
    (∀ i d (a : A) x, ρ i d (a • x) = (d • a) • ρ i d x) →
    (∀ x : ι → D, (∀ i, x i ∈ W.N i) → (∀ i d, ρ i d (x i) = x i) →
      ∃ x' : ι → D, (∀ i, x' i ∈ W.N i) ∧ (∀ i d, ρ i d (x' i) = x' i) ∧
        ∀ i, W.γ i (x i) - x i = IB.j B.X • x' i) →
    ∃ (V : WachMod B M₀ D') (J : InvMod IB W ρ V), J.j = j ∧ V.φ = φ' ∧ V.γ = γ'

end Formalism.RepresentationBoundsCohomology.JN
