import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.StatementTop

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JL

open Formalism.CoboundaryTransfers Formalism.RepresentationBoundsCohomology.N2

def LiftZ (ℓ : ℕ) [Fact ℓ.Prime] {H₁ H₂ : Type*} [AddCommGroup H₁] [Module ℤ_[ℓ] H₁]
    [AddCommGroup H₂] [Module ℤ_[ℓ] H₂] (Hf₁ : Submodule ℤ_[ℓ] H₁) (Hf₂ : Submodule ℤ_[ℓ] H₂)
    (g : H₁ →ₗ[ℤ_[ℓ]] H₂) (e : ℕ) : Prop :=
  ∀ κ ∈ Hf₂, ∃ κ₁ ∈ Hf₁, g κ₁ = ((ℓ : ℤ_[ℓ]) ^ e) • κ

def LiftO {O : Type*} [CommRing O] (ℓ : ℕ) {H₁ H₂ : Type*} [AddCommGroup H₁] [Module O H₁]
    [AddCommGroup H₂] [Module O H₂] (Hf₁ : Submodule O H₁) (Hf₂ : Submodule O H₂)
    (g : H₁ →ₗ[O] H₂) (e : ℕ) : Prop :=
  ∀ κ ∈ Hf₂, ((ℓ : O) ^ e) • κ ∈ Hf₁.map g

def StatScal : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (O : Type*) [CommRing O] [Algebra ℤ_[ℓ] O]
    (H₁ H₂ : Type*) [AddCommGroup H₁] [Module O H₁] [Module ℤ_[ℓ] H₁] [IsScalarTower ℤ_[ℓ] O H₁]
    [AddCommGroup H₂] [Module O H₂] [Module ℤ_[ℓ] H₂] [IsScalarTower ℤ_[ℓ] O H₂]
    (Hf₁ : Submodule O H₁) (Hf₂ : Submodule O H₂) (g : H₁ →ₗ[O] H₂) (e : ℕ),
    LiftZ ℓ (Hf₁.restrictScalars ℤ_[ℓ]) (Hf₂.restrictScalars ℤ_[ℓ]) (g.restrictScalars ℤ_[ℓ]) e ↔
      LiftO ℓ Hf₁ Hf₂ g e

def StatMono : Prop :=
  ∀ (O : Type*) [CommRing O] (ℓ : ℕ) (H₁ H₂ : Type*) [AddCommGroup H₁] [Module O H₁]
    [AddCommGroup H₂] [Module O H₂] (Hf₁ : Submodule O H₁) (Hf₂ : Submodule O H₂)
    (g : H₁ →ₗ[O] H₂) (e e' : ℕ), e ≤ e' → LiftO ℓ Hf₁ Hf₂ g e → LiftO ℓ Hf₁ Hf₂ g e'

def StatExpMonoB : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (M M' H H' s : ℕ) (jumps jumps' : Finset ℤ),
    jumps ⊆ jumps' → M ≤ M' → H ≤ H' →
    2 * eWB ℓ H s + eUB ℓ M s (JSet jumps M) ≤ 2 * eWB ℓ H' s + eUB ℓ M' s (JSet jumps' M')

def StatExpMonoA : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (M M' H H' : ℕ) (jumps jumps' : Finset ℤ),
    jumps ⊆ jumps' → M ≤ M' → H ≤ H' →
    2 * eWA ℓ H + eUA ℓ M (JSet jumps M) ≤ 2 * eWA ℓ H' + eUA ℓ M' (JSet jumps' M')

section FinalTheorems
variable (ℓ : ℕ) [Fact ℓ.Prime] {H₁ H₂ : Type} [AddCommGroup H₁] [Module ℤ_[ℓ] H₁]
    [AddCommGroup H₂] [Module ℤ_[ℓ] H₂] (Hf₁ : Submodule ℤ_[ℓ] H₁) (Hf₂ : Submodule ℤ_[ℓ] H₂)
    (g : H₁ →ₗ[ℤ_[ℓ]] H₂) (e : ℕ)

def ProdB : Prop :=
  ∃ (A : Type) (_ : CommRing A) (_ : Algebra ℤ_[ℓ] A) (B : Base ℤ_[ℓ] A) (M : ℕ)
    (u : ℤ_[ℓ]ˣ) (s H : ℕ) (jumps : Finset ℤ) (D₀ D₁ D₂ : Type)
    (_ : AddCommGroup D₀) (_ : Module A D₀) (_ : Module ℤ_[ℓ] D₀) (_ : IsScalarTower ℤ_[ℓ] A D₀)
    (_ : AddCommGroup D₁) (_ : Module A D₁) (_ : Module ℤ_[ℓ] D₁) (_ : IsScalarTower ℤ_[ℓ] A D₁)
    (_ : AddCommGroup D₂) (_ : Module A D₂) (_ : Module ℤ_[ℓ] D₂) (_ : IsScalarTower ℤ_[ℓ] A D₂)
    (W₀ : WachMod B M D₀) (W₁ : WachMod B M D₁) (W₂ : WachMod B M D₂) (S : SES W₀ W₁ W₂)
    (cl₁ : W₁.Z1 →ₗ[ℤ_[ℓ]] H₁) (cl₂ : W₂.Z1 →ₗ[ℤ_[ℓ]] H₂) (I : Ideal A)
    (_ : IsAdicComplete I W₀.N),
    B.p = ℓ ∧ B.φ B.X = B.X * B.Q ∧ B.GammaX (u : ℤ_[ℓ]) ∧ B.GammaQ ∧
    1 ≤ s ∧ (ℓ = 2 → 2 ≤ s) ∧ PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = s ∧
    B.Q ∈ I ∧ (∀ a ∈ I, B.φ a ∈ I) ∧ RegXQ W₀ ∧ RegLQ W₀ ∧ NoTors ℓ D₀ ∧
    XKills S.π H ∧ SemiB W₀ u jumps ∧
    ClNat S.π cl₁ cl₂ g ∧ CocHf W₁ cl₁ Hf₁ ∧ CocHf W₂ cl₂ Hf₂ ∧ HerrInj W₂ cl₂ ∧
    ExtInput W₁ cl₁ Hf₁ H ∧ ExtInput W₂ cl₂ Hf₂ H ∧ RatOnto g Hf₁ Hf₂ ∧
    e = 2 * eWB ℓ H s + eUB ℓ M s (JSet jumps M)

def ProdA : Prop :=
  ℓ ≠ 2 ∧ ∃ (A : Type) (_ : CommRing A) (_ : Algebra ℤ_[ℓ] A) (B : Base ℤ_[ℓ] A) (M : ℕ)
    (u : ℤ_[ℓ]ˣ) (H : ℕ) (jumps : Finset ℤ) (c : ℤ → ℤ_[ℓ]) (D₀ D₁ D₂ : Type)
    (_ : AddCommGroup D₀) (_ : Module A D₀) (_ : Module ℤ_[ℓ] D₀) (_ : IsScalarTower ℤ_[ℓ] A D₀)
    (_ : AddCommGroup D₁) (_ : Module A D₁) (_ : Module ℤ_[ℓ] D₁) (_ : IsScalarTower ℤ_[ℓ] A D₁)
    (_ : AddCommGroup D₂) (_ : Module A D₂) (_ : Module ℤ_[ℓ] D₂) (_ : IsScalarTower ℤ_[ℓ] A D₂)
    (W₀ : WachMod B M D₀) (W₁ : WachMod B M D₁) (W₂ : WachMod B M D₂) (S : SES W₀ W₁ W₂)
    (δ : D₀ →ₗ[ℤ_[ℓ]] D₀)
    (cl₁ : W₁.Z1 →ₗ[ℤ_[ℓ]] H₁) (cl₂ : W₂.Z1 →ₗ[ℤ_[ℓ]] H₂) (I : Ideal A)
    (_ : IsAdicComplete I W₀.N),
    B.p = ℓ ∧ B.PhiX (ℓ - 1) ∧ B.GammaX ((u : ℤ_[ℓ]) ^ (ℓ - 1)) ∧
    PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = 1 ∧
    (∀ j : ℤ, (ℓ : ℤ_[ℓ]) * c j = 1 - ((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) ∧
    (∀ y, B.X • δ y = W₀.γ y - y) ∧
    B.Q ∈ I ∧ (∀ a ∈ I, B.φ a ∈ I) ∧ RegLQ W₀ ∧ NoTors ℓ D₀ ∧
    XKills S.π ((H + (ℓ - 2)) / (ℓ - 1)) ∧ SemiA W₀ δ c jumps ∧
    ClNat S.π cl₁ cl₂ g ∧ CocHf W₁ cl₁ Hf₁ ∧ CocHf W₂ cl₂ Hf₂ ∧ HerrInj W₂ cl₂ ∧
    ExtInput W₁ cl₁ Hf₁ ((H + (ℓ - 2)) / (ℓ - 1)) ∧
    ExtInput W₂ cl₂ Hf₂ ((H + (ℓ - 2)) / (ℓ - 1)) ∧ RatOnto g Hf₁ Hf₂ ∧
    e = 2 * eWA ℓ H + eUA ℓ M (JSet jumps M)

def ProdSub : Prop :=
  ∃ (K₁ K₂ : Type) (_ : AddCommGroup K₁) (_ : Module ℤ_[ℓ] K₁) (_ : AddCommGroup K₂)
    (_ : Module ℤ_[ℓ] K₂) (Kf₁ : Submodule ℤ_[ℓ] K₁) (Kf₂ : Submodule ℤ_[ℓ] K₂)
    (h : K₁ →ₗ[ℤ_[ℓ]] K₂) (res₂ : H₂ →ₗ[ℤ_[ℓ]] K₂) (cor₁ : K₁ →ₗ[ℤ_[ℓ]] H₁)
    (cor₂ : K₂ →ₗ[ℤ_[ℓ]] H₂) (n E : ℕ),
    0 < n ∧ (∀ x, cor₂ (res₂ x) = (n : ℤ_[ℓ]) • x) ∧ (∀ x, g (cor₁ x) = cor₂ (h x)) ∧
    (∀ x ∈ Hf₂, res₂ x ∈ Kf₂) ∧ (∀ x ∈ Kf₁, cor₁ x ∈ Hf₁) ∧
    (ProdB ℓ Kf₁ Kf₂ h E ∨ ProdA ℓ Kf₁ Kf₂ h E) ∧ e = E + padicValNat ℓ n

def LiftSrc : Prop := ProdB ℓ Hf₁ Hf₂ g e ∨ ProdA ℓ Hf₁ Hf₂ g e ∨ ProdSub ℓ Hf₁ Hf₂ g e

end FinalTheorems

def StatSrc : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (H₁ H₂ : Type) [AddCommGroup H₁] [Module ℤ_[ℓ] H₁]
    [AddCommGroup H₂] [Module ℤ_[ℓ] H₂] (Hf₁ : Submodule ℤ_[ℓ] H₁) (Hf₂ : Submodule ℤ_[ℓ] H₂)
    (g : H₁ →ₗ[ℤ_[ℓ]] H₂) (e : ℕ), LiftSrc ℓ Hf₁ Hf₂ g e → LiftZ ℓ Hf₁ Hf₂ g e

def LiftSrcO (ℓ : ℕ) [Fact ℓ.Prime] {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O]
    {H₁ H₂ : Type} [AddCommGroup H₁] [Module O H₁] [Module ℤ_[ℓ] H₁] [IsScalarTower ℤ_[ℓ] O H₁]
    [AddCommGroup H₂] [Module O H₂] [Module ℤ_[ℓ] H₂] [IsScalarTower ℤ_[ℓ] O H₂]
    (Hf₁ : Submodule O H₁) (Hf₂ : Submodule O H₂) (g : H₁ →ₗ[O] H₂) (e' : ℕ) : Prop :=
  ∃ e ≤ e', LiftSrc ℓ (Hf₁.restrictScalars ℤ_[ℓ]) (Hf₂.restrictScalars ℤ_[ℓ])
    (g.restrictScalars ℤ_[ℓ]) e

def StatSrcO : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [Algebra ℤ_[ℓ] O]
    (H₁ H₂ : Type) [AddCommGroup H₁] [Module O H₁] [Module ℤ_[ℓ] H₁] [IsScalarTower ℤ_[ℓ] O H₁]
    [AddCommGroup H₂] [Module O H₂] [Module ℤ_[ℓ] H₂] [IsScalarTower ℤ_[ℓ] O H₂]
    (Hf₁ : Submodule O H₁) (Hf₂ : Submodule O H₂) (g : H₁ →ₗ[O] H₂) (e' : ℕ),
    LiftSrcO ℓ Hf₁ Hf₂ g e' → LiftO ℓ Hf₁ Hf₂ g e'

end Formalism.RepresentationBoundsCohomology.JL
