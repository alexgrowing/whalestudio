import Formalism.WachLatticeTwists.SplitLocalLifts.Statement
import Formalism.WachLatticeTwists.HerrComplexInjectivity.Statement

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.SplitClassesAll

open Formalism.CoboundaryTransfers Formalism.RepresentationBoundsCohomology.N1 Formalism.RepresentationBoundsCohomology.N2 Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JN

section FinalTheorems
variable (ℓ : ℕ) [Fact ℓ.Prime] {H₁ H₂ : Type} [AddCommGroup H₁] [Module ℤ_[ℓ] H₁]
    [AddCommGroup H₂] [Module ℤ_[ℓ] H₂] (Hf₁ : Submodule ℤ_[ℓ] H₁) (Hf₂ : Submodule ℤ_[ℓ] H₂)
    (g : H₁ →ₗ[ℤ_[ℓ]] H₂) (e : ℕ)

def SrcNB : Prop :=
  ∃ (A : Type) (_ : CommRing A) (_ : Algebra ℤ_[ℓ] A) (S : HidaSetting ℤ_[ℓ] A)
    (ι : Type) (_ : Finite ι) (pr : Equiv.Perm ι) (D₀ D₁ D₂ : Type)
    (_ : AddCommGroup D₀) (_ : Module A D₀) (_ : Module ℤ_[ℓ] D₀) (_ : IsScalarTower ℤ_[ℓ] A D₀)
    (_ : AddCommGroup D₁) (_ : Module A D₁) (_ : Module ℤ_[ℓ] D₁) (_ : IsScalarTower ℤ_[ℓ] A D₁)
    (_ : AddCommGroup D₂) (_ : Module A D₂) (_ : Module ℤ_[ℓ] D₂) (_ : IsScalarTower ℤ_[ℓ] A D₂)
    (W₀ : NData S ι pr D₀) (W₁ : NData S ι pr D₁) (W₂ : NData S ι pr D₂) (E : NSES W₀ W₁ W₂)
    (M h : ι → ℕ) (M₀ H : ℕ) (u : ℤ_[ℓ]ˣ) (jumps : Finset ℤ)
    (R P ρ κ : Type) (_ : CommRing R) (_ : Algebra ℤ_[ℓ] R) (_ : AddCommGroup P) (_ : Module R P)
    (_ : Module ℤ_[ℓ] P) (_ : IsScalarTower ℤ_[ℓ] R P) (_ : Fintype κ)
    (L : P4 (O := ℤ_[ℓ]) (A := A) ι D₀ R P ρ κ)
    (_ : IsAdicComplete (mI S) ↥(Submodule.pi Set.univ W₀.N)),
    S.ℓ = ℓ ∧ IsUnit S.c₀ ∧ (u : ℤ_[ℓ]) = S.u ∧ S.Rad ∧ S.Decomp ∧
    W₀.P2 ∧ W₁.P2 ∧ W₂.P2 ∧ W₀.P5 M h ∧ W₁.P5 M h ∧ W₂.P5 M h ∧
    InLattice W₀ ∧ InLattice W₁ ∧ InLattice W₂ ∧ LatticeSequenceExactUpToPrimePower E ∧
    (∀ i, M i ≤ M₀) ∧ (∀ i, M i + h i ≤ H) ∧
    RegXQN W₀ ∧ NoTors ℓ D₀ ∧
    L.Holds W₀ u ∧ L.Test W₀ ∧ (∀ x k, L.a x k ∈ jumps) ∧
    (∀ (V₀ : WachMod S.base M₀ (ι → D₀)) (V₁ : WachMod S.base M₀ (ι → D₁))
      (V₂ : WachMod S.base M₀ (ι → D₂)) (Sq : SES V₀ V₁ V₂),
      IsProd V₀ W₀ → IsProd V₁ W₁ → IsProd V₂ W₂ →
      (∀ x i, Sq.ι.f x i = E.ι.f i (x i)) → (∀ x i, Sq.π.f x i = E.π.f i (x i)) →
      ∃ (cl₁ : V₁.Z1 →ₗ[ℤ_[ℓ]] H₁) (cl₂ : V₂.Z1 →ₗ[ℤ_[ℓ]] H₂),
        ClNat Sq.π cl₁ cl₂ g ∧ CocHf V₁ cl₁ Hf₁ ∧ CocHf V₂ cl₂ Hf₂ ∧ HerrInj V₂ cl₂ ∧
        ExtInputN V₁ W₁ cl₁ Hf₁ M h ∧ ExtInputN V₂ W₂ cl₂ Hf₂ M h) ∧
    RatOnto g Hf₁ Hf₂ ∧
    e = 2 * eWB ℓ H S.s + eUB ℓ M₀ S.s (JSet jumps M₀)

def SrcN : Prop :=
  SrcNB ℓ Hf₁ Hf₂ g e ∨
  ∃ (K₁ K₂ : Type) (_ : AddCommGroup K₁) (_ : Module ℤ_[ℓ] K₁) (_ : AddCommGroup K₂)
    (_ : Module ℤ_[ℓ] K₂) (Kf₁ : Submodule ℤ_[ℓ] K₁) (Kf₂ : Submodule ℤ_[ℓ] K₂)
    (h : K₁ →ₗ[ℤ_[ℓ]] K₂) (res₂ : H₂ →ₗ[ℤ_[ℓ]] K₂) (cor₁ : K₁ →ₗ[ℤ_[ℓ]] H₁)
    (cor₂ : K₂ →ₗ[ℤ_[ℓ]] H₂) (n E : ℕ),
    0 < n ∧ (∀ x, cor₂ (res₂ x) = (n : ℤ_[ℓ]) • x) ∧ (∀ x, g (cor₁ x) = cor₂ (h x)) ∧
    (∀ x ∈ Hf₂, res₂ x ∈ Kf₂) ∧ (∀ x ∈ Kf₁, cor₁ x ∈ Hf₁) ∧
    SrcNB ℓ Kf₁ Kf₂ h E ∧ e = E + padicValNat ℓ n

end FinalTheorems

def SrcNO (ℓ : ℕ) [Fact ℓ.Prime] {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O]
    {H₁ H₂ : Type} [AddCommGroup H₁] [Module O H₁] [Module ℤ_[ℓ] H₁] [IsScalarTower ℤ_[ℓ] O H₁]
    [AddCommGroup H₂] [Module O H₂] [Module ℤ_[ℓ] H₂] [IsScalarTower ℤ_[ℓ] O H₂]
    (Hf₁ : Submodule O H₁) (Hf₂ : Submodule O H₂) (g : H₁ →ₗ[O] H₂) (e' : ℕ) : Prop :=
  ∃ e ≤ e', SrcN ℓ (Hf₁.restrictScalars ℤ_[ℓ]) (Hf₂.restrictScalars ℤ_[ℓ])
    (g.restrictScalars ℤ_[ℓ]) e

def StatSrcNB : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (H₁ H₂ : Type) [AddCommGroup H₁] [Module ℤ_[ℓ] H₁]
    [AddCommGroup H₂] [Module ℤ_[ℓ] H₂] (Hf₁ : Submodule ℤ_[ℓ] H₁) (Hf₂ : Submodule ℤ_[ℓ] H₂)
    (g : H₁ →ₗ[ℤ_[ℓ]] H₂) (e : ℕ), SrcNB ℓ Hf₁ Hf₂ g e → ProdB ℓ Hf₁ Hf₂ g e

def StatSrcN : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (H₁ H₂ : Type) [AddCommGroup H₁] [Module ℤ_[ℓ] H₁]
    [AddCommGroup H₂] [Module ℤ_[ℓ] H₂] (Hf₁ : Submodule ℤ_[ℓ] H₁) (Hf₂ : Submodule ℤ_[ℓ] H₂)
    (g : H₁ →ₗ[ℤ_[ℓ]] H₂) (e : ℕ), SrcN ℓ Hf₁ Hf₂ g e → LiftSrc ℓ Hf₁ Hf₂ g e

def StatSrcNO : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [Algebra ℤ_[ℓ] O]
    (H₁ H₂ : Type) [AddCommGroup H₁] [Module O H₁] [Module ℤ_[ℓ] H₁] [IsScalarTower ℤ_[ℓ] O H₁]
    [AddCommGroup H₂] [Module O H₂] [Module ℤ_[ℓ] H₂] [IsScalarTower ℤ_[ℓ] O H₂]
    (Hf₁ : Submodule O H₁) (Hf₂ : Submodule O H₂) (g : H₁ →ₗ[O] H₂) (e' : ℕ),
    SrcNO ℓ Hf₁ Hf₂ g e' → LiftSrcO ℓ Hf₁ Hf₂ g e'

end Formalism.RepresentationBoundsCohomology.SplitClassesAll
