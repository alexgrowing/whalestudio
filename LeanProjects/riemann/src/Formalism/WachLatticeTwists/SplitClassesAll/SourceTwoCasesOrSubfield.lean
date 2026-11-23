import Formalism.WachLatticeTwists.SplitClassesAll.StatSrcNB
import Formalism.WachLatticeTwists.HerrComplexInjectivity.LiftCaseAHerrSources

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.SplitClassesAll

open Formalism.CoboundaryTransfers Formalism.RepresentationBoundsCohomology.N1 Formalism.RepresentationBoundsCohomology.N2 Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JN

section FinalTheorems
variable (ℓ : ℕ) [Fact ℓ.Prime] {H₁ H₂ : Type} [AddCommGroup H₁] [Module ℤ_[ℓ] H₁]
    [AddCommGroup H₂] [Module ℤ_[ℓ] H₂] (Hf₁ : Submodule ℤ_[ℓ] H₁) (Hf₂ : Submodule ℤ_[ℓ] H₂)
    (g : H₁ →ₗ[ℤ_[ℓ]] H₂) (e : ℕ)

def SrcNA : Prop :=
  ℓ ≠ 2 ∧ ∀ Pp : Prop,
  (∀ (A A₀ : Type) [CommRing A] [Algebra ℤ_[ℓ] A] [CommRing A₀]
    [Algebra ℤ_[ℓ] A₀] (S : HidaSetting ℤ_[ℓ] A) (B : Base ℤ_[ℓ] A₀) (Δ : Type) [Group Δ] [Fintype Δ]
    [MulSemiringAction Δ A] (IB : InvBase S B Δ) (ι : Type) [Finite ι] (pr : Equiv.Perm ι)
    (D₀ D₁ D₂ : Type)
    [AddCommGroup D₀] [Module A D₀] [Module ℤ_[ℓ] D₀] [IsScalarTower ℤ_[ℓ] A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module ℤ_[ℓ] D₁] [IsScalarTower ℤ_[ℓ] A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module ℤ_[ℓ] D₂] [IsScalarTower ℤ_[ℓ] A D₂]
    (W₀ : NData S ι pr D₀) (W₁ : NData S ι pr D₁) (W₂ : NData S ι pr D₂) (E : NSES W₀ W₁ W₂)
    (M h : ι → ℕ) (M₀ H : ℕ)
    (ρ₀ : ι → Δ →* Module.End ℤ_[ℓ] D₀) (ρ₁ : ι → Δ →* Module.End ℤ_[ℓ] D₁)
    (ρ₂ : ι → Δ →* Module.End ℤ_[ℓ] D₂) (D₀' D₁' D₂' : Type)
    [AddCommGroup D₀'] [Module A₀ D₀'] [Module ℤ_[ℓ] D₀'] [IsScalarTower ℤ_[ℓ] A₀ D₀']
    [AddCommGroup D₁'] [Module A₀ D₁'] [Module ℤ_[ℓ] D₁'] [IsScalarTower ℤ_[ℓ] A₀ D₁']
    [AddCommGroup D₂'] [Module A₀ D₂'] [Module ℤ_[ℓ] D₂'] [IsScalarTower ℤ_[ℓ] A₀ D₂']
    (j₀ : D₀' →ₗ[ℤ_[ℓ]] (ι → D₀)) (j₁ : D₁' →ₗ[ℤ_[ℓ]] (ι → D₁)) (j₂ : D₂' →ₗ[ℤ_[ℓ]] (ι → D₂))
    (φ₀ γ₀ : D₀' →ₗ[ℤ_[ℓ]] D₀') (φ₁ γ₁ : D₁' →ₗ[ℤ_[ℓ]] D₁') (φ₂ γ₂ : D₂' →ₗ[ℤ_[ℓ]] D₂')
    (u : ℤ_[ℓ]ˣ) (jumps : Finset ℤ),
    S.ℓ = ℓ → S.s = 1 → IsUnit S.c₀ → (u : ℤ_[ℓ]) = S.u → S.Rad → S.Decomp →
    W₀.P2 → W₁.P2 → W₂.P2 → W₀.P5 M h → W₁.P5 M h → W₂.P5 M h →
    InLattice W₀ → InLattice W₁ → InLattice W₂ → LatticeSequenceExactUpToPrimePower E →
    (∀ i, M i ≤ M₀) → (∀ i, M i + h i ≤ H) →
    B.p = ℓ → Fintype.card Δ = ℓ - 1 → DeltaRing IB → S.base.GammaModX →
    (∀ a : A, (∀ d : Δ, d • (S.π * a) = S.π * a) →
      ∃ a' : A, (∀ d : Δ, d • a' = a') ∧ S.π * a = IB.j B.X * a') →
    (∀ a : A, IB.j B.X * a = 0 → a = 0) →
    B.QLin → (∃ w : A₀, B.γ B.X - B.X = B.X * B.Q * w) → B.X ∈ (⊥ : Ideal A₀).jacobson →
    IsInv IB W₀ ρ₀ j₀ φ₀ γ₀ → IsInv IB W₁ ρ₁ j₁ φ₁ γ₁ → IsInv IB W₂ ρ₂ j₂ φ₂ γ₂ →
    DeltaN W₀ ρ₀ → DeltaN W₁ ρ₁ → DeltaN W₂ ρ₂ →
    (∀ i d x, E.ι.f i (ρ₀ i d x) = ρ₁ i d (E.ι.f i x)) →
    (∀ i d x, E.π.f i (ρ₁ i d x) = ρ₂ i d (E.π.f i x)) →
    NoTors ℓ D₀ →
    (∀ (V₀ : WachMod B M₀ D₀') (V₁ : WachMod B M₀ D₁') (V₂ : WachMod B M₀ D₂') (Sq : SES V₀ V₁ V₂)
      (J₀ : InvMod IB W₀ ρ₀ V₀) (J₁ : InvMod IB W₁ ρ₁ V₁) (J₂ : InvMod IB W₂ ρ₂ V₂),
      (J₀.j = j₀ ∧ V₀.φ = φ₀ ∧ V₀.γ = γ₀) → (J₁.j = j₁ ∧ V₁.φ = φ₁ ∧ V₁.γ = γ₁) →
      (J₂.j = j₂ ∧ V₂.φ = φ₂ ∧ V₂.γ = γ₂) →
      (∀ x i, J₁.j (Sq.ι.f x) i = E.ι.f i (J₀.j x i)) →
      (∀ x i, J₂.j (Sq.π.f x) i = E.π.f i (J₁.j x i)) →
      ∃ (δ : D₀' →ₗ[ℤ_[ℓ]] D₀')
        (R P ρ κ : Type) (_ : CommRing R) (_ : Algebra ℤ_[ℓ] R) (_ : AddCommGroup P) (_ : Module R P)
        (_ : Module ℤ_[ℓ] P) (_ : IsScalarTower ℤ_[ℓ] R P) (_ : Fintype κ)
        (L : P4 (O := ℤ_[ℓ]) (A := A₀) Unit D₀' R P ρ κ)
        (cl₁ : V₁.Z1 →ₗ[ℤ_[ℓ]] H₁) (cl₂ : V₂.Z1 →ₗ[ℤ_[ℓ]] H₂)
        (_ : IsAdicComplete (Ideal.span {(ℓ : A₀), B.X}) V₀.N),
        (∀ y, B.X • δ y = V₀.γ y - y) ∧
        L.HoldsA V₀ u (-(ℓ : ℤ_[ℓ])) ∧ (∀ x k, L.a x k ∈ jumps) ∧
        ClNat Sq.π cl₁ cl₂ g ∧ CocHf V₁ cl₁ Hf₁ ∧ CocHf V₂ cl₂ Hf₂ ∧ HerrInj V₂ cl₂ ∧
        ExtInputNL J₁ cl₁ Hf₁ M h ∧ ExtInputNL J₂ cl₂ Hf₂ M h) →
    RatOnto g Hf₁ Hf₂ →
    e = 2 * eWA ℓ H + eUA ℓ M₀ (JSet jumps M₀) → Pp) → Pp

def sourceTwoCasesOrSubfield : Prop :=
  SrcNB ℓ Hf₁ Hf₂ g e ∨ SrcNA ℓ Hf₁ Hf₂ g e ∨
  ∃ (K₁ K₂ : Type) (_ : AddCommGroup K₁) (_ : Module ℤ_[ℓ] K₁) (_ : AddCommGroup K₂)
    (_ : Module ℤ_[ℓ] K₂) (Kf₁ : Submodule ℤ_[ℓ] K₁) (Kf₂ : Submodule ℤ_[ℓ] K₂)
    (h : K₁ →ₗ[ℤ_[ℓ]] K₂) (res₂ : H₂ →ₗ[ℤ_[ℓ]] K₂) (cor₁ : K₁ →ₗ[ℤ_[ℓ]] H₁)
    (cor₂ : K₂ →ₗ[ℤ_[ℓ]] H₂) (n E : ℕ),
    0 < n ∧ (∀ x, cor₂ (res₂ x) = (n : ℤ_[ℓ]) • x) ∧ (∀ x, g (cor₁ x) = cor₂ (h x)) ∧
    (∀ x ∈ Hf₂, res₂ x ∈ Kf₂) ∧ (∀ x ∈ Kf₁, cor₁ x ∈ Hf₁) ∧
    (SrcNB ℓ Kf₁ Kf₂ h E ∨ SrcNA ℓ Kf₁ Kf₂ h E) ∧ e = E + padicValNat ℓ n

end FinalTheorems

def SrcNO2 (ℓ : ℕ) [Fact ℓ.Prime] {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O]
    {H₁ H₂ : Type} [AddCommGroup H₁] [Module O H₁] [Module ℤ_[ℓ] H₁] [IsScalarTower ℤ_[ℓ] O H₁]
    [AddCommGroup H₂] [Module O H₂] [Module ℤ_[ℓ] H₂] [IsScalarTower ℤ_[ℓ] O H₂]
    (Hf₁ : Submodule O H₁) (Hf₂ : Submodule O H₂) (g : H₁ →ₗ[O] H₂) (e' : ℕ) : Prop :=
  ∃ e ≤ e', sourceTwoCasesOrSubfield ℓ (Hf₁.restrictScalars ℤ_[ℓ]) (Hf₂.restrictScalars ℤ_[ℓ])
    (g.restrictScalars ℤ_[ℓ]) e

def StatSrcNA : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (H₁ H₂ : Type) [AddCommGroup H₁] [Module ℤ_[ℓ] H₁]
    [AddCommGroup H₂] [Module ℤ_[ℓ] H₂] (Hf₁ : Submodule ℤ_[ℓ] H₁) (Hf₂ : Submodule ℤ_[ℓ] H₂)
    (g : H₁ →ₗ[ℤ_[ℓ]] H₂) (e : ℕ), SrcNA ℓ Hf₁ Hf₂ g e → ProdA ℓ Hf₁ Hf₂ g e

def SourceTwoCases : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (H₁ H₂ : Type) [AddCommGroup H₁] [Module ℤ_[ℓ] H₁]
    [AddCommGroup H₂] [Module ℤ_[ℓ] H₂] (Hf₁ : Submodule ℤ_[ℓ] H₁) (Hf₂ : Submodule ℤ_[ℓ] H₂)
    (g : H₁ →ₗ[ℤ_[ℓ]] H₂) (e : ℕ), sourceTwoCasesOrSubfield ℓ Hf₁ Hf₂ g e → LiftSrc ℓ Hf₁ Hf₂ g e

def StatSrcNO2 : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [Algebra ℤ_[ℓ] O]
    (H₁ H₂ : Type) [AddCommGroup H₁] [Module O H₁] [Module ℤ_[ℓ] H₁] [IsScalarTower ℤ_[ℓ] O H₁]
    [AddCommGroup H₂] [Module O H₂] [Module ℤ_[ℓ] H₂] [IsScalarTower ℤ_[ℓ] O H₂]
    (Hf₁ : Submodule O H₁) (Hf₂ : Submodule O H₂) (g : H₁ →ₗ[O] H₂) (e' : ℕ),
    SrcNO2 ℓ Hf₁ Hf₂ g e' → LiftSrcO ℓ Hf₁ Hf₂ g e'

def SourceCaseBSpecial : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [Algebra ℤ_[ℓ] O]
    (H₁ H₂ : Type) [AddCommGroup H₁] [Module O H₁] [Module ℤ_[ℓ] H₁] [IsScalarTower ℤ_[ℓ] O H₁]
    [AddCommGroup H₂] [Module O H₂] [Module ℤ_[ℓ] H₂] [IsScalarTower ℤ_[ℓ] O H₂]
    (Hf₁ : Submodule O H₁) (Hf₂ : Submodule O H₂) (g : H₁ →ₗ[O] H₂) (e' : ℕ),
    SrcNO ℓ Hf₁ Hf₂ g e' → SrcNO2 ℓ Hf₁ Hf₂ g e'

end Formalism.RepresentationBoundsCohomology.SplitClassesAll
