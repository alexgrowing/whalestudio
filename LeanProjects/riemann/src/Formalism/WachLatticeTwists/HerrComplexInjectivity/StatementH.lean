import Formalism.WachLatticeTwists.HerrComplexInjectivity.Statement

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JN

open Formalism.CoboundaryTransfers Formalism.RepresentationBoundsCohomology.N1 Formalism.RepresentationBoundsCohomology.N2

def IsProdP {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {S : HidaSetting O A} {ι : Type}
    {pr : Equiv.Perm ι} {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
    {M₀ : ℕ} (V' : WachMod (S.prodBase ι pr) M₀ (ι → D)) (W : NData S ι pr D) : Prop :=
  (∀ x, x ∈ V'.N ↔ ∀ i, x i ∈ W.N i) ∧ (∀ x i, V'.φ x i = W.φ i (x (pr i))) ∧
    (∀ x i, V'.γ x i = W.γ i (x i))

def IsLat {A' : Type} [CommRing A'] {D₁ : Type} [AddCommGroup D₁] [Module A' D₁] (ℓ : ℕ) (ϖ : A')
    (N₁ : Submodule A' D₁) : Prop :=
  Module.Free A' ↥N₁ ∧ Module.Finite A' ↥N₁ ∧
  (∀ (a : ℕ) (d : D₁), ∃ k : ℕ, ∃ n ∈ N₁, ∃ d' : D₁, ϖ ^ k • d = n + (ℓ : A') ^ a • d') ∧
  (∀ d : D₁, (ℓ : A') • d ∈ N₁ → d ∈ N₁) ∧
  (∀ d : D₁, (∃ k : ℕ, ϖ ^ k • ((ℓ : A') • d) ∈ N₁) → ∃ k : ℕ, ϖ ^ k • d ∈ N₁)

def FreeN {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {S : HidaSetting O A} {ι : Type}
    {pr : Equiv.Perm ι} {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
    (W : NData S ι pr D) : Prop :=
  ∃ (κ : Type) (_ : Fintype κ), ∀ i, Nonempty (Module.Basis κ A ↥(W.N i))

def StatLatProd : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (S : HidaSetting O A) (ι : Type) [Finite ι]
    (pr : Equiv.Perm ι) (D : Type) [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
    (W : NData S ι pr D) (M₀ : ℕ) (V' : WachMod (S.prodBase ι pr) M₀ (ι → D)),
    IsProdP V' W → InLattice W → FreeN W → IsLat S.ℓ (fun _ : ι => S.π) V'.N

def StatLatExt : Prop :=
  ∀ (A' : Type) [CommRing A'] (D D₁ D₂ : Type) [AddCommGroup D] [Module A' D] [AddCommGroup D₁]
    [Module A' D₁] [AddCommGroup D₂] [Module A' D₂] (ℓ : ℕ) (ϖ : A') (i : D →ₗ[A'] D₁)
    (p : D₁ →ₗ[A'] D₂) (N : Submodule A' D) (e : D₁),
    Function.Injective i → (∀ x, p x = 0 ↔ ∃ x₀, i x₀ = x) → Function.Surjective p →
    (∀ a : A', a • p e = 0 → a = 0) →
    IsLat ℓ ϖ N → IsLat ℓ ϖ (Submodule.span A' {p e}) →
    IsLat ℓ ϖ (N.map i ⊔ Submodule.span A' {e})

def CoboundaryRealisedByExtension {O A' : Type} [CommRing O] [CommRing A'] [Algebra O A'] {B : Base O A'} {M₀ : ℕ}
    {D : Type} [AddCommGroup D] [Module A' D] [Module O D] [IsScalarTower O A' D]
    (V' : WachMod B M₀ D) (ϖ : A') : Prop :=
  ∀ y z m : D, V'.C1 y z → y = V'.φ m - m → z = V'.γ m - m →
    ∃ (D₁ D₂ : Type) (_ : AddCommGroup D₁) (_ : Module A' D₁) (_ : Module O D₁)
      (_ : IsScalarTower O A' D₁) (_ : AddCommGroup D₂) (_ : Module A' D₂)
      (i : D →ₗ[A'] D₁) (p : D₁ →ₗ[A'] D₂) (φ₁ γ₁ : D₁ →ₗ[O] D₁) (e : D₁),
      Function.Injective i ∧ (∀ x, p x = 0 ↔ ∃ x₀, i x₀ = x) ∧ Function.Surjective p ∧
      (∀ a : A', a • p e = 0 → a = 0) ∧ IsLat B.p ϖ (Submodule.span A' {p e}) ∧
      (∀ (a : A') (x : D₁), φ₁ (a • x) = B.φ a • φ₁ x) ∧
      (∀ (a : A') (x : D₁), γ₁ (a • x) = B.γ a • γ₁ x) ∧
      (∀ x, φ₁ (i x) = i (V'.φ x)) ∧ (∀ x, γ₁ (i x) = i (V'.γ x)) ∧
      φ₁ e = e + i y ∧ γ₁ e = e + i z ∧
      (∀ N₁ N₂ : Submodule A' D₁, IsLat B.p ϖ N₁ → IsLat B.p ϖ N₂ →
        GammaTrivialFiniteHeightLattice B φ₁ γ₁ N₁ → GammaTrivialFiniteHeightLattice B φ₁ γ₁ N₂ → N₁ = N₂)

def StatHerrCore : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (S : HidaSetting O A) (ι : Type) [Finite ι]
    (pr : Equiv.Perm ι) (D : Type) [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
    (W : NData S ι pr D) (M h : ι → ℕ) (M₀ h₀ : ℕ),
    S.Rad → W.P2 → W.P5 M h → (∀ i, M i ≤ M₀) → (∀ i, h i ≤ h₀) →
    S.base.GammaModX → InLattice W → FreeN W →
    (∀ V' : WachMod (S.prodBase ι pr) M₀ (ι → D), IsProdP V' W → CoboundaryRealisedByExtension V' (fun _ : ι => S.π)) →
    ∀ y n m : ι → D, (∀ i, S.Q ^ M₀ • y i ∈ W.N i) → (∀ i, n i ∈ W.N i) →
      (∀ i, y i = W.φ i (m (pr i)) - m i) → (∀ i, S.X • n i = W.γ i (m i) - m i) →
      ∀ i, m i ∈ W.N i

def StatHerrInj : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (S : HidaSetting O A) (ι : Type) [Finite ι]
    (pr : Equiv.Perm ι) (D : Type) [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
    (W : NData S ι pr D) (M h : ι → ℕ) (M₀ h₀ : ℕ) (V : WachMod S.base M₀ (ι → D))
    (Hh : Type) [AddCommGroup Hh] [Module O Hh] (cl : V.Z1 →ₗ[O] Hh),
    S.Rad → IsProd V W → W.P2 → W.P5 M h → (∀ i, M i ≤ M₀) → (∀ i, h i ≤ h₀) →
    S.base.GammaModX → InLattice W → FreeN W →
    (∀ p : V.Z1, cl p = 0 → (p : (ι → D) × (ι → D)) ∈ V.B1) →
    (∀ V' : WachMod (S.prodBase ι pr) M₀ (ι → D), IsProdP V' W → CoboundaryRealisedByExtension V' (fun _ : ι => S.π)) →
    HerrInj V cl

def HerrComplexLiftSources : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] (S : HidaSetting ℤ_[ℓ] A)
    (ι : Type) [Finite ι] (pr : Equiv.Perm ι) (D₀ D₁ D₂ : Type)
    [AddCommGroup D₀] [Module A D₀] [Module ℤ_[ℓ] D₀] [IsScalarTower ℤ_[ℓ] A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module ℤ_[ℓ] D₁] [IsScalarTower ℤ_[ℓ] A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module ℤ_[ℓ] D₂] [IsScalarTower ℤ_[ℓ] A D₂]
    (W₀ : NData S ι pr D₀) (W₁ : NData S ι pr D₁) (W₂ : NData S ι pr D₂) (E : NSES W₀ W₁ W₂)
    (M h : ι → ℕ) (M₀ H : ℕ) (u : ℤ_[ℓ]ˣ) (jumps : Finset ℤ)
    (R P ρ κ : Type) [CommRing R] [Algebra ℤ_[ℓ] R] [AddCommGroup P] [Module R P] [Module ℤ_[ℓ] P]
    [IsScalarTower ℤ_[ℓ] R P] [Fintype κ] (L : P4 (O := ℤ_[ℓ]) (A := A) ι D₀ R P ρ κ)
    [IsAdicComplete (mI S) ↥(Submodule.pi Set.univ W₀.N)],
    S.ℓ = ℓ → IsUnit S.c₀ → (u : ℤ_[ℓ]) = S.u → S.Rad → S.Decomp → S.base.GammaModX →
    W₀.P2 → W₁.P2 → W₂.P2 → W₀.P5 M h → W₁.P5 M h → W₂.P5 M h →
    InLattice W₀ → InLattice W₁ → InLattice W₂ → LatticeSequenceExactUpToPrimePower E →
    (∀ i, M i ≤ M₀) → (∀ i, M i + h i ≤ H) →
    RegXQN W₀ → NoTors ℓ D₀ →
    L.Holds W₀ u → L.Test W₀ → (∀ x k, L.a x k ∈ jumps) →
    FreeN W₂ →
    (∀ V' : WachMod (S.prodBase ι pr) M₀ (ι → D₂), IsProdP V' W₂ → CoboundaryRealisedByExtension V' (fun _ : ι => S.π)) →
    ∃ (V₀ : WachMod S.base M₀ (ι → D₀)) (V₁ : WachMod S.base M₀ (ι → D₁))
      (V₂ : WachMod S.base M₀ (ι → D₂)) (Sq : SES V₀ V₁ V₂),
      IsProd V₀ W₀ ∧ IsProd V₁ W₁ ∧ IsProd V₂ W₂ ∧
      (∀ x i, Sq.ι.f x i = E.ι.f i (x i)) ∧ (∀ x i, Sq.π.f x i = E.π.f i (x i)) ∧
      ∀ (H₁ H₂ : Type) [AddCommGroup H₁] [Module ℤ_[ℓ] H₁] [AddCommGroup H₂] [Module ℤ_[ℓ] H₂]
        (cl₁ : V₁.Z1 →ₗ[ℤ_[ℓ]] H₁) (cl₂ : V₂.Z1 →ₗ[ℤ_[ℓ]] H₂) (Hf₁ : Submodule ℤ_[ℓ] H₁)
        (Hf₂ : Submodule ℤ_[ℓ] H₂) (g : H₁ →ₗ[ℤ_[ℓ]] H₂),
        ClNat Sq.π cl₁ cl₂ g → CocHf V₁ cl₁ Hf₁ → CocHf V₂ cl₂ Hf₂ →
        (∀ p : V₂.Z1, cl₂ p = 0 → (p : (ι → D₂) × (ι → D₂)) ∈ V₂.B1) →
        ExtInputN V₁ W₁ cl₁ Hf₁ M h → ExtInputN V₂ W₂ cl₂ Hf₂ M h → RatOnto g Hf₁ Hf₂ →
        ∀ κ' ∈ Hf₂, ∃ κ₁ ∈ Hf₁,
          g κ₁ = ((ℓ : ℤ_[ℓ]) ^ (2 * eWB ℓ H S.s + eUB ℓ M₀ S.s (JSet jumps M₀))) • κ'

end Formalism.RepresentationBoundsCohomology.JN
