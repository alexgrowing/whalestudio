import Formalism.WachLatticeTwists.HerrComplexInjectivity.Statement

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JN

open Formalism.CoboundaryTransfers Formalism.RepresentationBoundsCohomology.N1 Formalism.RepresentationBoundsCohomology.N2

structure InvBase {O A A₀ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing A₀]
    [Algebra O A₀] (S : HidaSetting O A) (B : Base O A₀) (Δ : Type) [Group Δ] [Fintype Δ]
    [MulSemiringAction Δ A] where
  j : A₀ →ₐ[O] A
  j_inj : Function.Injective j
  j_range : ∀ a : A, (∀ d : Δ, d • a = a) ↔ ∃ a₀, j a₀ = a
  j_φ : ∀ a, j (B.φ a) = S.φ (j a)
  j_γ : ∀ a, j (B.γ a) = S.γ (j a)

def DeltaRing {O A A₀ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing A₀]
    [Algebra O A₀] {S : HidaSetting O A} {B : Base O A₀} {Δ : Type} [Group Δ] [Fintype Δ]
    [MulSemiringAction Δ A] (IB : InvBase S B Δ) : Prop :=
  (∀ (d : Δ) (a : A), S.φ (d • a) = d • S.φ a) ∧ (∀ (d : Δ) (a : A), S.γ (d • a) = d • S.γ a) ∧
  (∀ d : Δ, ∃ w : A, IsUnit w ∧ d • S.π = w * S.π) ∧
  (∃ r : A, IsUnit r ∧ S.Q = r * IB.j B.Q) ∧
  (∃ ε₀ : A₀, IsUnit ε₀ ∧ IB.j B.X = IB.j ε₀ * ∏ d : Δ, d • S.π)

def StatBaseA : Prop :=
  ∀ (O A A₀ : Type) [CommRing O] [CommRing A] [Algebra O A] [CommRing A₀] [Algebra O A₀]
    (S : HidaSetting O A) (B : Base O A₀) (Δ : Type) [Group Δ] [Fintype Δ] [MulSemiringAction Δ A]
    (IB : InvBase S B Δ),
    S.s = 1 → DeltaRing IB → S.base.GammaModX →
    (∀ a : A, (∀ d : Δ, d • (S.π * a) = S.π * a) →
      ∃ a' : A, (∀ d : Δ, d • a' = a') ∧ S.π * a = IB.j B.X * a') →
    (∀ a : A, IB.j B.X * a = 0 → a = 0) →
    B.PhiX (Fintype.card Δ) ∧ B.GammaX (S.u ^ Fintype.card Δ)

def StatGammaQA : Prop :=
  ∀ (O A₀ : Type) [CommRing O] [CommRing A₀] [Algebra O A₀] (B : Base O A₀),
    B.QLin → (∃ w : A₀, B.γ B.X - B.X = B.X * B.Q * w) → B.X ∈ (⊥ : Ideal A₀).jacobson → B.GammaQ

structure InvMod {O A A₀ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing A₀]
    [Algebra O A₀] {S : HidaSetting O A} {B : Base O A₀} {Δ : Type} [Group Δ] [Fintype Δ]
    [MulSemiringAction Δ A] (IB : InvBase S B Δ) {ι : Type} {pr : Equiv.Perm ι} {D : Type}
    [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D] (W : NData S ι pr D)
    (ρ : ι → Δ →* Module.End O D) {M₀ : ℕ} {D' : Type} [AddCommGroup D'] [Module A₀ D']
    [Module O D'] [IsScalarTower O A₀ D'] (V : WachMod B M₀ D') where
  j : D' →ₗ[O] (ι → D)
  j_inj : Function.Injective j
  j_smul : ∀ (a : A₀) (x : D') (i : ι), j (a • x) i = IB.j a • j x i
  j_range : ∀ x : ι → D, (∀ i d, ρ i d (x i) = x i) ↔ ∃ x', j x' = x
  j_N : ∀ x', x' ∈ V.N ↔ ∀ i, j x' i ∈ W.N i

def InvMod.Compat {O A A₀ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing A₀]
    [Algebra O A₀] {S : HidaSetting O A} {B : Base O A₀} {Δ : Type} [Group Δ] [Fintype Δ]
    [MulSemiringAction Δ A] {IB : InvBase S B Δ} {ι : Type} {pr : Equiv.Perm ι} {D : Type}
    [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D] {W : NData S ι pr D}
    {ρ : ι → Δ →* Module.End O D} {M₀ : ℕ} {D' : Type} [AddCommGroup D'] [Module A₀ D']
    [Module O D'] [IsScalarTower O A₀ D'] {V : WachMod B M₀ D'} (J : InvMod IB W ρ V) : Prop :=
  (∀ x i, J.j (V.φ x) i = W.φ i (J.j x (pr i))) ∧ (∀ x i, J.j (V.γ x) i = W.γ i (J.j x i))

def StatCeil : Prop :=
  ∀ (ℓ H : ℕ), 2 ≤ ℓ →
    ⌈((1 * H : ℕ) : ℚ) / ((ℓ - 1 : ℕ) : ℚ)⌉₊ = (H + (ℓ - 2)) / (ℓ - 1)

def StatXKillsA : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A A₀ : Type) [CommRing A] [Algebra ℤ_[ℓ] A] [CommRing A₀]
    [Algebra ℤ_[ℓ] A₀] (S : HidaSetting ℤ_[ℓ] A) (B : Base ℤ_[ℓ] A₀) (Δ : Type) [Group Δ] [Fintype Δ]
    [MulSemiringAction Δ A] (IB : InvBase S B Δ) (ι : Type) [Finite ι] (pr : Equiv.Perm ι)
    (D₀ D₁ D₂ : Type)
    [AddCommGroup D₀] [Module A D₀] [Module ℤ_[ℓ] D₀] [IsScalarTower ℤ_[ℓ] A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module ℤ_[ℓ] D₁] [IsScalarTower ℤ_[ℓ] A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module ℤ_[ℓ] D₂] [IsScalarTower ℤ_[ℓ] A D₂]
    (W₀ : NData S ι pr D₀) (W₁ : NData S ι pr D₁) (W₂ : NData S ι pr D₂) (E : NSES W₀ W₁ W₂)
    (M h : ι → ℕ) (M₀ H : ℕ)
    (ρ₁ : ι → Δ →* Module.End ℤ_[ℓ] D₁) (ρ₂ : ι → Δ →* Module.End ℤ_[ℓ] D₂)
    (D₁' D₂' : Type)
    [AddCommGroup D₁'] [Module A₀ D₁'] [Module ℤ_[ℓ] D₁'] [IsScalarTower ℤ_[ℓ] A₀ D₁']
    [AddCommGroup D₂'] [Module A₀ D₂'] [Module ℤ_[ℓ] D₂'] [IsScalarTower ℤ_[ℓ] A₀ D₂']
    (V₁ : WachMod B M₀ D₁') (V₂ : WachMod B M₀ D₂') (F : Hom V₁ V₂)
    (J₁ : InvMod IB W₁ ρ₁ V₁) (J₂ : InvMod IB W₂ ρ₂ V₂),
    S.ℓ = ℓ → S.s = 1 → S.Rad → S.Decomp →
    W₀.P2 → W₁.P2 → W₂.P2 → W₀.P5 M h → W₁.P5 M h → W₂.P5 M h →
    InLattice W₀ → InLattice W₁ → InLattice W₂ → LatticeSequenceExactUpToPrimePower E →
    (∀ i, M i ≤ M₀) → (∀ i, M i + h i ≤ H) →
    Fintype.card Δ = ℓ - 1 → DeltaRing IB →
    (∀ i d, ∀ x ∈ W₁.N i, ρ₁ i d x ∈ W₁.N i) →
    (∀ i d x, E.π.f i (ρ₁ i d x) = ρ₂ i d (E.π.f i x)) →
    (∀ i d (a : A) x, ρ₂ i d (a • x) = (d • a) • ρ₂ i d x) →
    (∀ x i, J₂.j (F.f x) i = E.π.f i (J₁.j x i)) →
    XKills F ((H + (ℓ - 2)) / (ℓ - 1))

def StatRegLQA : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A A₀ : Type) [CommRing A] [Algebra ℤ_[ℓ] A] [CommRing A₀]
    [Algebra ℤ_[ℓ] A₀] (S : HidaSetting ℤ_[ℓ] A) (B : Base ℤ_[ℓ] A₀) (Δ : Type) [Group Δ] [Fintype Δ]
    [MulSemiringAction Δ A] (IB : InvBase S B Δ) (ι : Type) (pr : Equiv.Perm ι) (D : Type)
    [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]
    (W : NData S ι pr D) (ρ : ι → Δ →* Module.End ℤ_[ℓ] D) (M₀ : ℕ) (D' : Type)
    [AddCommGroup D'] [Module A₀ D'] [Module ℤ_[ℓ] D'] [IsScalarTower ℤ_[ℓ] A₀ D']
    (V : WachMod B M₀ D') (_J : InvMod IB W ρ V),
    S.ℓ = ℓ → InLattice W → RegLQ V ∧ (NoTors ℓ D → NoTors ℓ D')

def StatSemiA : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A R : Type) [CommRing A] [CommRing R] [Algebra ℤ_[ℓ] A]
    [Algebra ℤ_[ℓ] R] (B : Base ℤ_[ℓ] A) (M : ℕ) (D P : Type)
    [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]
    [AddCommGroup P] [Module R P] [Module ℤ_[ℓ] P] [IsScalarTower ℤ_[ℓ] R P]
    (W : WachMod B M D) (dd : D →ₗ[ℤ_[ℓ]] D) (u : ℤ_[ℓ]ˣ) (c : ℤ → ℤ_[ℓ]) (jumps : Finset ℤ)
    (ρ κ : Type) [Fintype κ]
    (t : R) (γR : R →ₐ[ℤ_[ℓ]] R) (locA : ρ → A →+* R) (loc : ρ → D →ₗ[ℤ_[ℓ]] P)
    (γl : ρ → P →ₗ[ℤ_[ℓ]] P) (n : ρ → κ → P) (a : ρ → κ → ℤ),
    B.GammaQ →
    (∀ v, B.X • dd v = W.γ v - v) →
    γR t = (u : ℤ_[ℓ]) • t →
    (∀ r : R, ∃ r' : R, γR r - r = t * r') →
    Function.Bijective (fun v : P => t • v) →
    (∀ x (r : R) (v : P), γl x (r • v) = γR r • γl x v) →
    (∀ x (b : A) (d : D), (∃ k : ℕ, B.Q ^ k • d ∈ W.N) → loc x (b • d) = locA x b • loc x d) →
    (∀ x d, (∃ k : ℕ, B.Q ^ k • d ∈ W.N) → loc x (W.γ d) = γl x (loc x d)) →
    (∀ x, ∃ v : R, IsUnit v ∧ locA x B.Q = v * t) →
    (∀ x, IsUnit (locA x B.X) ∧
      ∃ r₀ : R, locA x B.X = algebraMap ℤ_[ℓ] R (-(ℓ : ℤ_[ℓ])) + t * r₀) →
    (∀ j : ℤ, (ℓ : ℤ_[ℓ]) * c j = 1 - ((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) →
    (∀ x, ∀ d ∈ W.N, loc x d ∈ Submodule.span R (Set.range (n x))) →
    (∀ x k, γl x (n x k) = ((u ^ (-a x k) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • n x k) →
    (∀ d, (∃ k : ℕ, B.Q ^ k • d ∈ W.N) →
      (∀ x, loc x d ∈ Submodule.span R (Set.range (n x))) → d ∈ W.N) →
    (∀ x k, a x k ∈ jumps) →
    SemiA W dd c jumps

end Formalism.RepresentationBoundsCohomology.JN
