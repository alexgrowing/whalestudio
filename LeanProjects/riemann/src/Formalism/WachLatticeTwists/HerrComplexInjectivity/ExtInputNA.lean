import Formalism.WachLatticeTwists.HerrComplexInjectivity.StatementA

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JN

open Formalism.CoboundaryTransfers Formalism.RepresentationBoundsCohomology.N1 Formalism.RepresentationBoundsCohomology.N2

def DeltaMod {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {S : HidaSetting O A} {ι : Type}
    {pr : Equiv.Perm ι} {D₁ D₂ : Type}
    [AddCommGroup D₁] [Module A D₁] [Module O D₁] [IsScalarTower O A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module O D₂] [IsScalarTower O A D₂]
    {W₁ : NData S ι pr D₁} {W₂ : NData S ι pr D₂} (F : NHom W₁ W₂) {Δ : Type} [Group Δ]
    [MulSemiringAction Δ A] (ρ₁ : ι → Δ →* Module.End O D₁) (ρ₂ : ι → Δ →* Module.End O D₂) : Prop :=
  (∀ i d, ∀ x ∈ W₁.N i, ρ₁ i d x ∈ W₁.N i) ∧
  (∀ i d x, F.f i (ρ₁ i d x) = ρ₂ i d (F.f i x)) ∧
  (∀ i d (a : A) x, ρ₂ i d (a • x) = (d • a) • ρ₂ i d x)

def ExtInputNA {ℓ : ℕ} [Fact ℓ.Prime] {A A₀ : Type} [CommRing A] [Algebra ℤ_[ℓ] A] [CommRing A₀]
    [Algebra ℤ_[ℓ] A₀] {S : HidaSetting ℤ_[ℓ] A} {B : Base ℤ_[ℓ] A₀} {Δ : Type} [Group Δ] [Fintype Δ]
    [MulSemiringAction Δ A] (IB : InvBase S B Δ) {ι : Type} {pr : Equiv.Perm ι} {D : Type}
    [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D] (W : NData S ι pr D)
    {M₀ : ℕ} {D' : Type} [AddCommGroup D'] [Module A₀ D'] [Module ℤ_[ℓ] D']
    [IsScalarTower ℤ_[ℓ] A₀ D'] (V : WachMod B M₀ D') {Hh : Type} [AddCommGroup Hh]
    [Module ℤ_[ℓ] Hh] (cl : V.Z1 →ₗ[ℤ_[ℓ]] Hh) (Hf : Submodule ℤ_[ℓ] Hh) (M h : ι → ℕ) : Prop :=
  ∀ κ ∈ Hf, ∃ (X : ExtDatum V) (Dp Dt : Type) (_ : AddCommGroup Dp) (_ : Module A Dp)
    (_ : Module ℤ_[ℓ] Dp) (_ : IsScalarTower ℤ_[ℓ] A Dp) (_ : AddCommGroup Dt) (_ : Module A Dt)
    (_ : Module ℤ_[ℓ] Dt) (_ : IsScalarTower ℤ_[ℓ] A Dt) (Wp : NData S ι pr Dp)
    (Wt : NData S ι pr Dt) (E : NSES W Wp Wt) (ρp : ι → Δ →* Module.End ℤ_[ℓ] Dp)
    (ρt : ι → Δ →* Module.End ℤ_[ℓ] Dt) (Jp : InvMod IB Wp ρp X.Wp) (Jt : InvMod IB Wt ρt X.Wt),
    Wp.P2 ∧ Wt.P2 ∧ Wp.P5 M h ∧ Wt.P5 M h ∧ InLattice Wp ∧ InLattice Wt ∧ LatticeSequenceExactUpToPrimePower E ∧
    Jp.Compat ∧ Jt.Compat ∧
    DeltaMod E.π ρp ρt ∧ (∀ x i, Jt.j (X.S.π.f x) i = E.π.f i (Jp.j x i)) ∧ X.Dict cl κ

def StatExtA : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A A₀ : Type) [CommRing A] [Algebra ℤ_[ℓ] A] [CommRing A₀]
    [Algebra ℤ_[ℓ] A₀] (S : HidaSetting ℤ_[ℓ] A) (B : Base ℤ_[ℓ] A₀) (Δ : Type) [Group Δ] [Fintype Δ]
    [MulSemiringAction Δ A] (IB : InvBase S B Δ) (ι : Type) [Finite ι] (pr : Equiv.Perm ι)
    (D : Type) [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]
    (W : NData S ι pr D) (M₀ : ℕ) (D' : Type) [AddCommGroup D'] [Module A₀ D'] [Module ℤ_[ℓ] D']
    [IsScalarTower ℤ_[ℓ] A₀ D'] (V : WachMod B M₀ D') (Hh : Type) [AddCommGroup Hh]
    [Module ℤ_[ℓ] Hh] (cl : V.Z1 →ₗ[ℤ_[ℓ]] Hh) (Hf : Submodule ℤ_[ℓ] Hh) (M h : ι → ℕ) (H : ℕ),
    S.ℓ = ℓ → S.s = 1 → S.Rad → S.Decomp → W.P2 → W.P5 M h → InLattice W →
    (∀ i, M i ≤ M₀) → (∀ i, M i + h i ≤ H) → Fintype.card Δ = ℓ - 1 → DeltaRing IB →
    ExtInputNA IB W V cl Hf M h → ExtInput V cl Hf ((H + (ℓ - 2)) / (ℓ - 1))

def P4.HoldsA {O A₀ : Type} [CommRing O] [CommRing A₀] [Algebra O A₀] {B : Base O A₀} {M₀ : ℕ}
    {D' : Type} [AddCommGroup D'] [Module A₀ D'] [Module O D'] [IsScalarTower O A₀ D']
    {R P ρ κ : Type} [CommRing R] [Algebra O R] [AddCommGroup P] [Module R P] [Module O P]
    [IsScalarTower O R P] (L : P4 (O := O) (A := A₀) Unit D' R P ρ κ) (V : WachMod B M₀ D')
    (u : Oˣ) (ϖ : O) : Prop :=
  L.γR L.t = (u : O) • L.t ∧
  (∀ r : R, ∃ r' : R, L.γR r - r = L.t * r') ∧
  Function.Bijective (fun v : P => L.t • v) ∧
  (∀ x (r : R) (v : P), L.γl x (r • v) = L.γR r • L.γl x v) ∧
  (∀ x (b : A₀) (d : D'), (∃ k : ℕ, B.Q ^ k • d ∈ V.N) → L.loc x (b • d) = L.locA x b • L.loc x d) ∧
  (∀ x d, (∃ k : ℕ, B.Q ^ k • d ∈ V.N) → L.loc x (V.γ d) = L.γl x (L.loc x d)) ∧
  (∀ x, ∃ v : R, IsUnit v ∧ L.locA x B.Q = v * L.t) ∧
  (∀ x, IsUnit (L.locA x B.X) ∧ ∃ r₀ : R, L.locA x B.X = algebraMap O R ϖ + L.t * r₀) ∧
  (∀ x, ∀ d ∈ V.N, L.loc x d ∈ Submodule.span R (Set.range (L.n x))) ∧
  (∀ x k, L.γl x (L.n x k) = ((u ^ (-L.a x k) : Oˣ) : O) • L.n x k) ∧
  (∀ d, (∃ k : ℕ, B.Q ^ k • d ∈ V.N) →
    (∀ x, L.loc x d ∈ Submodule.span R (Set.range (L.n x))) → d ∈ V.N)

def StatCompA : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ 2 → ∀ (A A₀ : Type) [CommRing A] [Algebra ℤ_[ℓ] A] [CommRing A₀]
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
    (V₀ : WachMod B M₀ D₀') (V₁ : WachMod B M₀ D₁') (V₂ : WachMod B M₀ D₂') (Sq : SES V₀ V₁ V₂)
    (J₀ : InvMod IB W₀ ρ₀ V₀) (J₁ : InvMod IB W₁ ρ₁ V₁) (J₂ : InvMod IB W₂ ρ₂ V₂)
    (u : ℤ_[ℓ]ˣ) (jumps : Finset ℤ) (δ : D₀' →ₗ[ℤ_[ℓ]] D₀')
    (R P ρ κ : Type) [CommRing R] [Algebra ℤ_[ℓ] R] [AddCommGroup P] [Module R P] [Module ℤ_[ℓ] P]
    [IsScalarTower ℤ_[ℓ] R P] [Fintype κ] (L : P4 (O := ℤ_[ℓ]) (A := A₀) Unit D₀' R P ρ κ)
    (H₁ H₂ : Type) [AddCommGroup H₁] [Module ℤ_[ℓ] H₁] [AddCommGroup H₂] [Module ℤ_[ℓ] H₂]
    (cl₁ : V₁.Z1 →ₗ[ℤ_[ℓ]] H₁) (cl₂ : V₂.Z1 →ₗ[ℤ_[ℓ]] H₂) (Hf₁ : Submodule ℤ_[ℓ] H₁)
    (Hf₂ : Submodule ℤ_[ℓ] H₂) (g : H₁ →ₗ[ℤ_[ℓ]] H₂)
    [IsAdicComplete (Ideal.span {(ℓ : A₀), B.X}) V₀.N],

    S.ℓ = ℓ → S.s = 1 → IsUnit S.c₀ → (u : ℤ_[ℓ]) = S.u → S.Rad → S.Decomp →
    W₀.P2 → W₁.P2 → W₂.P2 → W₀.P5 M h → W₁.P5 M h → W₂.P5 M h →
    InLattice W₀ → InLattice W₁ → InLattice W₂ → LatticeSequenceExactUpToPrimePower E →
    (∀ i, M i ≤ M₀) → (∀ i, M i + h i ≤ H) →

    B.p = ℓ → Fintype.card Δ = ℓ - 1 → DeltaRing IB → S.base.GammaModX →
    (∀ a : A, (∀ d : Δ, d • (S.π * a) = S.π * a) →
      ∃ a' : A, (∀ d : Δ, d • a' = a') ∧ S.π * a = IB.j B.X * a') →
    (∀ a : A, IB.j B.X * a = 0 → a = 0) →
    B.QLin → (∃ w : A₀, B.γ B.X - B.X = B.X * B.Q * w) → B.X ∈ (⊥ : Ideal A₀).jacobson →
    J₀.Compat → J₁.Compat → J₂.Compat →
    DeltaMod E.π ρ₁ ρ₂ → (∀ x i, J₂.j (Sq.π.f x) i = E.π.f i (J₁.j x i)) →

    (∀ y, B.X • δ y = V₀.γ y - y) → NoTors ℓ D₀ →
    L.HoldsA V₀ u (-(ℓ : ℤ_[ℓ])) → (∀ x k, L.a x k ∈ jumps) →

    ClNat Sq.π cl₁ cl₂ g → CocHf V₁ cl₁ Hf₁ → CocHf V₂ cl₂ Hf₂ → HerrInj V₂ cl₂ →
    ExtInputNA IB W₁ V₁ cl₁ Hf₁ M h → ExtInputNA IB W₂ V₂ cl₂ Hf₂ M h → RatOnto g Hf₁ Hf₂ →
    ∀ κ' ∈ Hf₂, ∃ κ₁ ∈ Hf₁,
      g κ₁ = ((ℓ : ℤ_[ℓ]) ^ (2 * eWA ℓ H + eUA ℓ M₀ (JSet jumps M₀))) • κ'

end Formalism.RepresentationBoundsCohomology.JN
