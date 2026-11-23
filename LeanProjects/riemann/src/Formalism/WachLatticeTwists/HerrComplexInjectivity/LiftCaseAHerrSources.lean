import Formalism.WachLatticeTwists.HerrComplexInjectivity.GammaSubOneStatedForm
import Formalism.WachLatticeTwists.HerrComplexInjectivity.StatementH

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JN

open Formalism.CoboundaryTransfers Formalism.RepresentationBoundsCohomology.N1 Formalism.RepresentationBoundsCohomology.N2

def ExtInputNL {ℓ : ℕ} [Fact ℓ.Prime] {A A₀ : Type} [CommRing A] [Algebra ℤ_[ℓ] A] [CommRing A₀]
    [Algebra ℤ_[ℓ] A₀] {S : HidaSetting ℤ_[ℓ] A} {B : Base ℤ_[ℓ] A₀} {Δ : Type} [Group Δ] [Fintype Δ]
    [MulSemiringAction Δ A] {IB : InvBase S B Δ} {ι : Type} {pr : Equiv.Perm ι} {D : Type}
    [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D] {W : NData S ι pr D}
    {ρ : ι → Δ →* Module.End ℤ_[ℓ] D} {M₀ : ℕ} {D' : Type} [AddCommGroup D'] [Module A₀ D']
    [Module ℤ_[ℓ] D'] [IsScalarTower ℤ_[ℓ] A₀ D'] {V : WachMod B M₀ D'} (J : InvMod IB W ρ V)
    {Hh : Type} [AddCommGroup Hh] [Module ℤ_[ℓ] Hh] (cl : V.Z1 →ₗ[ℤ_[ℓ]] Hh)
    (Hf : Submodule ℤ_[ℓ] Hh) (M h : ι → ℕ) : Prop :=
  ∀ κ ∈ Hf, ∃ (Dp Dt : Type) (_ : AddCommGroup Dp) (_ : Module A Dp) (_ : Module ℤ_[ℓ] Dp)
    (_ : IsScalarTower ℤ_[ℓ] A Dp) (_ : AddCommGroup Dt) (_ : Module A Dt) (_ : Module ℤ_[ℓ] Dt)
    (_ : IsScalarTower ℤ_[ℓ] A Dt) (Wp : NData S ι pr Dp) (Wt : NData S ι pr Dt)
    (E : NSES W Wp Wt) (ρp : ι → Δ →* Module.End ℤ_[ℓ] Dp) (ρt : ι → Δ →* Module.End ℤ_[ℓ] Dt)
    (e : ι → Dt),
    Wp.P2 ∧ Wt.P2 ∧ Wp.P5 M h ∧ Wt.P5 M h ∧ InLattice Wp ∧ InLattice Wt ∧ LatticeSequenceExactUpToPrimePower E ∧
    DeltaN Wp ρp ∧ DeltaN Wt ρt ∧
    (∀ i d x, E.ι.f i (ρ i d x) = ρp i d (E.ι.f i x)) ∧
    (∀ i d x, E.π.f i (ρp i d x) = ρt i d (E.π.f i x)) ∧
    (∀ i, e i ∈ Wt.N i) ∧ (∀ i, Wt.φ i (e (pr i)) = e i) ∧ (∀ i, Wt.γ i (e i) = e i) ∧
    (∀ i d, ρt i d (e i) = e i) ∧
    ∀ (c : ℤ_[ℓ]) (x : ι → Dp) (p : V.Z1), (∀ i d, ρp i d (x i) = x i) →
      (∀ i, E.π.f i (x i) = c • e i) →
      (∀ i, E.ι.f i (J.j (p : D' × D').1 i) = Wp.φ i (x (pr i)) - x i) →
      (∀ i, E.ι.f i (J.j (p : D' × D').2 i) = Wp.γ i (x i) - x i) →
      cl p = c • κ

def StatExtNL : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A A₀ : Type) [CommRing A] [Algebra ℤ_[ℓ] A] [CommRing A₀]
    [Algebra ℤ_[ℓ] A₀] (S : HidaSetting ℤ_[ℓ] A) (B : Base ℤ_[ℓ] A₀) (Δ : Type) [Group Δ] [Fintype Δ]
    [MulSemiringAction Δ A] (IB : InvBase S B Δ) (ι : Type) [Finite ι] (pr : Equiv.Perm ι)
    (D : Type) [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]
    (W : NData S ι pr D) (ρ : ι → Δ →* Module.End ℤ_[ℓ] D) (M₀ : ℕ) (D' : Type) [AddCommGroup D']
    [Module A₀ D'] [Module ℤ_[ℓ] D'] [IsScalarTower ℤ_[ℓ] A₀ D'] (V : WachMod B M₀ D')
    (J : InvMod IB W ρ V) (Hh : Type) [AddCommGroup Hh] [Module ℤ_[ℓ] Hh]
    (cl : V.Z1 →ₗ[ℤ_[ℓ]] Hh) (Hf : Submodule ℤ_[ℓ] Hh) (M h : ι → ℕ) (H : ℕ),
    S.s = 1 → S.Rad → S.Decomp → W.P2 → W.P5 M h → InLattice W →
    (∀ i, M i ≤ M₀) → (∀ i, M i + h i ≤ H) → Fintype.card Δ = ℓ - 1 → DeltaRing IB → B.GammaQ →
    (∀ a : A, (∀ d : Δ, d • (S.π * a) = S.π * a) →
      ∃ a' : A, (∀ d : Δ, d • a' = a') ∧ S.π * a = IB.j B.X * a') →
    J.Compat → ExtInputNL J cl Hf M h → ExtInputNA IB W V cl Hf M h

def ResNat {O A A₀ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing A₀]
    [Algebra O A₀] {S : HidaSetting O A} {B : Base O A₀} {Δ : Type} [Group Δ] [Fintype Δ]
    [MulSemiringAction Δ A] {IB : InvBase S B Δ} {ι : Type} {pr : Equiv.Perm ι} {D : Type}
    [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D] {W : NData S ι pr D}
    {ρ : ι → Δ →* Module.End O D} {M₀ : ℕ} {D' : Type} [AddCommGroup D'] [Module A₀ D']
    [Module O D'] [IsScalarTower O A₀ D'] {V : WachMod B M₀ D'} (J : InvMod IB W ρ V)
    (VB : WachMod S.base M₀ (ι → D)) {Hh HB : Type} [AddCommGroup Hh] [Module O Hh]
    [AddCommGroup HB] [Module O HB] (cl : V.Z1 →ₗ[O] Hh) (clB : VB.Z1 →ₗ[O] HB)
    (res : Hh →ₗ[O] HB) : Prop :=
  ∀ (p : V.Z1) (q : VB.Z1),
    (q : (ι → D) × (ι → D)) = (J.j (p : D' × D').1, J.j (p : D' × D').2) → res (cl p) = clB q

def StatHerrInjA : Prop :=
  ∀ (O A A₀ : Type) [CommRing O] [CommRing A] [Algebra O A] [CommRing A₀] [Algebra O A₀]
    (S : HidaSetting O A) (B : Base O A₀) (Δ : Type) [Group Δ] [Fintype Δ] [MulSemiringAction Δ A]
    (IB : InvBase S B Δ) (ι : Type) (pr : Equiv.Perm ι) (D : Type) [AddCommGroup D] [Module A D]
    [Module O D] [IsScalarTower O A D] (W : NData S ι pr D) (ρ : ι → Δ →* Module.End O D)
    (M₀ : ℕ) (D' : Type) [AddCommGroup D'] [Module A₀ D'] [Module O D'] [IsScalarTower O A₀ D']
    (V : WachMod B M₀ D') (J : InvMod IB W ρ V) (VB : WachMod S.base M₀ (ι → D))
    (Hh HB : Type) [AddCommGroup Hh] [Module O Hh] [AddCommGroup HB] [Module O HB]
    (cl : V.Z1 →ₗ[O] Hh) (clB : VB.Z1 →ₗ[O] HB) (res : Hh →ₗ[O] HB),
    S.s = 1 → DeltaRing IB → IsUnit ((Fintype.card Δ : ℕ) : O) → J.Compat → IsProd VB W →
    (∀ i d x, W.φ i (ρ (pr i) d x) = ρ i d (W.φ i x)) →
    (∀ i d x, W.γ i (ρ i d x) = ρ i d (W.γ i x)) →
    (∀ i d, ∀ x ∈ W.N i, ρ i d x ∈ W.N i) →
    ResNat J VB cl clB res → HerrInj VB clB → HerrInj V cl

def StatHerrInjK : Prop :=
  ∀ (O A A₀ : Type) [CommRing O] [CommRing A] [Algebra O A] [CommRing A₀] [Algebra O A₀]
    (S : HidaSetting O A) (B : Base O A₀) (Δ : Type) [Group Δ] [Fintype Δ] [MulSemiringAction Δ A]
    (IB : InvBase S B Δ) (ι : Type) [Finite ι] (pr : Equiv.Perm ι) (D : Type) [AddCommGroup D]
    [Module A D] [Module O D] [IsScalarTower O A D] (W : NData S ι pr D)
    (ρ : ι → Δ →* Module.End O D) (M h : ι → ℕ) (M₀ h₀ : ℕ) (D' : Type) [AddCommGroup D']
    [Module A₀ D'] [Module O D'] [IsScalarTower O A₀ D'] (V : WachMod B M₀ D')
    (J : InvMod IB W ρ V) (Hh : Type) [AddCommGroup Hh] [Module O Hh] (cl : V.Z1 →ₗ[O] Hh),
    S.s = 1 → S.Rad → DeltaRing IB → J.Compat → W.P2 → W.P5 M h → (∀ i, M i ≤ M₀) →
    (∀ i, h i ≤ h₀) → S.base.GammaModX → InLattice W → FreeN W →
    (∀ p : V.Z1, cl p = 0 → (p : D' × D') ∈ V.B1) →
    (∀ V' : WachMod (S.prodBase ι pr) M₀ (ι → D), IsProdP V' W → CoboundaryRealisedByExtension V' (fun _ : ι => S.π)) →
    HerrInj V cl

def LiftCaseAOddPrime : Prop :=
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
    ∃ (V₀ : WachMod B M₀ D₀') (V₁ : WachMod B M₀ D₁') (V₂ : WachMod B M₀ D₂') (Sq : SES V₀ V₁ V₂)
      (J₀ : InvMod IB W₀ ρ₀ V₀) (J₁ : InvMod IB W₁ ρ₁ V₁) (J₂ : InvMod IB W₂ ρ₂ V₂),
      (J₀.j = j₀ ∧ V₀.φ = φ₀ ∧ V₀.γ = γ₀) ∧ (J₁.j = j₁ ∧ V₁.φ = φ₁ ∧ V₁.γ = γ₁) ∧
      (J₂.j = j₂ ∧ V₂.φ = φ₂ ∧ V₂.γ = γ₂) ∧
      (∀ x i, J₁.j (Sq.ι.f x) i = E.ι.f i (J₀.j x i)) ∧
      (∀ x i, J₂.j (Sq.π.f x) i = E.π.f i (J₁.j x i)) ∧
      ∀ (δ : D₀' →ₗ[ℤ_[ℓ]] D₀')
        (R P ρ κ : Type) [CommRing R] [Algebra ℤ_[ℓ] R] [AddCommGroup P] [Module R P]
        [Module ℤ_[ℓ] P] [IsScalarTower ℤ_[ℓ] R P] [Fintype κ]
        (L : P4 (O := ℤ_[ℓ]) (A := A₀) Unit D₀' R P ρ κ)
        (H₁ H₂ : Type) [AddCommGroup H₁] [Module ℤ_[ℓ] H₁] [AddCommGroup H₂] [Module ℤ_[ℓ] H₂]
        (cl₁ : V₁.Z1 →ₗ[ℤ_[ℓ]] H₁) (cl₂ : V₂.Z1 →ₗ[ℤ_[ℓ]] H₂) (Hf₁ : Submodule ℤ_[ℓ] H₁)
        (Hf₂ : Submodule ℤ_[ℓ] H₂) (g : H₁ →ₗ[ℤ_[ℓ]] H₂)
        [IsAdicComplete (Ideal.span {(ℓ : A₀), B.X}) V₀.N],
        (∀ y, B.X • δ y = V₀.γ y - y) →
        L.HoldsA V₀ u (-(ℓ : ℤ_[ℓ])) → (∀ x k, L.a x k ∈ jumps) →
        ClNat Sq.π cl₁ cl₂ g → CocHf V₁ cl₁ Hf₁ → CocHf V₂ cl₂ Hf₂ → HerrInj V₂ cl₂ →
        ExtInputNL J₁ cl₁ Hf₁ M h → ExtInputNL J₂ cl₂ Hf₂ M h → RatOnto g Hf₁ Hf₂ →
        ∀ κ' ∈ Hf₂, ∃ κ₁ ∈ Hf₁,
          g κ₁ = ((ℓ : ℤ_[ℓ]) ^ (2 * eWA ℓ H + eUA ℓ M₀ (JSet jumps M₀))) • κ'

def LiftCaseAHerrSources : Prop :=
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
    ∃ (V₀ : WachMod B M₀ D₀') (V₁ : WachMod B M₀ D₁') (V₂ : WachMod B M₀ D₂') (Sq : SES V₀ V₁ V₂)
      (J₀ : InvMod IB W₀ ρ₀ V₀) (J₁ : InvMod IB W₁ ρ₁ V₁) (J₂ : InvMod IB W₂ ρ₂ V₂),
      (J₀.j = j₀ ∧ V₀.φ = φ₀ ∧ V₀.γ = γ₀) ∧ (J₁.j = j₁ ∧ V₁.φ = φ₁ ∧ V₁.γ = γ₁) ∧
      (J₂.j = j₂ ∧ V₂.φ = φ₂ ∧ V₂.γ = γ₂) ∧
      (∀ x i, J₁.j (Sq.ι.f x) i = E.ι.f i (J₀.j x i)) ∧
      (∀ x i, J₂.j (Sq.π.f x) i = E.π.f i (J₁.j x i)) ∧
      ∀ (δ : D₀' →ₗ[ℤ_[ℓ]] D₀')
        (R P ρ κ : Type) [CommRing R] [Algebra ℤ_[ℓ] R] [AddCommGroup P] [Module R P]
        [Module ℤ_[ℓ] P] [IsScalarTower ℤ_[ℓ] R P] [Fintype κ]
        (L : P4 (O := ℤ_[ℓ]) (A := A₀) Unit D₀' R P ρ κ)
        (H₁ H₂ : Type) [AddCommGroup H₁] [Module ℤ_[ℓ] H₁] [AddCommGroup H₂] [Module ℤ_[ℓ] H₂]
        (cl₁ : V₁.Z1 →ₗ[ℤ_[ℓ]] H₁) (cl₂ : V₂.Z1 →ₗ[ℤ_[ℓ]] H₂) (Hf₁ : Submodule ℤ_[ℓ] H₁)
        (Hf₂ : Submodule ℤ_[ℓ] H₂) (g : H₁ →ₗ[ℤ_[ℓ]] H₂)
        (VB : WachMod S.base M₀ (ι → D₂)) (HB : Type) [AddCommGroup HB] [Module ℤ_[ℓ] HB]
        (clB : VB.Z1 →ₗ[ℤ_[ℓ]] HB) (res : H₂ →ₗ[ℤ_[ℓ]] HB)
        [IsAdicComplete (Ideal.span {(ℓ : A₀), B.X}) V₀.N],
        (∀ y, B.X • δ y = V₀.γ y - y) →
        L.HoldsA V₀ u (-(ℓ : ℤ_[ℓ])) → (∀ x k, L.a x k ∈ jumps) →
        ClNat Sq.π cl₁ cl₂ g → CocHf V₁ cl₁ Hf₁ → CocHf V₂ cl₂ Hf₂ →
        IsProd VB W₂ → ResNat J₂ VB cl₂ clB res →
        (∀ p : VB.Z1, clB p = 0 → (p : (ι → D₂) × (ι → D₂)) ∈ VB.B1) →
        (∀ V' : WachMod (S.prodBase ι pr) M₀ (ι → D₂), IsProdP V' W₂ →
          CoboundaryRealisedByExtension V' (fun _ : ι => S.π)) →
        ExtInputNL J₁ cl₁ Hf₁ M h → ExtInputNL J₂ cl₂ Hf₂ M h → RatOnto g Hf₁ Hf₂ →
        ∀ κ' ∈ Hf₂, ∃ κ₁ ∈ Hf₁,
          g κ₁ = ((ℓ : ℤ_[ℓ]) ^ (2 * eWA ℓ H + eUA ℓ M₀ (JSet jumps M₀))) • κ'

def LiftCaseAHerrSourcesAlt : Prop :=
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
    ∃ (V₀ : WachMod B M₀ D₀') (V₁ : WachMod B M₀ D₁') (V₂ : WachMod B M₀ D₂') (Sq : SES V₀ V₁ V₂)
      (J₀ : InvMod IB W₀ ρ₀ V₀) (J₁ : InvMod IB W₁ ρ₁ V₁) (J₂ : InvMod IB W₂ ρ₂ V₂),
      (J₀.j = j₀ ∧ V₀.φ = φ₀ ∧ V₀.γ = γ₀) ∧ (J₁.j = j₁ ∧ V₁.φ = φ₁ ∧ V₁.γ = γ₁) ∧
      (J₂.j = j₂ ∧ V₂.φ = φ₂ ∧ V₂.γ = γ₂) ∧
      (∀ x i, J₁.j (Sq.ι.f x) i = E.ι.f i (J₀.j x i)) ∧
      (∀ x i, J₂.j (Sq.π.f x) i = E.π.f i (J₁.j x i)) ∧
      ∀ (δ : D₀' →ₗ[ℤ_[ℓ]] D₀')
        (R P ρ κ : Type) [CommRing R] [Algebra ℤ_[ℓ] R] [AddCommGroup P] [Module R P]
        [Module ℤ_[ℓ] P] [IsScalarTower ℤ_[ℓ] R P] [Fintype κ]
        (L : P4 (O := ℤ_[ℓ]) (A := A₀) Unit D₀' R P ρ κ)
        (H₁ H₂ : Type) [AddCommGroup H₁] [Module ℤ_[ℓ] H₁] [AddCommGroup H₂] [Module ℤ_[ℓ] H₂]
        (cl₁ : V₁.Z1 →ₗ[ℤ_[ℓ]] H₁) (cl₂ : V₂.Z1 →ₗ[ℤ_[ℓ]] H₂) (Hf₁ : Submodule ℤ_[ℓ] H₁)
        (Hf₂ : Submodule ℤ_[ℓ] H₂) (g : H₁ →ₗ[ℤ_[ℓ]] H₂)
        [IsAdicComplete (Ideal.span {(ℓ : A₀), B.X}) V₀.N],
        (∀ y, B.X • δ y = V₀.γ y - y) →
        L.HoldsA V₀ u (-(ℓ : ℤ_[ℓ])) → (∀ x k, L.a x k ∈ jumps) →
        ClNat Sq.π cl₁ cl₂ g → CocHf V₁ cl₁ Hf₁ → CocHf V₂ cl₂ Hf₂ →
        (∀ p : V₂.Z1, cl₂ p = 0 → (p : D₂' × D₂') ∈ V₂.B1) →
        (∀ V' : WachMod (S.prodBase ι pr) M₀ (ι → D₂), IsProdP V' W₂ →
          CoboundaryRealisedByExtension V' (fun _ : ι => S.π)) →
        ExtInputNL J₁ cl₁ Hf₁ M h → ExtInputNL J₂ cl₂ Hf₂ M h → RatOnto g Hf₁ Hf₂ →
        ∀ κ' ∈ Hf₂, ∃ κ₁ ∈ Hf₁,
          g κ₁ = ((ℓ : ℤ_[ℓ]) ^ (2 * eWA ℓ H + eUA ℓ M₀ (JSet jumps M₀))) • κ'

end Formalism.RepresentationBoundsCohomology.JN
