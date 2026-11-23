import Formalism.WachLatticeTwists.WachProductBases.StatementTop
import Formalism.WachLatticeTwists.WachProductBases.NontrivialWachExample
import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.StatementTop

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JN

open Formalism.CoboundaryTransfers Formalism.RepresentationBoundsCohomology.N1 Formalism.RepresentationBoundsCohomology.N2

def mI {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (S : HidaSetting O A) : Ideal A :=
  Ideal.span {(S.ℓ : A), S.π}

def StatBaseB : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] (S : HidaSetting ℤ_[ℓ] A),
    S.ℓ = ℓ →
    S.base.p = ℓ ∧ S.base.φ S.base.X = S.base.X * S.base.Q ∧ S.base.GammaX S.u ∧
    (S.Rad → S.base.GammaQ) ∧ 1 ≤ S.s ∧ (ℓ = 2 → 2 ≤ S.s) ∧
    IsUnit S.u ∧ (IsUnit S.c₀ → PadicInt.valuation (S.u - 1) = S.s) ∧
    S.base.Q ∈ mI S ∧ (∀ a ∈ mI S, S.base.φ a ∈ mI S)

section Lattice

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {S : HidaSetting O A} {ι : Type}
  {pr : Equiv.Perm ι} {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]

def IsProd {M₀ : ℕ} (V : WachMod S.base M₀ (ι → D)) (W : NData S ι pr D) : Prop :=
  V.N = Submodule.pi Set.univ W.N ∧ (∀ x i, V.φ x i = W.φ i (x (pr i))) ∧
    (∀ x i, V.γ x i = W.γ i (x i))

def RegXQN (W : NData S ι pr D) : Prop :=
  ∀ i, ∀ n ∈ W.N i, (∃ m ∈ W.N i, S.Q • n = S.X • m) → ∃ m ∈ W.N i, n = S.X • m

end Lattice

def StatLattice : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] (S : HidaSetting ℤ_[ℓ] A)
    (ι : Type) (pr : Equiv.Perm ι) (D : Type) [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D]
    [IsScalarTower ℤ_[ℓ] A D] (W : NData S ι pr D) (M₀ : ℕ) (V : WachMod S.base M₀ (ι → D)),
    S.ℓ = ℓ → IsProd V W →
    (InLattice W → RegLQ V) ∧ (RegXQN W → RegXQ V) ∧ (NoTors ℓ D → NoTors ℓ (ι → D))

structure P4 {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (ι D R P ρ κ : Type)
    [AddCommGroup D] [Module O D] [CommRing R] [Algebra O R] [AddCommGroup P] [Module O P] where
  lt : ρ → ι
  t : R
  γR : R →ₐ[O] R
  locA : ρ → A →+* R
  loc : ρ → D →ₗ[O] P
  γl : ρ → P →ₗ[O] P
  n : ρ → κ → P
  a : ρ → κ → ℤ

section P4

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {S : HidaSetting O A} {ι : Type}
  {pr : Equiv.Perm ι} {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
  {R P ρ κ : Type} [CommRing R] [Algebra O R] [AddCommGroup P] [Module R P] [Module O P]
  [IsScalarTower O R P]

def P4.Holds (L : P4 (O := O) (A := A) ι D R P ρ κ) (W : NData S ι pr D) (u : Oˣ) : Prop :=
  L.γR L.t = (u : O) • L.t ∧
  (∀ r : R, ∃ r' : R, L.γR r - r = L.t * r') ∧
  Function.Bijective (fun v : P => L.t • v) ∧
  (∀ x (r : R) (v : P), L.γl x (r • v) = L.γR r • L.γl x v) ∧
  (∀ x (b : A) (d : D), (∃ k : ℕ, S.Q ^ k • d ∈ W.N (L.lt x)) →
    L.loc x (b • d) = L.locA x b • L.loc x d) ∧
  (∀ x d, (∃ k : ℕ, S.Q ^ k • d ∈ W.N (L.lt x)) →
    L.loc x (W.γ (L.lt x) d) = L.γl x (L.loc x d)) ∧
  (∀ x, ∃ v : R, IsUnit v ∧ L.locA x S.Q = v * L.t) ∧
  (∀ x, ∀ d ∈ W.N (L.lt x), L.loc x d ∈ Submodule.span R (Set.range (L.n x))) ∧
  (∀ x k, L.γl x (L.n x k) = ((u ^ (-L.a x k) : Oˣ) : O) • L.n x k)

def P4.Test (L : P4 (O := O) (A := A) ι D R P ρ κ) (W : NData S ι pr D) : Prop :=
  ∀ i d, (∃ k : ℕ, S.Q ^ k • d ∈ W.N i) →
    (∀ x, L.lt x = i → L.loc x d ∈ Submodule.span R (Set.range (L.n x))) → d ∈ W.N i

end P4

def StatSemiB : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] (S : HidaSetting ℤ_[ℓ] A)
    (ι : Type) (pr : Equiv.Perm ι) (D : Type) [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D]
    [IsScalarTower ℤ_[ℓ] A D] (W : NData S ι pr D) (M₀ : ℕ) (V : WachMod S.base M₀ (ι → D))
    (R P ρ κ : Type) [CommRing R] [Algebra ℤ_[ℓ] R] [AddCommGroup P] [Module R P] [Module ℤ_[ℓ] P]
    [IsScalarTower ℤ_[ℓ] R P] [Fintype κ] (L : P4 (O := ℤ_[ℓ]) (A := A) ι D R P ρ κ) (u : ℤ_[ℓ]ˣ)
    (jumps : Finset ℤ),
    S.Rad → IsProd V W → L.Holds W u → L.Test W → (∀ x k, L.a x k ∈ jumps) →
    SemiB V u jumps

def StatSES : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (S : HidaSetting O A) (ι : Type) [Finite ι]
    (pr : Equiv.Perm ι) (D₀ D₁ D₂ : Type)
    [AddCommGroup D₀] [Module A D₀] [Module O D₀] [IsScalarTower O A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module O D₁] [IsScalarTower O A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module O D₂] [IsScalarTower O A D₂]
    (W₀ : NData S ι pr D₀) (W₁ : NData S ι pr D₁) (W₂ : NData S ι pr D₂) (E : NSES W₀ W₁ W₂)
    (M h : ι → ℕ) (M₀ H : ℕ),
    S.Rad → S.Decomp →
    W₀.P2 → W₁.P2 → W₂.P2 → W₀.P5 M h → W₁.P5 M h → W₂.P5 M h →
    InLattice W₀ → InLattice W₁ → InLattice W₂ → LatticeSequenceExactUpToPrimePower E →
    (∀ i, M i ≤ M₀) → (∀ i, M i + h i ≤ H) →
    ∃ (V₀ : WachMod S.base M₀ (ι → D₀)) (V₁ : WachMod S.base M₀ (ι → D₁))
      (V₂ : WachMod S.base M₀ (ι → D₂)) (Sq : SES V₀ V₁ V₂),
      IsProd V₀ W₀ ∧ IsProd V₁ W₁ ∧ IsProd V₂ W₂ ∧
      (∀ x i, Sq.ι.f x i = E.ι.f i (x i)) ∧ (∀ x i, Sq.π.f x i = E.π.f i (x i)) ∧
      (∀ n ∈ V₂.N, ∃ n₁ ∈ V₁.N, Sq.π.f n₁ = S.base.X ^ H • n)

def StatProdUnique : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (S : HidaSetting O A) (ι : Type)
    (pr : Equiv.Perm ι) (D : Type) [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
    (W : NData S ι pr D) (M₀ : ℕ) (V V' : WachMod S.base M₀ (ι → D)),
    IsProd V W → IsProd V' W → V = V'

def ExtInputN {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A]
    {S : HidaSetting ℤ_[ℓ] A} {ι : Type} {pr : Equiv.Perm ι} {D : Type} [AddCommGroup D] [Module A D]
    [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D] {M₀ : ℕ} (V : WachMod S.base M₀ (ι → D))
    (W : NData S ι pr D) {Hh : Type} [AddCommGroup Hh] [Module ℤ_[ℓ] Hh]
    (cl : V.Z1 →ₗ[ℤ_[ℓ]] Hh) (Hf : Submodule ℤ_[ℓ] Hh) (M h : ι → ℕ) : Prop :=
  ∀ κ ∈ Hf, ∃ (Dp Dt : Type) (_ : AddCommGroup Dp) (_ : Module A Dp) (_ : Module ℤ_[ℓ] Dp)
    (_ : IsScalarTower ℤ_[ℓ] A Dp) (_ : AddCommGroup Dt) (_ : Module A Dt) (_ : Module ℤ_[ℓ] Dt)
    (_ : IsScalarTower ℤ_[ℓ] A Dt) (Wp : NData S ι pr Dp) (Wt : NData S ι pr Dt)
    (E : NSES W Wp Wt) (e : ι → Dt),
    Wp.P2 ∧ Wt.P2 ∧ Wp.P5 M h ∧ Wt.P5 M h ∧ InLattice Wp ∧ InLattice Wt ∧ LatticeSequenceExactUpToPrimePower E ∧
    (∀ i, e i ∈ Wt.N i) ∧ (∀ i, Wt.φ i (e (pr i)) = e i) ∧ (∀ i, Wt.γ i (e i) = e i) ∧
    ∀ (c : ℤ_[ℓ]) (x : ι → Dp) (p : V.Z1), (∀ i, E.π.f i (x i) = c • e i) →
      (∀ i, E.ι.f i ((p : (ι → D) × (ι → D)).1 i) = Wp.φ i (x (pr i)) - x i) →
      (∀ i, E.ι.f i ((p : (ι → D) × (ι → D)).2 i) = Wp.γ i (x i) - x i) →
      cl p = c • κ

def StatExt : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] (S : HidaSetting ℤ_[ℓ] A)
    (ι : Type) [Finite ι] (pr : Equiv.Perm ι) (D : Type) [AddCommGroup D] [Module A D]
    [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D] (W : NData S ι pr D) (M₀ : ℕ)
    (V : WachMod S.base M₀ (ι → D)) (Hh : Type) [AddCommGroup Hh] [Module ℤ_[ℓ] Hh]
    (cl : V.Z1 →ₗ[ℤ_[ℓ]] Hh) (Hf : Submodule ℤ_[ℓ] Hh) (M h : ι → ℕ) (H : ℕ),
    S.Rad → S.Decomp → IsProd V W → W.P2 → W.P5 M h → InLattice W →
    (∀ i, M i ≤ M₀) → (∀ i, M i + h i ≤ H) →
    ExtInputN V W cl Hf M h → ExtInput V cl Hf H

def StatCompB : Prop :=
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
    S.ℓ = ℓ → IsUnit S.c₀ → (u : ℤ_[ℓ]) = S.u → S.Rad → S.Decomp →
    W₀.P2 → W₁.P2 → W₂.P2 → W₀.P5 M h → W₁.P5 M h → W₂.P5 M h →
    InLattice W₀ → InLattice W₁ → InLattice W₂ → LatticeSequenceExactUpToPrimePower E →
    (∀ i, M i ≤ M₀) → (∀ i, M i + h i ≤ H) →
    RegXQN W₀ → NoTors ℓ D₀ →
    L.Holds W₀ u → L.Test W₀ → (∀ x k, L.a x k ∈ jumps) →
    ∃ (V₀ : WachMod S.base M₀ (ι → D₀)) (V₁ : WachMod S.base M₀ (ι → D₁))
      (V₂ : WachMod S.base M₀ (ι → D₂)) (Sq : SES V₀ V₁ V₂),
      IsProd V₀ W₀ ∧ IsProd V₁ W₁ ∧ IsProd V₂ W₂ ∧
      (∀ x i, Sq.ι.f x i = E.ι.f i (x i)) ∧ (∀ x i, Sq.π.f x i = E.π.f i (x i)) ∧
      ∀ (H₁ H₂ : Type) [AddCommGroup H₁] [Module ℤ_[ℓ] H₁] [AddCommGroup H₂] [Module ℤ_[ℓ] H₂]
        (cl₁ : V₁.Z1 →ₗ[ℤ_[ℓ]] H₁) (cl₂ : V₂.Z1 →ₗ[ℤ_[ℓ]] H₂) (Hf₁ : Submodule ℤ_[ℓ] H₁)
        (Hf₂ : Submodule ℤ_[ℓ] H₂) (g : H₁ →ₗ[ℤ_[ℓ]] H₂),
        ClNat Sq.π cl₁ cl₂ g → CocHf V₁ cl₁ Hf₁ → CocHf V₂ cl₂ Hf₂ → HerrInj V₂ cl₂ →
        ExtInputN V₁ W₁ cl₁ Hf₁ M h → ExtInputN V₂ W₂ cl₂ Hf₂ M h → RatOnto g Hf₁ Hf₂ →
        ∀ κ' ∈ Hf₂, ∃ κ₁ ∈ Hf₁,
          g κ₁ = ((ℓ : ℤ_[ℓ]) ^ (2 * eWB ℓ H S.s + eUB ℓ M₀ S.s (JSet jumps M₀))) • κ'

end Formalism.RepresentationBoundsCohomology.JN
