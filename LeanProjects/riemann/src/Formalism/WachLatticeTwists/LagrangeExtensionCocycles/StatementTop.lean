import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.Statement

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N2

open Polynomial Formalism.CoboundaryTransfers

def eigSet (jumps : Finset ℤ) (M : ℕ) : Finset ℤ :=
  (jumps ×ˢ Finset.Icc (1 : ℤ) M).image fun p => p.1 + p.2

def JSet (jumps : Finset ℤ) (M : ℕ) : Finset ℤ :=
  (eigSet jumps M).erase 0 ∪ Finset.Icc (1 : ℤ) M

def eUB (ℓ M s : ℕ) (J : Finset ℤ) : ℕ :=
  (∑ j ∈ J, (s + padicValInt ℓ j)) + M * s + padicValNat ℓ M.factorial

def aStar (ℓ M : ℕ) : ℕ := M / (ℓ - 1) + 1

def eUA (ℓ M : ℕ) (J : Finset ℤ) : ℕ :=
  (∑ j ∈ J, padicValInt ℓ j) + aStar ℓ M + padicValNat ℓ (aStar ℓ M).factorial

section Inputs

variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A] {B : Base ℤ_[ℓ] A} {M : ℕ}
  {D D' : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]
  [AddCommGroup D'] [Module A D'] [Module ℤ_[ℓ] D'] [IsScalarTower ℤ_[ℓ] A D']
  {H H' : Type} [AddCommGroup H] [Module ℤ_[ℓ] H] [AddCommGroup H'] [Module ℤ_[ℓ] H']

def XKills {W : WachMod B M D} {W' : WachMod B M D'} (F : Hom W W') (a : ℕ) : Prop :=
  ∀ n ∈ W'.N, ∃ n₁ ∈ W.N, F.f n₁ = B.X ^ a • n

def RegXQ (W : WachMod B M D) : Prop :=
  ∀ n ∈ W.N, (∃ m ∈ W.N, B.Q • n = B.X • m) → ∃ m ∈ W.N, n = B.X • m

def RegLQ (W : WachMod B M D) : Prop :=
  ∀ n ∈ W.N, (∃ m ∈ W.N, B.Q • n = (ℓ : ℤ_[ℓ]) • m) → ∃ m ∈ W.N, n = (ℓ : ℤ_[ℓ]) • m

def NoTors (ℓ : ℕ) [Fact ℓ.Prime] (D : Type) [AddCommGroup D] [Module ℤ_[ℓ] D] : Prop :=
  ∀ x : D, (ℓ : ℤ_[ℓ]) • x = 0 → x = 0

def SemiB (W : WachMod B M D) (u : ℤ_[ℓ]ˣ) (jumps : Finset ℤ) : Prop :=
  ∀ y, W.QInv y →
    aeval W.γ (∏ j ∈ eigSet jumps M, (X - C (((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])))) y ∈ W.N

def SemiA (W : WachMod B M D) (δ : D →ₗ[ℤ_[ℓ]] D) (c : ℤ → ℤ_[ℓ]) (jumps : Finset ℤ) : Prop :=
  ∀ y, W.QInv y → aeval δ (∏ j ∈ eigSet jumps M, (X - C (c j))) y ∈ W.N

def CocHf (W : WachMod B M D) (cl : W.Z1 →ₗ[ℤ_[ℓ]] H) (Hf : Submodule ℤ_[ℓ] H) : Prop :=
  ∀ pr : W.Z1, W.Cocycle (pr : D × D).1 (pr : D × D).2 → cl pr ∈ Hf

def RatOnto (g : H →ₗ[ℤ_[ℓ]] H') (Hf : Submodule ℤ_[ℓ] H) (Hf' : Submodule ℤ_[ℓ] H') : Prop :=
  ∀ κ ∈ Hf', ∃ k : ℕ, ∃ κ₁ ∈ Hf, g κ₁ = ((ℓ : ℤ_[ℓ]) ^ k) • κ

structure ExtDatum (W : WachMod B M D) where
  Dp : Type
  Dt : Type
  [gp : AddCommGroup Dp]
  [mp : Module A Dp]
  [zp : Module ℤ_[ℓ] Dp]
  [tp : IsScalarTower ℤ_[ℓ] A Dp]
  [gt : AddCommGroup Dt]
  [mt : Module A Dt]
  [zt : Module ℤ_[ℓ] Dt]
  [tt : IsScalarTower ℤ_[ℓ] A Dt]
  Wp : WachMod B M Dp
  Wt : WachMod B M Dt
  S : SES W Wp Wt
  e : Dt
  e_mem : e ∈ Wt.N
  φe : Wt.φ e = e
  γe : Wt.γ e = e

attribute [instance] ExtDatum.gp ExtDatum.mp ExtDatum.zp ExtDatum.tp ExtDatum.gt ExtDatum.mt
  ExtDatum.zt ExtDatum.tt

def ExtDatum.Dict {W : WachMod B M D} (E : ExtDatum W) (cl : W.Z1 →ₗ[ℤ_[ℓ]] H) (κ : H) : Prop :=
  ∀ (c : ℤ_[ℓ]) (x : E.Dp) (pr : W.Z1), E.S.π.f x = c • E.e →
    E.S.ι.f (pr : D × D).1 = E.Wp.φ x - x → E.S.ι.f (pr : D × D).2 = E.Wp.γ x - x →
    cl pr = c • κ

def ExtInput (W : WachMod B M D) (cl : W.Z1 →ₗ[ℤ_[ℓ]] H) (Hf : Submodule ℤ_[ℓ] H) (a : ℕ) : Prop :=
  ∀ κ ∈ Hf, ∃ E : ExtDatum W, XKills E.S.π a ∧ E.Dict cl κ

end Inputs

def StatPhiOnto : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (B : Base O A) (M : ℕ)
    (D : Type) [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
    (W : WachMod B M D) (I : Ideal A) [IsAdicComplete I W.N] (k b : ℕ),
    B.PhiX k → M + 1 ≤ k * b → B.Q ∈ I → (∀ a ∈ I, B.φ a ∈ I) →
    ∀ n ∈ W.N, ∃ z ∈ W.N, B.X ^ b • n = B.X ^ b • z - W.φ (B.X ^ b • z)

def StatRegX : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] (B : Base ℤ_[ℓ] A) (M : ℕ)
    (D : Type) [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]
    (W : WachMod B M D), RegXQ W → ∀ y, W.QInv y → B.X • y ∈ W.N → y ∈ W.N

def StatRegL : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] (B : Base ℤ_[ℓ] A) (M : ℕ)
    (D : Type) [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]
    (W : WachMod B M D), RegLQ W → NoTors ℓ D → ∀ y, W.QInv y → (ℓ : ℤ_[ℓ]) • y ∈ W.N → y ∈ W.N

def StatExtCocycle : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] (B : Base ℤ_[ℓ] A) (M : ℕ)
    (D : Type) [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]
    (W : WachMod B M D) (H : Type) [AddCommGroup H] [Module ℤ_[ℓ] H] (cl : W.Z1 →ₗ[ℤ_[ℓ]] H)
    (κ : H) (E : ExtDatum W) (e : ℕ), E.Dict cl κ →
    (∀ n ∈ E.Wt.N, ∃ n₁ ∈ E.Wp.N, E.S.π.f n₁ = ((ℓ : ℤ_[ℓ]) ^ e) • n) →
    ∃ pr : W.Z1, W.Cocycle (pr : D × D).1 (pr : D × D).2 ∧ cl pr = ((ℓ : ℤ_[ℓ]) ^ e) • κ

def StatRatSurj : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] (B : Base ℤ_[ℓ] A) (M : ℕ)
    (D₀ D₁ D₂ : Type)
    [AddCommGroup D₀] [Module A D₀] [Module ℤ_[ℓ] D₀] [IsScalarTower ℤ_[ℓ] A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module ℤ_[ℓ] D₁] [IsScalarTower ℤ_[ℓ] A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module ℤ_[ℓ] D₂] [IsScalarTower ℤ_[ℓ] A D₂]
    (W₀ : WachMod B M D₀) (W₁ : WachMod B M D₁) (W₂ : WachMod B M D₂) (S : SES W₀ W₁ W₂)
    (H₁ H₂ : Type) [AddCommGroup H₁] [Module ℤ_[ℓ] H₁] [AddCommGroup H₂] [Module ℤ_[ℓ] H₂]
    (cl₁ : W₁.Z1 →ₗ[ℤ_[ℓ]] H₁) (cl₂ : W₂.Z1 →ₗ[ℤ_[ℓ]] H₂) (Hf₁ : Submodule ℤ_[ℓ] H₁)
    (Hf₂ : Submodule ℤ_[ℓ] H₂) (g : H₁ →ₗ[ℤ_[ℓ]] H₂) (e₁ : ℕ),
    B.p = ℓ → ClNat S.π cl₁ cl₂ g → CocHf W₂ cl₂ Hf₂ → HerrInj W₂ cl₂ → RatOnto g Hf₁ Hf₂ →
    (∀ κ ∈ Hf₁, ∃ pr : W₁.Z1, W₁.Cocycle (pr : D₁ × D₁).1 (pr : D₁ × D₁).2 ∧
      cl₁ pr = ((ℓ : ℤ_[ℓ]) ^ e₁) • κ) →
    RatSurj S

def StatLiftB : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] (B : Base ℤ_[ℓ] A) (M : ℕ)
    (u : ℤ_[ℓ]ˣ) (s H : ℕ) (jumps : Finset ℤ),
    B.p = ℓ → B.φ B.X = B.X * B.Q → B.GammaX (u : ℤ_[ℓ]) → B.GammaQ →
    1 ≤ s → (ℓ = 2 → 2 ≤ s) → PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = s →
    ∀ (D₀ D₁ D₂ : Type)
    [AddCommGroup D₀] [Module A D₀] [Module ℤ_[ℓ] D₀] [IsScalarTower ℤ_[ℓ] A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module ℤ_[ℓ] D₁] [IsScalarTower ℤ_[ℓ] A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module ℤ_[ℓ] D₂] [IsScalarTower ℤ_[ℓ] A D₂]
    (W₀ : WachMod B M D₀) (W₁ : WachMod B M D₁) (W₂ : WachMod B M D₂) (S : SES W₀ W₁ W₂)
    (H₁ H₂ : Type) [AddCommGroup H₁] [Module ℤ_[ℓ] H₁] [AddCommGroup H₂] [Module ℤ_[ℓ] H₂]
    (cl₁ : W₁.Z1 →ₗ[ℤ_[ℓ]] H₁) (cl₂ : W₂.Z1 →ₗ[ℤ_[ℓ]] H₂) (Hf₁ : Submodule ℤ_[ℓ] H₁)
    (Hf₂ : Submodule ℤ_[ℓ] H₂) (g : H₁ →ₗ[ℤ_[ℓ]] H₂) (I : Ideal A) [IsAdicComplete I W₀.N],
    B.Q ∈ I → (∀ a ∈ I, B.φ a ∈ I) → RegXQ W₀ → RegLQ W₀ → NoTors ℓ D₀ →
    XKills S.π H → SemiB W₀ u jumps →
    ClNat S.π cl₁ cl₂ g → CocHf W₁ cl₁ Hf₁ → CocHf W₂ cl₂ Hf₂ → HerrInj W₂ cl₂ →
    ExtInput W₁ cl₁ Hf₁ H → ExtInput W₂ cl₂ Hf₂ H → RatOnto g Hf₁ Hf₂ →
    ∀ κ ∈ Hf₂, ∃ κ₁ ∈ Hf₁,
      g κ₁ = ((ℓ : ℤ_[ℓ]) ^ (2 * eWB ℓ H s + eUB ℓ M s (JSet jumps M))) • κ

def StatLiftA : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ 2 → ∀ (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A]
    (B : Base ℤ_[ℓ] A) (M : ℕ) (u : ℤ_[ℓ]ˣ) (H : ℕ) (jumps : Finset ℤ) (c : ℤ → ℤ_[ℓ]),
    B.p = ℓ → B.PhiX (ℓ - 1) → B.GammaX ((u : ℤ_[ℓ]) ^ (ℓ - 1)) →
    PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = 1 →
    (∀ j : ℤ, (ℓ : ℤ_[ℓ]) * c j = 1 - ((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) →
    ∀ (D₀ D₁ D₂ : Type)
    [AddCommGroup D₀] [Module A D₀] [Module ℤ_[ℓ] D₀] [IsScalarTower ℤ_[ℓ] A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module ℤ_[ℓ] D₁] [IsScalarTower ℤ_[ℓ] A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module ℤ_[ℓ] D₂] [IsScalarTower ℤ_[ℓ] A D₂]
    (W₀ : WachMod B M D₀) (W₁ : WachMod B M D₁) (W₂ : WachMod B M D₂) (S : SES W₀ W₁ W₂)
    (δ : D₀ →ₗ[ℤ_[ℓ]] D₀)
    (H₁ H₂ : Type) [AddCommGroup H₁] [Module ℤ_[ℓ] H₁] [AddCommGroup H₂] [Module ℤ_[ℓ] H₂]
    (cl₁ : W₁.Z1 →ₗ[ℤ_[ℓ]] H₁) (cl₂ : W₂.Z1 →ₗ[ℤ_[ℓ]] H₂) (Hf₁ : Submodule ℤ_[ℓ] H₁)
    (Hf₂ : Submodule ℤ_[ℓ] H₂) (g : H₁ →ₗ[ℤ_[ℓ]] H₂) (I : Ideal A) [IsAdicComplete I W₀.N],
    (∀ y, B.X • δ y = W₀.γ y - y) →
    B.Q ∈ I → (∀ a ∈ I, B.φ a ∈ I) → RegLQ W₀ → NoTors ℓ D₀ →
    XKills S.π ((H + (ℓ - 2)) / (ℓ - 1)) → SemiA W₀ δ c jumps →
    ClNat S.π cl₁ cl₂ g → CocHf W₁ cl₁ Hf₁ → CocHf W₂ cl₂ Hf₂ → HerrInj W₂ cl₂ →
    ExtInput W₁ cl₁ Hf₁ ((H + (ℓ - 2)) / (ℓ - 1)) →
    ExtInput W₂ cl₂ Hf₂ ((H + (ℓ - 2)) / (ℓ - 1)) → RatOnto g Hf₁ Hf₂ →
    ∀ κ ∈ Hf₂, ∃ κ₁ ∈ Hf₁,
      g κ₁ = ((ℓ : ℤ_[ℓ]) ^ (2 * eWA ℓ H + eUA ℓ M (JSet jumps M))) • κ

def StatLiftSub : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (H₁ H₂ H₁' H₂' : Type)
    [AddCommGroup H₁] [Module ℤ_[ℓ] H₁] [AddCommGroup H₂] [Module ℤ_[ℓ] H₂]
    [AddCommGroup H₁'] [Module ℤ_[ℓ] H₁'] [AddCommGroup H₂'] [Module ℤ_[ℓ] H₂']
    (Hf₁ : Submodule ℤ_[ℓ] H₁) (Hf₂ : Submodule ℤ_[ℓ] H₂) (Hf₁' : Submodule ℤ_[ℓ] H₁')
    (Hf₂' : Submodule ℤ_[ℓ] H₂')
    (h : H₁ →ₗ[ℤ_[ℓ]] H₂) (h' : H₁' →ₗ[ℤ_[ℓ]] H₂') (res₂ : H₂' →ₗ[ℤ_[ℓ]] H₂)
    (cor₁ : H₁ →ₗ[ℤ_[ℓ]] H₁') (cor₂ : H₂ →ₗ[ℤ_[ℓ]] H₂') (g E : ℕ),
    0 < g →
    (∀ x, cor₂ (res₂ x) = (g : ℤ_[ℓ]) • x) →
    (∀ x, h' (cor₁ x) = cor₂ (h x)) →
    (∀ x ∈ Hf₂', res₂ x ∈ Hf₂) → (∀ x ∈ Hf₁, cor₁ x ∈ Hf₁') →
    (∀ κ ∈ Hf₂, ∃ κ₁ ∈ Hf₁, h κ₁ = ((ℓ : ℤ_[ℓ]) ^ E) • κ) →
    ∀ κ' ∈ Hf₂', ∃ κ₁' ∈ Hf₁', h' κ₁' = ((ℓ : ℤ_[ℓ]) ^ (E + padicValNat ℓ g)) • κ'

def StatLIFT : Prop := StatLiftB ∧ StatLiftA ∧ StatLiftSub

def StatSizeB : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (M h H s : ℕ) (jumps : Finset ℤ), 1 ≤ s → M + h ≤ H →
    (∀ a ∈ jumps, -(M : ℤ) ≤ a ∧ a ≤ h) →
    2 * eWB ℓ H s + eUB ℓ M s (JSet jumps M) ≤ 16 * H * s

def StatSizeA : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ 2 → ∀ (M h H : ℕ) (jumps : Finset ℤ), M + h ≤ H →
    (∀ a ∈ jumps, -(M : ℤ) ≤ a ∧ a ≤ h) →
    ((2 * eWA ℓ H + eUA ℓ M (JSet jumps M) : ℕ) : ℝ) ≤
      15 / 2 * (H : ℝ) / ((ℓ : ℝ) - 1) + 8 + 2 * Real.logb ℓ ((H : ℝ) + 1)

end Formalism.RepresentationBoundsCohomology.N2
