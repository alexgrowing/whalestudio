import Formalism.WachLatticeTwists.WachProductBases.Statement

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N1

def LocalValuationConsequence : Prop :=
  ∀ (L R : Type) [CommRing L] [CommRing R] [Algebra L R] (P : Type) [AddCommGroup P] [Module R P]
    [Module L P] [IsScalarTower L R P] (t π' r₀ : R) (u : Lˣ) (ϖ : L) (γR : R →ₐ[L] R)
    (γ d : P →ₗ[L] P) (κ : Type) [Fintype κ] (n : κ → P) (a : κ → ℤ) (c : ℤ → L) (y : ℕ)
    (Sx : Finset ℤ),
    γR t = (u : L) • t →
    (∀ (r : R) (x : P), γ (r • x) = γR r • γ x) →
    (∀ r : R, ∃ r' : R, γR r - r = t * r') →
    Function.Bijective (fun x : P => t • x) →
    IsUnit π' → π' = algebraMap L R (ϖ : L) + t * r₀ →
    (∀ x, π' • d x = γ x - x) →
    (∀ b, (ϖ : L) * c b = ((u ^ (-b) : Lˣ) : L) - 1) →
    (∀ k, γ (n k) = ((u ^ (-a k) : Lˣ) : L) • n k) →
    (∀ k, ∀ j ∈ Finset.Icc (1 : ℤ) y, a k + j ∈ Sx) →
    ∀ x : P, t ^ y • x ∈ Submodule.span R (Set.range n) →
      Polynomial.aeval d (∏ b ∈ Sx, (Polynomial.X - Polynomial.C (c b))) x ∈
        Submodule.span R (Set.range n)

def TriangularConsequence : Prop :=
  ∀ (L R : Type) [CommRing L] [CommRing R] [Algebra L R] (P : Type) [AddCommGroup P] [Module R P]
    [Module L P] [IsScalarTower L R P] (t : R) (u : Lˣ) (γR : R →ₐ[L] R) (γ : P →ₗ[L] P)
    (κ : Type) [Fintype κ] (n : κ → P) (a : κ → ℤ) (y : ℕ) (Sx : Finset ℤ),
    γR t = (u : L) • t →
    (∀ (r : R) (x : P), γ (r • x) = γR r • γ x) →
    (∀ r : R, ∃ r' : R, γR r - r = t * r') →
    Function.Bijective (fun x : P => t • x) →
    (∀ k, γ (n k) = ((u ^ (-a k) : Lˣ) : L) • n k) →
    (∀ k, ∀ j ∈ Finset.Icc (1 : ℤ) y, a k + j ∈ Sx) →
    ∀ x : P, t ^ y • x ∈ Submodule.span R (Set.range n) →
      Polynomial.aeval γ (∏ b ∈ Sx, (Polynomial.X - Polynomial.C (((u ^ (-b) : Lˣ) : L)))) x ∈
        Submodule.span R (Set.range n)

open Formalism.CoboundaryTransfers in

def TopDegreeTriangularConsequence : Prop :=
  ∀ (O A R : Type) [CommRing O] [CommRing A] [CommRing R] [Algebra O A] [Algebra O R]
    (B : Base O A) (M : ℕ) (D P : Type)
    [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
    [AddCommGroup P] [Module R P] [Module O P] [IsScalarTower O R P]
    (W : WachMod B M D) (u : Oˣ) (y : ℕ) (Sx : Finset ℤ) (ρ κ : Type) [Fintype κ]
    (t : R) (γR : R →ₐ[O] R) (locA : ρ → A →+* R) (loc : ρ → D →ₗ[O] P) (γl : ρ → P →ₗ[O] P)
    (n : ρ → κ → P) (a : ρ → κ → ℤ),
    B.GammaQ →
    γR t = (u : O) • t →
    (∀ r : R, ∃ r' : R, γR r - r = t * r') →
    Function.Bijective (fun v : P => t • v) →
    (∀ x (r : R) (v : P), γl x (r • v) = γR r • γl x v) →
    (∀ x (b : A) (d : D), (∃ k : ℕ, B.Q ^ k • d ∈ W.N) → loc x (b • d) = locA x b • loc x d) →
    (∀ x d, (∃ k : ℕ, B.Q ^ k • d ∈ W.N) → loc x (W.γ d) = γl x (loc x d)) →
    (∀ x, ∃ v : R, IsUnit v ∧ locA x B.Q = v * t) →
    (∀ x, ∀ d ∈ W.N, loc x d ∈ Submodule.span R (Set.range (n x))) →
    (∀ x k, γl x (n x k) = ((u ^ (-a x k) : Oˣ) : O) • n x k) →
    (∀ d, (∃ k : ℕ, B.Q ^ k • d ∈ W.N) →
      (∀ x, loc x d ∈ Submodule.span R (Set.range (n x))) → d ∈ W.N) →
    (∀ x k, ∀ j ∈ Finset.Icc (1 : ℤ) y, a x k + j ∈ Sx) →
    ∀ d, B.Q ^ y • d ∈ W.N →
      Polynomial.aeval W.γ (∏ b ∈ Sx, (Polynomial.X - Polynomial.C (((u ^ (-b) : Oˣ) : O)))) d ∈ W.N

open Formalism.CoboundaryTransfers in

def TopDegreeValuationConsequence : Prop :=
  ∀ (O A R : Type) [CommRing O] [CommRing A] [CommRing R] [Algebra O A] [Algebra O R]
    (B : Base O A) (M : ℕ) (D P : Type)
    [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
    [AddCommGroup P] [Module R P] [Module O P] [IsScalarTower O R P]
    (W : WachMod B M D) (dd : D →ₗ[O] D) (u : Oˣ) (y : ℕ)
    (ρ κ : Type) [Fintype ρ] [Fintype κ] (ϖ : ρ → O) (c : ρ → ℤ → O) (Sx : ρ → Finset ℤ)
    (t : R) (γR : R →ₐ[O] R) (locA : ρ → A →+* R) (loc : ρ → D →ₗ[O] P) (γl : ρ → P →ₗ[O] P)
    (n : ρ → κ → P) (a : ρ → κ → ℤ),
    B.GammaQ →
    (∀ v, B.X • dd v = W.γ v - v) →
    γR t = (u : O) • t →
    (∀ r : R, ∃ r' : R, γR r - r = t * r') →
    Function.Bijective (fun v : P => t • v) →
    (∀ x (r : R) (v : P), γl x (r • v) = γR r • γl x v) →
    (∀ x (b : A) (d : D), (∃ k : ℕ, B.Q ^ k • d ∈ W.N) → loc x (b • d) = locA x b • loc x d) →
    (∀ x d, (∃ k : ℕ, B.Q ^ k • d ∈ W.N) → loc x (W.γ d) = γl x (loc x d)) →
    (∀ x, ∃ v : R, IsUnit v ∧ locA x B.Q = v * t) →
    (∀ x, IsUnit (locA x B.X) ∧ ∃ r₀ : R, locA x B.X = algebraMap O R (ϖ x) + t * r₀) →
    (∀ x b, ϖ x * c x b = ((u ^ (-b) : Oˣ) : O) - 1) →
    (∀ x, ∀ d ∈ W.N, loc x d ∈ Submodule.span R (Set.range (n x))) →
    (∀ x k, γl x (n x k) = ((u ^ (-a x k) : Oˣ) : O) • n x k) →
    (∀ d, (∃ k : ℕ, B.Q ^ k • d ∈ W.N) →
      (∀ x, loc x d ∈ Submodule.span R (Set.range (n x))) → d ∈ W.N) →
    (∀ x k, ∀ j ∈ Finset.Icc (1 : ℤ) y, a x k + j ∈ Sx x) →
    ∀ d, B.Q ^ y • d ∈ W.N →
      Polynomial.aeval dd (∏ x, ∏ b ∈ Sx x, (Polynomial.X - Polynomial.C (c x b))) d ∈ W.N

open Formalism.CoboundaryTransfers in

def ToWachProd : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (S : HidaSetting O A) (ι : Type) [Finite ι]
    (pr : Equiv.Perm ι) (D : Type) [AddCommGroup D] [Module A D] [Module O D]
    [IsScalarTower O A D] (W : NData S ι pr D) (M h : ι → ℕ) (M₀ h₀ : ℕ),
    S.Rad → W.P2 → W.P5 M h → (∀ i, M i ≤ M₀) → (∀ i, h i ≤ h₀) →
    (S.base.GammaModX → (S.prodBase ι pr).GammaModX) ∧
    ∃ W' : WachMod (S.prodBase ι pr) M₀ (ι → D),
      (∀ x, x ∈ W'.N ↔ ∀ i, x i ∈ W.N i) ∧
      (∀ x i, W'.φ x i = W.φ i (x (pr i))) ∧ (∀ x i, W'.γ x i = W.γ i (x i)) ∧
      W'.HeightLower h₀

open Formalism.CoboundaryTransfers in

def GammaTrivialFiniteHeightLattice {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (B : Base O A) {D₁ : Type}
    [AddCommGroup D₁] [Module A D₁] [Module O D₁] (φ₁ γ₁ : D₁ →ₗ[O] D₁) (N₁ : Submodule A D₁) : Prop :=
  (∀ x ∈ N₁, ∃ x' ∈ N₁, γ₁ x - x = B.X • x') ∧
  (∃ k : ℕ, ∀ x ∈ N₁, B.Q ^ k • φ₁ x ∈ N₁) ∧
  (∃ k : ℕ, ∀ x ∈ N₁, B.Q ^ k • x ∈ Submodule.span A (φ₁ '' (N₁ : Set D₁)))

open Formalism.CoboundaryTransfers in

def TopDegreeLatticeProposition : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (B : Base O A) (M : ℕ) (D₀ D₁ D₂ : Type)
    [AddCommGroup D₀] [Module A D₀] [Module O D₀] [IsScalarTower O A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module O D₁] [IsScalarTower O A D₁]
    [AddCommGroup D₂] [Module A D₂]
    (W : WachMod B M D₀) (i : D₀ →ₗ[A] D₁) (p : D₁ →ₗ[A] D₂) (φ₁ γ₁ : D₁ →ₗ[O] D₁) (e : D₁)
    (y z m : D₀) (k : ℕ) (Lat : Submodule A D₁ → Prop),
    Function.Injective i → (∀ x, p (i x) = 0) → (∀ a : A, a • p e = 0 → a = 0) →
    (∀ (a : A) (x : D₁), φ₁ (a • x) = B.φ a • φ₁ x) →
    (∀ (a : A) (x : D₁), γ₁ (a • x) = B.γ a • γ₁ x) →
    (∀ x, φ₁ (i x) = i (W.φ x)) → (∀ x, γ₁ (i x) = i (W.γ x)) →
    φ₁ e = e + i y → γ₁ e = e + i z →
    W.C1 y z → y = W.φ m - m → z = W.γ m - m →
    B.GammaModX → W.HeightLower k →
    Lat (W.N.map i ⊔ Submodule.span A {e}) → Lat (W.N.map i ⊔ Submodule.span A {e - i m}) →
    (∀ N₁ N₂ : Submodule A D₁, Lat N₁ → Lat N₂ → GammaTrivialFiniteHeightLattice B φ₁ γ₁ N₁ → GammaTrivialFiniteHeightLattice B φ₁ γ₁ N₂ →
      N₁ = N₂) →
    m ∈ W.N

def SettingConsistentExample : Prop :=
  ∀ (ℓ s : ℕ), ℓ.Prime → 1 ≤ s → (ℓ = 2 → 2 ≤ s) →
    ∃ S : HidaSetting ℤ (Polynomial ℤ), S.ℓ = ℓ ∧ S.s = s ∧ S.c₀ = 1 ∧ S.Decomp ∧ ¬ IsUnit S.X ∧
      ¬ IsUnit S.Q ∧ S.γ S.π ≠ S.π

def SettingRadicalExample : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime],
    ∃ S : HidaSetting (ZMod ℓ) (PowerSeries (ZMod ℓ)), S.ℓ = ℓ ∧ S.Rad ∧ S.Decomp ∧ ¬ IsUnit S.X ∧
      ¬ IsUnit S.Q ∧ S.X ≠ 0 ∧ S.Q ≠ 0

def NontrivialWachExample : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (H : ℕ),
    ∃ (S : HidaSetting (ZMod ℓ) (PowerSeries (ZMod ℓ))) (D : Type) (_ : AddCommGroup D)
      (_ : Module (PowerSeries (ZMod ℓ)) D) (_ : Module (ZMod ℓ) D)
      (_ : IsScalarTower (ZMod ℓ) (PowerSeries (ZMod ℓ)) D)
      (W₁ W₂ : NData S Unit (Equiv.refl Unit) D) (F : NHom W₁ W₂) (c : ℕ),
      S.Rad ∧ S.Decomp ∧ W₁.P2 ∧ W₂.P2 ∧ W₁.P5 (fun _ => 0) (fun _ => H) ∧
      W₂.P5 (fun _ => 0) (fun _ => H) ∧ F.Kills () (S.π ^ c) ∧ ∀ k < H, ¬ F.Kills () (S.X ^ k)

end Formalism.RepresentationBoundsCohomology.N1
