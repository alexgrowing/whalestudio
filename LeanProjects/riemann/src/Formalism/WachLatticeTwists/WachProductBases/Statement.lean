import Formalism.WachLatticeTwists.WachProductBases.OneAddPowSubOne
import Formalism.CoboundaryTransfers.StatementAPI

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N1

open Formalism.CoboundaryTransfers

def BaseFacts : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (S : HidaSetting O A),
    (∃ t : A, S.X = S.π * t) ∧
    (∃ t : A, S.Q = (S.ℓ : A) + S.X * t) ∧
    S.φ S.X = S.X * S.Q ∧
    (∃ t : A, S.γ S.X = S.X * (algebraMap O A S.u + S.X * t)) ∧
    (∃ t : A, S.γ S.X - S.X = S.X * S.Q * t) ∧
    (∃ t : A, S.γ S.Q = S.Q * (1 + S.X * t) ∧ (S.Rad → IsUnit (1 + S.X * t)))

def BaseWach : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (S : HidaSetting O A),
    S.base.PhiX 1 ∧ S.base.GammaX S.u ∧ (S.Rad → S.base.GammaQ)

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A]

structure NData (S : HidaSetting O A) (ι : Type) (pr : Equiv.Perm ι) (D : Type) [AddCommGroup D]
    [Module A D] [Module O D] [IsScalarTower O A D] where
  N : ι → Submodule A D
  φ : ι → D →ₗ[O] D
  γ : ι → D →ₗ[O] D
  φ_smul : ∀ (i : ι) (a : A) (x : D), φ i (a • x) = S.φ a • φ i x
  γ_smul : ∀ (i : ι) (a : A) (x : D), γ i (a • x) = S.γ a • γ i x
  comm : ∀ (i : ι) (x : D), φ i (γ (pr i) x) = γ i (φ i x)
  X_bij : Function.Bijective (fun x : D => S.X • x)
  Q_bij : Function.Bijective (fun x : D => S.Q • x)
  etale : ∀ i : ι, Function.Bijective
    (fun m : Fin S.ℓ → D => ∑ j : Fin S.ℓ, S.ε ^ (j : ℕ) • φ i (m j))

namespace NData

variable {S : HidaSetting O A} {ι : Type} {pr : Equiv.Perm ι} {D : Type} [AddCommGroup D]
  [Module A D] [Module O D] [IsScalarTower O A D] (W : NData S ι pr D)

def P2 : Prop := ∀ i, ∀ x ∈ W.N i, ∃ x' ∈ W.N i, W.γ i x - x = S.X • x'

def P5 (M h : ι → ℕ) : Prop :=
  (∀ i, ∀ x ∈ W.N (pr i), S.Q ^ M i • W.φ i x ∈ W.N i) ∧
    ∀ i, ∀ x ∈ W.N i, S.Q ^ h i • x ∈ Submodule.span A (W.φ i '' (W.N (pr i) : Set D))

end NData

structure NHom {S : HidaSetting O A} {ι : Type} {pr : Equiv.Perm ι} {D₁ D₂ : Type}
    [AddCommGroup D₁] [Module A D₁] [Module O D₁] [IsScalarTower O A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module O D₂] [IsScalarTower O A D₂]
    (W₁ : NData S ι pr D₁) (W₂ : NData S ι pr D₂) where
  f : ι → D₁ →ₗ[A] D₂
  φ_comm : ∀ i x, f i (W₁.φ i x) = W₂.φ i (f (pr i) x)
  γ_comm : ∀ i x, f i (W₁.γ i x) = W₂.γ i (f i x)
  N_le : ∀ i, ∀ x ∈ W₁.N i, f i x ∈ W₂.N i

def NHom.Kills {S : HidaSetting O A} {ι : Type} {pr : Equiv.Perm ι} {D₁ D₂ : Type}
    [AddCommGroup D₁] [Module A D₁] [Module O D₁] [IsScalarTower O A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module O D₂] [IsScalarTower O A D₂]
    {W₁ : NData S ι pr D₁} {W₂ : NData S ι pr D₂} (F : NHom W₁ W₂) (i : ι) (a : A) : Prop :=
  ∀ n ∈ W₂.N i, ∃ n₁ ∈ W₁.N i, F.f i n₁ = a • n

def ToWach : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (S : HidaSetting O A) (ι : Type) [Finite ι]
    (pr : Equiv.Perm ι) (D : Type) [AddCommGroup D] [Module A D] [Module O D]
    [IsScalarTower O A D] (W : NData S ι pr D) (M h : ι → ℕ) (M₀ h₀ : ℕ),
    S.Rad → W.P2 → W.P5 M h → (∀ i, M i ≤ M₀) → (∀ i, h i ≤ h₀) →
    ∃ W' : WachMod S.base M₀ (ι → D),
      W'.N = Submodule.pi Set.univ W.N ∧
      (∀ x i, W'.φ x i = W.φ i (x (pr i))) ∧ (∀ x i, W'.γ x i = W.γ i (x i)) ∧
      W'.HeightLower h₀

def FreeMembershipHeightOne : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A] (N : Type)
    [AddCommGroup N] [Module A N] [Module.Free A N] (b : A) (x : N), b ≠ 0 →
    (∀ p : A, Prime p → p ∣ b → ∃ s : A, ¬ p ∣ s ∧ ∃ n : N, s • x = b • n) →
    ∃ n : N, x = b • n

def SaturationIntersection : Prop :=
  ∀ (A E : Type) [CommRing A] [CommRing E] [Algebra A E] (D : Type) [AddCommGroup D] [Module A D]
    [Module E D] [IsScalarTower A E D] (κ : Type) (b : Module.Basis κ E D) (l : A),
    (∀ c : E, (∃ a : A, algebraMap A E l * c = algebraMap A E a) → ∃ a : A, c = algebraMap A E a) →
    ∀ d : D, l • d ∈ Submodule.span A (Set.range b) → d ∈ Submodule.span A (Set.range b)

def ComapLeOfSaturated : Prop :=
  ∀ (A : Type) [CommRing A] (D₀ D₁ : Type) [AddCommGroup D₀] [Module A D₀] [AddCommGroup D₁]
    [Module A D₁] (f : D₀ →ₗ[A] D₁) (N₀ : Submodule A D₀) (N₁ : Submodule A D₁) (l : A),
    (∀ x, f x ∈ N₁ → ∃ k : ℕ, l ^ k • x ∈ N₀) →
    (∀ x, l • x ∈ N₀ → x ∈ N₀) →
    ∀ x, f x ∈ N₁ → x ∈ N₀

def CokernelKilledByPower : Prop :=
  ∀ (A : Type) [CommRing A] (D₁ D₂ : Type) [AddCommGroup D₁] [Module A D₁] [AddCommGroup D₂]
    [Module A D₂] (f : D₁ →ₗ[A] D₂) (N₁ : Submodule A D₁) (N₂ : Submodule A D₂) (π l : A) (a : ℕ),
    Function.Surjective f →
    (∀ n ∈ N₁, f n ∈ N₂) →
    (∀ n ∈ N₂, ∃ n₁ ∈ N₁, f n₁ = l ^ a • n) →
    (∀ d : D₁, ∃ k : ℕ, ∃ n₁ ∈ N₁, ∃ d' : D₁, π ^ k • d = n₁ + l ^ a • d') →
    (∀ d : D₂, (∃ k : ℕ, π ^ k • (l • d) ∈ N₂) → ∃ k : ℕ, π ^ k • d ∈ N₂) →
    N₂.FG →
    ∃ c : ℕ, ∀ n ∈ N₂, ∃ n₁ ∈ N₁, f n₁ = π ^ c • n

def P8 : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (B : Base O A) (M : ℕ)
    (D₀ D₁ D₂ : Type)
    [AddCommGroup D₀] [Module A D₀] [Module O D₀] [IsScalarTower O A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module O D₁] [IsScalarTower O A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module O D₂] [IsScalarTower O A D₂]
    (W₀ : WachMod B M D₀) (W₁ : WachMod B M D₁) (W₂ : WachMod B M D₂) (S : SES W₀ W₁ W₂),
    ∀ x ∈ W₁.N, W₂.φ (S.π.f x) = S.π.f x → W₂.γ (S.π.f x) = S.π.f x →
      ∃ y z, W₀.Cocycle y z ∧ S.ι.f y = W₁.φ x - x ∧ S.ι.f z = W₁.γ x - x

def P2c3 : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (B : Base O A) (M : ℕ)
    (D₀ D₁ D₂ : Type)
    [AddCommGroup D₀] [Module A D₀] [Module O D₀] [IsScalarTower O A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module O D₁] [IsScalarTower O A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module O D₂] [IsScalarTower O A D₂]
    (W₀ : WachMod B M D₀) (W₁ : WachMod B M D₁) (W₂ : WachMod B M D₂) (S : SES W₀ W₁ W₂)
    (e : D₁) (c : O),
    W₂.φ (S.π.f e) = S.π.f e → W₂.γ (S.π.f e) = S.π.f e →
    ∀ x ∈ W₁.N, S.π.f x = c • S.π.f e →
      ∃ ye ze y z, S.ι.f ye = W₁.φ e - e ∧ S.ι.f ze = W₁.γ e - e ∧ (ye, ze) ∈ W₀.Z1 ∧
        W₀.Cocycle y z ∧ (y, z) - c • (ye, ze) ∈ W₀.B1

def P2c1 : Prop :=
  ∀ (A : Type) [CommRing A] (D₀ D₁ D₂ : Type) [AddCommGroup D₀] [Module A D₀] [AddCommGroup D₁]
    [Module A D₁] [AddCommGroup D₂] [Module A D₂] (i : D₀ →ₗ[A] D₁) (p : D₁ →ₗ[A] D₂)
    (N : Submodule A D₀) (e : D₁) (m : D₀),
    Function.Injective i → (∀ x, p (i x) = 0) → (∀ a : A, a • p e = 0 → a = 0) →
    N.map i ⊔ Submodule.span A {e} = N.map i ⊔ Submodule.span A {e - i m} →
    m ∈ N

def ProductBasisLatticeProposition : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (B : Base O A) (M : ℕ) (D₀ D₁ : Type)
    [AddCommGroup D₀] [Module A D₀] [Module O D₀] [IsScalarTower O A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module O D₁] [IsScalarTower O A D₁]
    (W : WachMod B M D₀) (i : D₀ →ₗ[A] D₁) (φ₁ γ₁ : D₁ →ₗ[O] D₁) (e : D₁) (y z : D₀) (k : ℕ),
    (∀ (a : A) (x : D₁), φ₁ (a • x) = B.φ a • φ₁ x) →
    (∀ (a : A) (x : D₁), γ₁ (a • x) = B.γ a • γ₁ x) →
    (∀ x, φ₁ (i x) = i (W.φ x)) → (∀ x, γ₁ (i x) = i (W.γ x)) →
    φ₁ e = e + i y → γ₁ e = e + i z → W.C1 y z → B.GammaModX → W.HeightLower k →
    let N₁ : Submodule A D₁ := W.N.map i ⊔ Submodule.span A {e}
    (∀ x ∈ N₁, ∃ x' ∈ N₁, γ₁ x - x = B.X • x') ∧
    (∀ x ∈ N₁, B.Q ^ M • φ₁ x ∈ N₁) ∧
    (∀ x ∈ N₁, B.Q ^ (k + M) • x ∈ Submodule.span A (φ₁ '' (N₁ : Set D₁)))

def ProductBasisProposition : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (B : Base O A) (M : ℕ)
    (D₀ D₁ D₂ : Type)
    [AddCommGroup D₀] [Module A D₀] [Module O D₀] [IsScalarTower O A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module O D₁] [IsScalarTower O A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module O D₂] [IsScalarTower O A D₂]
    (W₀ : WachMod B M D₀) (W₁ : WachMod B M D₁) (W₂ : WachMod B M D₂) (S : SES W₀ W₁ W₂) (e : ℕ),
    CokerKilled S e → RatSurj S →
    ∀ y₁ z₁, W₁.C1 y₁ z₁ → W₂.Cocycle (S.π.f y₁) (S.π.f z₁) →
      ∃ ω, W₀.C2 ω ∧ S.ι.f ω = W₁.d1 y₁ z₁ ∧ ∃ k : ℕ, W₀.IsCob2 (((B.p : O) ^ k) • ω)

def InvariantNorm : Prop :=
  ∀ (A : Type) [CommRing A] (Δ : Type) [Group Δ] [Fintype Δ] [MulSemiringAction Δ A]
    (φ γ : A →+* A) (π q r E u t : A) (w : Δ → A),
    (∀ (d : Δ) (a : A), φ (d • a) = d • φ a) → (∀ (d : Δ) (a : A), γ (d • a) = d • γ a) →
    φ π = π * q → (∀ d, IsUnit (w d)) → (∀ d, d • π = w d * π) →
    IsUnit r → q = r * E → (∀ d : Δ, d • E = E) →
    γ π = π * (u + π * t) → (∀ d : Δ, d • u = u) →
    (∀ d : Δ, d • (∏ d' : Δ, d' • π) = ∏ d' : Δ, d' • π) ∧
    (∃ v, IsUnit v ∧ ∏ d : Δ, d • π = v * π ^ Fintype.card Δ) ∧
    (∃ v, IsUnit v ∧ (∀ d : Δ, d • v = v) ∧
      φ (∏ d : Δ, d • π) = v * (∏ d : Δ, d • π) * E ^ Fintype.card Δ) ∧
    (∃ t', γ (∏ d : Δ, d • π) = (∏ d : Δ, d • π) * (u ^ Fintype.card Δ + π * t'))

def PowerSeriesCofactorIsUnitOfConstantCoeff : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (l a b : O) (g E h : PowerSeries O),
    l ≠ 0 → IsUnit a → IsUnit b → g = E * h →
    PowerSeries.constantCoeff g = l * a → PowerSeries.constantCoeff E = l * b → IsUnit h

def InvariantBasisAverage : Prop :=
  ∀ (A : Type) [CommRing A] (Δ : Type) [Group Δ] [Fintype Δ] [MulSemiringAction Δ A]
    (N : Type) [AddCommGroup N] [Module A N] (κ : Type) [Fintype κ] (_b : Module.Basis κ A N)
    (ρ : Δ → N →+ N) (π : A),
    (∀ d d' x, ρ (d * d') x = ρ d (ρ d' x)) → (∀ x, ρ 1 x = x) →
    (∀ d (a : A) x, ρ d (a • x) = (d • a) • ρ d x) →
    π ∈ (⊥ : Ideal A).jacobson → IsUnit ((Fintype.card Δ : ℕ) : A) →
    (∀ d x, ∃ x', ρ d x - x = π • x') →
    ∃ b' : Module.Basis κ A N, ∀ d k, ρ d (b' k) = b' k

def GammaSubOnePiInvariants : Prop :=
  ∀ (A : Type) [CommRing A] (Δ : Type) [Group Δ] [MulSemiringAction Δ A]
    (N : Type) [AddCommGroup N] [Module A N] (κ : Type) [Fintype κ] (b : Module.Basis κ A N)
    (ρ : Δ → N →+ N) (γ : N →+ N) (π π' : A),
    (∀ d (a : A) x, ρ d (a • x) = (d • a) • ρ d x) → (∀ d k, ρ d (b k) = b k) →
    (∀ d x, γ (ρ d x) = ρ d (γ x)) →
    (∀ x, ∃ x', γ x - x = π • x') →
    (∀ a : A, (∀ d : Δ, d • (π * a) = π * a) → ∃ a' : A, (∀ d : Δ, d • a' = a') ∧ π * a = π' * a') →
    ∀ x, (∀ d, ρ d x = x) → ∃ x', (∀ d, ρ d x' = x') ∧ γ x - x = π' • x'

def TwistLatticeCondition : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (B : Base O A) (M : ℕ) (D : Type)
    [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D] (W : WachMod B M D)
    (u : O) (j k : ℕ),
    B.φ B.X = B.X * B.Q → B.GammaX u → B.GammaQ →
    (∀ t : A, IsUnit (algebraMap O A u + B.X * t)) →
    Function.Surjective (fun x : D => B.X • x) → W.HeightLower k →
    ∃ W' : WachMod B (M + j) D, (∀ x, x ∈ W'.N ↔ B.X ^ j • x ∈ W.N) ∧ W'.φ = W.φ ∧
      W'.γ = u ^ j • W.γ ∧ W'.HeightLower (k - j)

def LocalWachProductConsequence : Prop :=
  ∀ (L R : Type) [CommRing L] [CommRing R] [Algebra L R] (P : Type) [AddCommGroup P] [Module R P]
    [Module L P] [IsScalarTower L R P] (t : R) (u : Lˣ) (γR : R →ₐ[L] R) (γ : P →ₗ[L] P)
    (κ : Type) [Fintype κ] (n : κ → P) (a : κ → ℤ) (y : ℕ) (Sx : Finset ℤ),
    γR t = (u : L) • t →
    (∀ (r : R) (x : P), γ (r • x) = γR r • γ x) →
    (∀ r : R, ∃ c : ℕ → L, ∃ r' : R, r = ∑ j ∈ Finset.range y, c j • t ^ j + t ^ y * r') →
    Function.Bijective (fun x : P => t • x) →
    (∀ k, γ (n k) = ((u ^ (-a k) : Lˣ) : L) • n k) →
    (∀ k, ∀ j ∈ Finset.Icc (1 : ℤ) y, a k + j ∈ Sx) →
    ∀ x : P, t ^ y • x ∈ Submodule.span R (Set.range n) →
      Polynomial.aeval γ (∏ b ∈ Sx, (Polynomial.X - Polynomial.C (((u ^ (-b) : Lˣ) : L)))) x ∈
        Submodule.span R (Set.range n)

def SemilinearActionOnEigenvectorFamily : Prop :=
  ∀ (L R : Type) [CommRing L] [CommRing R] [Algebra L R] (P : Type) [AddCommGroup P] [Module R P]
    [Module L P] [IsScalarTower L R P] (t : R) (u : Lˣ) (γR : R →ₐ[L] R) (γ : P →ₗ[L] P)
    (κ : Type) [Fintype κ] (n : κ → P) (a : κ → ℤ) (Sx : Finset ℤ),
    γR t = (u : L) • t →
    (∀ (r : R) (x : P), γ (r • x) = γR r • γ x) →
    (∀ r : R, ∃ c : L, ∃ r' : R, r = algebraMap L R c + t * r') →
    (∀ k, γ (n k) = ((u ^ (-a k) : Lˣ) : L) • n k) →
    (∀ k, a k ∈ Sx) →
    ∀ x ∈ Submodule.span R (Set.range n), ∃ x' ∈ Submodule.span R (Set.range n),
      Polynomial.aeval γ (∏ b ∈ Sx, (Polynomial.X - Polynomial.C (((u ^ (-b) : Lˣ) : L)))) x = t • x'

def GlobalWachProductConsequence : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (D : Type) [AddCommGroup D] [Module A D]
    [Module O D] [IsScalarTower O A D] (N : Submodule A D) (γ : D →ₗ[O] D) (Q : A) (y : ℕ)
    (p : Polynomial O) (ρ : Type) (P : ρ → Type) [∀ x, AddCommGroup (P x)] [∀ x, Module O (P x)]
    (loc : ∀ x, D →ₗ[O] P x) (γl : ∀ x, P x →ₗ[O] P x) (Ll Ly : ∀ x, Submodule O (P x)),
    (∀ x d, (∃ k : ℕ, Q ^ k • d ∈ N) → loc x (γ d) = γl x (loc x d)) →
    (∀ d, (∃ k : ℕ, Q ^ k • d ∈ N) → (∀ x, loc x d ∈ Ll x) → d ∈ N) →
    (∀ d, (∃ k : ℕ, Q ^ k • d ∈ N) → ∃ k : ℕ, Q ^ k • γ d ∈ N) →
    (∀ d, Q ^ y • d ∈ N → ∀ x, loc x d ∈ Ly x) →
    (∀ x, ∀ v ∈ Ly x, Polynomial.aeval (γl x) p v ∈ Ll x) →
    ∀ d, Q ^ y • d ∈ N → Polynomial.aeval γ p d ∈ N

def C5 : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (u : ℤ_[ℓ]ˣ), ℓ ≠ 2 → PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = 1 →
    ∃ c : ℤ → ℤ_[ℓ], (∀ x, (ℓ : ℤ_[ℓ]) * c x = 1 - ((u ^ (-x) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) ∧ c 0 = 0 ∧
      ∀ x y, x ≠ y → Associated (c x - c y) ((ℓ : ℤ_[ℓ]) ^ padicValInt ℓ (x - y))

def C3 : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (B : Base O A) (M : ℕ) (D : Type)
    [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D] (W : WachMod B M D) (y : ℕ),
    B.GammaQ → ∀ x : D, B.Q ^ y • x ∈ W.N → ∃ x' : D, B.Q ^ y • x' ∈ W.N ∧ W.γ x - x = B.X • x'

def ProductBasisInclusion : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (S : HidaSetting O A) (D' D : Type)
    [AddCommGroup D'] [Module A D'] [AddCommGroup D] [Module A D] (Φ : D' →+ D)
    (N₂' N'' : Submodule A D') (N₂ N' : Submodule A D) (M h : ℕ) (aa' : Ideal A) (g : A),
    S.Decomp →
    (∀ (a : A) (x : D'), Φ (a • x) = S.φ a • Φ x) →
    (∀ m : Fin S.ℓ → D', (∀ j, m j ∈ N₂') → ∑ j : Fin S.ℓ, S.ε ^ (j : ℕ) • Φ (m j) = 0 →
      ∀ j, m j = 0) →
    N'' ≤ N₂' →
    (∀ a, a ∈ aa' ↔ ∀ n ∈ N₂', a • n ∈ N'') →
    (∀ n ∈ N₂', S.Q ^ M • Φ n ∈ N₂) →
    (∀ n ∈ N', S.Q ^ h • n ∈ Submodule.span A (Φ '' (N'' : Set D'))) →
    (∀ n ∈ N₂, g • n ∈ N') →
    S.Q ^ (M + h) * g ∈ Ideal.map (S.φ : A →+* A) aa'

def ProductBasisPsiOperator : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] (φA : A →+* A) (ε X Q : A) (H c : ℕ)
    (ι : Type) (pr : ι → ι) (aa : ι → Ideal A),
    Function.Surjective pr →
    φA ε = ε ^ ℓ →
    (∀ g : A, ∃! e : Fin ℓ → A, g = ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i)) →
    φA X = X * Q →
    (∀ i, ∀ a ∈ aa i, Q ^ H * a ∈ Ideal.map φA (aa (pr i))) →
    (∀ i, (ε - 1) ^ c ∈ aa i) →
    ∀ i, X ^ H ∈ aa i

def Lemma3a : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (S : HidaSetting O A) (ι : Type)
    (pr : Equiv.Perm ι) (D₁ D₂ : Type)
    [AddCommGroup D₁] [Module A D₁] [Module O D₁] [IsScalarTower O A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module O D₂] [IsScalarTower O A D₂]
    (W₁ : NData S ι pr D₁) (W₂ : NData S ι pr D₂) (F : NHom W₁ W₂) (M h : ι → ℕ) (H c : ℕ),
    S.Decomp → W₁.P5 M h → W₂.P5 M h → (∀ i, M i + h i ≤ H) →
    (∀ i, F.Kills i (S.π ^ c)) →
    ∀ i, F.Kills i (S.X ^ H)

def ProductBasisTameExponent : Prop :=
  ∀ (A : Type) [CommRing A] (aa : Ideal A) (π π' w : A) (ℓ e s' H : ℕ),
    2 ≤ ℓ → e * s' = ℓ - 1 → π' = w * π ^ s' → π ^ H ∈ aa →
    π' ^ ⌈((e * H : ℕ) : ℚ) / ((ℓ - 1 : ℕ) : ℚ)⌉₊ ∈ aa

def ProductBasisInvariants : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (Δ : Type) [Group Δ] [Fintype Δ]
    (D₁ D₂ : Type)
    [AddCommGroup D₁] [Module A D₁] [Module O D₁] [IsScalarTower O A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module O D₂] [IsScalarTower O A D₂]
    (ρ₁ : Δ →* Module.End O D₁) (ρ₂ : Δ →* Module.End O D₂) (f : D₁ →ₗ[A] D₂)
    (N₁ : Submodule A D₁) (N₂ : Submodule A D₂) (a : A),
    IsUnit ((Fintype.card Δ : ℕ) : O) →
    (∀ d, ∀ x ∈ N₁, ρ₁ d x ∈ N₁) → (∀ d x, f (ρ₁ d x) = ρ₂ d (f x)) →
    (∀ d x, ρ₂ d (a • x) = a • ρ₂ d x) →
    (∀ n ∈ N₂, ∃ n₁ ∈ N₁, f n₁ = a • n) →
    ∀ n ∈ N₂, (∀ d, ρ₂ d n = n) → ∃ n₁ ∈ N₁, (∀ d, ρ₁ d n₁ = n₁) ∧ f n₁ = a • n

end Formalism.RepresentationBoundsCohomology.N1
