import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsCyclicClassPolynomial

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.HT
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LKP

structure Raw (K R : Type) [Field K] [Ring R] [Algebra ℚ R] where

  A : AbVar K

  ia : R →ₐ[ℚ] End0 A

  L : LB A.X.left
  hL : L.IsLB

section General

variable {K R : Type} [Field K] [Ring R] [Algebra ℚ R]

def Raw.c (X : Raw K R) : Pic X.A.X.left := cls X.L X.hL

def IsPol (σ : R → R) (X : Raw K R) : Prop :=
  IsAmpleCls X.c ∧ ∀ r : End0 X.A →ₗ[ℚ] End0 X.A, IsRosati X.c r → ∀ x, r (X.ia x) = X.ia (σ x)

def Intertw {A B : AbVar K} (f : A ⟶ B) (a : End0 A) (b : End0 B) : Prop :=
  ∀ (n : ℤ) (g : End A) (h : End B), n • a = toEnd0 A g → n • b = toEnd0 B h →
    (show A ⟶ A from g) ≫ f = f ≫ (show B ⟶ B from h)

def IsRIsog {A B : AbVar K} (a : R →ₐ[ℚ] End0 A) (b : R →ₐ[ℚ] End0 B) (f : A ⟶ B) : Prop :=
  IsIsogeny f ∧ ∀ x, Intertw f (a x) (b x)

def PolIsog (X Y : Raw K R) : Prop :=
  ∃ (f : X.A ⟶ Y.A) (m n : ℕ), IsRIsog X.ia Y.ia f ∧ 0 < m ∧ 0 < n ∧
    m • AbVar.lam X.c (fst X.A.X X.A.X) (snd X.A.X X.A.X) =
      n • AbVar.lam Y.c (fst X.A.X X.A.X ≫ f.hom) (snd X.A.X X.A.X ≫ f.hom)

def Betti (X : Raw K R) {W : Type} [AddCommGroup W] [Module ℚ W] (ρ : R → W → W) (ψ : W → W → ℚ) : Prop :=
  ∃ (Λ : Submodule ℤ W) (s : ℚ), Λ.FG ∧ Submodule.span ℚ (Λ : Set W) = ⊤ ∧ 0 < s ∧
    (∀ v ∈ Λ, ∀ w ∈ Λ, ∃ a : ℤ, s * ψ v w = a) ∧
    ∀ (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 →
      ∃ (β : Λ →ₗ[ℤ] Tl l X.A) (ζ : Tate l (AlgebraicClosure K)ˣ),
        Function.Bijective (β.liftBaseChange ℤ_[l]) ∧ Submodule.span ℤ_[l] {ζ} = ⊤ ∧
        (∀ (x : R) (n : ℤ) (g : End X.A) (v w : Λ), n • X.ia x = toEnd0 X.A g → n • ρ x v = (w : W) →
          tend l X.A g (β v) = β w) ∧
        ∀ E : Tl l X.A →ₗ[ℤ_[l]] Tl l X.A →ₗ[ℤ_[l]] Tate l (AlgebraicClosure K)ˣ, IsWeilForm l X.L E →
          ∀ (v w : Λ) (a : ℤ), s * ψ v w = a → E (β v) (β w) = a • ζ

def Link {K' : Type} [Field K'] (X : Raw K R) (Y : Raw K' R) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], (l : K') ≠ 0 →
    ∃ (e : Tl l X.A ≃ₗ[ℤ_[l]] Tl l Y.A)
      (u : Tate l (AlgebraicClosure K)ˣ ≃ₗ[ℤ_[l]] Tate l (AlgebraicClosure K')ˣ),
      (∀ (x : R) (n : ℤ) (g : End X.A) (h : End Y.A), n • X.ia x = toEnd0 X.A g → n • Y.ia x = toEnd0 Y.A h →
        ∀ t, e (tend l X.A g t) = tend l Y.A h (e t)) ∧
      ∀ (E : Tl l X.A →ₗ[ℤ_[l]] Tl l X.A →ₗ[ℤ_[l]] Tate l (AlgebraicClosure K)ˣ)
        (E' : Tl l Y.A →ₗ[ℤ_[l]] Tl l Y.A →ₗ[ℤ_[l]] Tate l (AlgebraicClosure K')ˣ),
        IsWeilForm l X.L E → IsWeilForm l Y.L E' → ∀ s t, E' (e s) (e t) = u (E s t)

def IsTwist {A : AbVar K} (c d : Pic A.X.left) (h : End0 A) : Prop :=
  ∃ (n m : ℕ) (g : End A), 0 < n ∧ 0 < m ∧ (m : ℤ) • h = toEnd0 A g ∧
    IsAdj (A := A) (B := A) c d (𝟙 A) n g

def IsFrobModel (q : ℕ) (A : AbVar K) (φ : End A) : Prop :=
  ∃ (k : Type) (_ : Field k) (_ : Fintype k) (_ : Algebra k K) (A₀ : AbVar k) (e : baseChange K A₀ ≅ A),
    Fintype.card k = q ∧ (show A ⟶ A from φ) = e.inv ≫ bcMap K (A := A₀) (B := A₀) (frob A₀) ≫ e.hom

def PInt (p : ℕ) {D : Type} [Ring D] (x : D) : Prop := ∃ N : ℕ, ¬ p ∣ N ∧ IsIntegral ℤ (N • x)

def PUnit (p : ℕ) {D : Type} [Ring D] (x : D) : Prop := ∃ u : Dˣ, (u : D) = x ∧ PInt p x ∧ PInt p ((u⁻¹ : Dˣ) : D)

def FrobLike (p r : ℕ) (A : AbVar K) (π : End0 A) : Prop :=
  ∃ (m : ℕ) (φ : End A) (u : End0 A), 0 < m ∧ IsFrobModel (p ^ (r * m)) A φ ∧ Commute π (toEnd0 A φ) ∧
    PUnit p u ∧ π ^ m = u * toEnd0 A φ

end General

abbrev Fb (p : ℕ) [Fact p.Prime] : Type := AlgebraicClosure (ZMod p)

abbrev Zb : Type := integralClosure ℤ ℂ

section CM

variable {M : Type} [Field M] [NumberField M]

def intEmb (φ : M →+* ℂ) : 𝓞 M →+* Zb :=
  (φ.comp (algebraMap (𝓞 M) M)).codRestrict (integralClosure ℤ ℂ) fun x =>
    (RingOfIntegers.isIntegral_coe x).map_of_comp_eq (RingHom.id ℤ) φ (RingHom.ext_int _ _)

def IsCMType (Φ : Finset (M →+* ℂ)) : Prop := ∀ φ, φ ∈ Φ ↔ ComplexEmbedding.conjugate φ ∉ Φ

def Matches (p r : ℕ) {k : Type} [Field k] (j : Zb →+* k) (Φ : Finset (M →+* ℂ)) (π : M) : Prop :=
  π ≠ 0 ∧ ∀ (w : HeightOneSpectrum (𝓞 M)) (m : ℤ), (p : 𝓞 M) ∈ w.asIdeal →
    w.valuation M π = WithZero.exp (-m) →
      (Ideal.absNorm w.asIdeal : ℚ) ^ m =
        (p : ℚ) ^ (r * Nat.card {φ : Φ // RingHom.ker (j.comp (intEmb φ.1)) = w.asIdeal})

def HasInt {K : Type} [Field K] (X : Raw K M) (a : OAct (𝓞 M) X.A.X) : Prop :=
  ∀ x : 𝓞 M, ∃ g : End X.A, AbVar.Hom.hom g = a.act x ∧ X.ia x = toEnd0 X.A g

def IsCMLie {K : Type} [Field K] (X : Raw K M) {I : Type} [Fintype I] [DecidableEq I]
    (φ : I → 𝓞 M →+* K) : Prop :=
  2 * X.A.dim = Module.finrank ℚ M ∧ ∃ a : OAct (𝓞 M) X.A.X, HasInt X a ∧ IsLieType a φ

variable [IsCMField M]

def cj (x : M) : M := IsCMField.complexConj M x

def TotPos (h : M) : Prop := cj h = h ∧ ∀ φ : M →+* ℂ, 0 < (φ h).re

def PosXi (Φ : Finset (M →+* ℂ)) (ξ : M) : Prop := cj ξ = -ξ ∧ ∀ φ ∈ Φ, 0 < (φ ξ).im

def sigH {d : ℕ} (H : Fin d → M) (x : Matrix (Fin d) (Fin d) M) : Matrix (Fin d) (Fin d) M :=
  Matrix.of fun i j => (H i)⁻¹ * cj (x j i) * H j

def psiH {d : ℕ} (H : Fin d → M) (ξ : M) (v w : Fin d → M) : ℚ :=
  Algebra.trace ℚ M (ξ * ∑ i, H i * v i * cj (w i))

def psi1 (ξ v w : M) : ℚ := Algebra.trace ℚ M (ξ * (v * cj w))

def XiEquiv (ξ ξ' : M) : Prop := ∃ (c : ℚ) (x : M), 0 < c ∧ x ≠ 0 ∧ ξ' = c * (x * cj x) * ξ

def admitted (p r : ℕ) {K : Type} [Field K] {d : ℕ} (H : Fin d → M) (π : M)
    (X : Raw K (Matrix (Fin d) (Fin d) M)) : Prop :=
  IsPol (sigH H) X ∧ 2 * X.A.dim = d * Module.finrank ℚ M ∧
    FrobLike p r X.A (X.ia (Matrix.scalar (Fin d) π))

end CM

def ClassifyField : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (r : ℕ) (M : Type) [Field M] [NumberField M] [IsCMField M] (d : ℕ) (H : Fin d → M)
    (Φ : Finset (M →+* ℂ)) (j : Zb →+* Fb p) (π : M), 0 < r → 0 < d → (∀ i, TotPos (H i)) → IsCMType Φ →
    Matches p r j Φ π →
    ∃ X : {ξ : M // PosXi Φ ξ} → Raw (Fb p) (Matrix (Fin d) (Fin d) M),
      (∀ ξ, admitted p r H π (X ξ) ∧ Betti (X ξ) Matrix.mulVec (psiH H ξ.1)) ∧
      (∀ Y, admitted p r H π Y → ∃ ξ, PolIsog Y (X ξ)) ∧
      ∀ ξ ξ', PolIsog (X ξ) (X ξ') ↔ XiEquiv ξ.1 ξ'.1

end GlobalTheory.LKP
