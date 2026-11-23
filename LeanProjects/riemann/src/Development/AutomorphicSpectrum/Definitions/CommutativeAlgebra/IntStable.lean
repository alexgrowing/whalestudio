import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements

namespace GlobalTheory.CompanionTheory.Ar.HS

open MvPolynomial NumberField GroundTheory.Heights₂.Heights

noncomputable section

section Forms
variable {R : Type*} [CommRing R] {k D N n : ℕ}

def comb (w : Fin n → Fin N → R) (x : Fin n → R) : Fin N → R := fun j => ∑ a, x a * w a j

def pair (u y : Fin N → R) : R := ∑ j, u j * y j

def pull (w : Fin n → Fin N → R) (f : MvPolynomial (Fin k × Fin N) R) :
    MvPolynomial (Fin k × Fin n) R :=
  bind₁ (fun ij => ∑ a, C (w a ij.2) * X (ij.1, a)) f

def pull1 (w : Fin n → Fin N → R) (g : MvPolynomial (Fin N) R) : MvPolynomial (Fin n) R :=
  bind₁ (fun j => ∑ a, C (w a j) * X a) g

def consPt (ξ : Fin N → R) (s : Fin D → Fin N → R) : Fin (D + 1) × Fin N → R :=
  fun ij => Fin.cases (motive := fun _ => R) (ξ ij.2) (fun i => s i ij.2) ij.1

def specRest (f : MvPolynomial (Fin (D + 1) × Fin N) R) (s : Fin D → Fin N → R) :
    MvPolynomial (Fin N) R :=
  bind₁ (fun ij => Fin.cases (motive := fun _ => MvPolynomial (Fin N) R) (X ij.2)
    (fun i => C (s i ij.2)) ij.1) f

def IsTransv (J : Set (MvPolynomial (Fin N) R)) (s : Fin D → Fin N → R) (y : Fin N → R) : Prop :=
  y ≠ 0 ∧ (∀ g ∈ J, eval y g = 0) ∧ (∀ i, pair (s i) y = 0) ∧
    ∀ v : Fin N → R, (∀ g ∈ J, ∑ j, eval y (pderiv j g) * v j = 0) → (∀ i, pair (s i) v = 0) →
      ∃ c : R, v = c • y

def Splits {δ : ℕ} (f : MvPolynomial (Fin (D + 1) × Fin N) R) (θ : Fin N → R)
    (s : Fin D → Fin N → R) (y : Fin δ → Fin N → R) : Prop :=
  (∃ c : R, c ≠ 0 ∧ specRest f s = C c * ∏ q, linForm (y q)) ∧
    (∀ q q', q ≠ q' → ∀ c : R, y q ≠ c • y q') ∧ ∀ q, pair θ (y q) ≠ 0

end Forms

section Heights
variable {K : Type*} [Field K] [NumberField K]

def hfin {ι : Type*} (g : MvPolynomial ι K) : ℝ :=
  (1 / Module.finrank ℚ K : ℝ) *
    ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v g)

def meanEmb (a : (K →+* ℂ) → ℝ) : ℝ := (1 / Module.finrank ℚ K : ℝ) * ∑ σ : K →+* ℂ, a σ

def chowHtW {k N n : ℕ} (w : Fin n → Fin N → K) (H : ArchData K N) (δ : ℕ)
    (f : MvPolynomial (Fin k × Fin N) K) : ℝ :=
  hfin (pull w f) +
    meanEmb fun σ => mahler (H.normAt σ) k (f.map σ) + k * δ * (harmonic (N - 1) : ℝ) / 2

def ptHt {F : Type*} [Field F] [NumberField F] [Algebra F K] {N n : ℕ} (w : Fin n → Fin N → F)
    (H : ArchData F N) (y : Fin N → K) : ℝ :=
  (1 / Module.finrank ℚ K : ℝ) *
    (∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      Real.log (⨆ a, NumberField.HeightOneSpectrum.adicAbv K v
        (pair (fun j => algebraMap F K (w a j)) y))) +
    meanEmb fun τ : K →+* ℂ =>
      Real.log ((H.normAt (τ.comp (algebraMap F K))).dualNorm fun j => τ (y j))

end Heights

structure ChowData (F : Type) [Field F] [NumberField F] (D N n δ : ℕ) where

  I : Ideal (MvPolynomial (Fin N) F)
  projPrime : IsProjPrime I
  nondeg : ∀ u : Fin N → F, linForm u ∈ I → u = 0
  one_le_D : 1 ≤ D

  f : MvPolynomial (Fin (D + 1) × Fin N) F
  chow : IsChowForm I (D + 1) f
  homog : IsMultiHomog δ f

  w : Fin n → Fin N → F
  span_top : Submodule.span F (Set.range w) = ⊤
  int_stable : ∀ (c : 𝓞 F) (a : Fin n), (c : F) • w a ∈ Submodule.span ℤ (Set.range w)

  H : ArchData F N

  Λ : ℝ
  one_le_Λ : 1 ≤ Λ
  w_le : ∀ (a : Fin n) (σ : F →+* ℂ), (H.normAt σ).norm (fun j => σ (w a j)) ≤ Λ

  θ : Fin N → F
  θ_ne : θ ≠ 0

namespace ChowData
variable {F : Type} [Field F] [NumberField F] {D N n δ : ℕ} (X : ChowData F D N n δ)

def h : ℝ := chowHtW X.w X.H δ X.f / (((D : ℝ) + 1) * δ)

def Theta : ℝ := n * D * δ * (2 + |X.h| + Real.log X.Λ)

def rho0 (l : ℕ) : ℝ := 8 * D * δ * n * l * X.Λ

def eqs {Ω : Type*} [Field Ω] (σ : F →+* Ω) : Set (MvPolynomial (Fin N) Ω) :=
  MvPolynomial.map σ '' (X.I : Set (MvPolynomial (Fin N) F))

variable {K : Type} [Field K] [NumberField K] [Algebra F K]

def sec (x : Fin D → Fin n → 𝓞 K) : Fin D → Fin N → K :=
  fun i => comb (fun a j => algebraMap F K (X.w a j)) fun a => (x i a : K)

def normK (τ : K →+* ℂ) (u : Fin N → K) : ℝ :=
  (X.H.normAt (τ.comp (algebraMap F K))).norm fun j => τ (u j)

def SplitsAt (x : Fin D → Fin n → 𝓞 K) (y : Fin δ → Fin N → K) : Prop :=
  Splits (X.f.map (algebraMap F K)) (fun j => algebraMap F K (X.θ j)) (X.sec x) y

structure ChoiceOut (l : ℕ) (x : Fin D → Fin n → 𝓞 K) (y : Fin δ → Fin N → K) : Prop where
  splits : X.SplitsAt x y
  norm_le : ∀ τ i, X.normK τ (X.sec x i) ≤ X.rho0 l * (1 + 1 / (8 * D * δ))
  norm_ge : ∀ τ i, X.rho0 l * (1 - 1 / (8 * D * δ)) ≤ X.normK τ (X.sec x i)
  ht_ge : ((D : ℝ) + 1) * δ * X.h + D * δ * Real.log (X.rho0 l) -
      δ * (((D : ℝ) + 1) * (harmonic (N - 1) : ℝ) / 2 + Real.log 2 / δ + 1 / 8) ≤
    ∑ q, ptHt X.w X.H (y q)
  ht_le : ∑ q, ptHt X.w X.H (y q) ≤ ((D : ℝ) + 1) * δ * X.h +
      δ * ∑ i, meanEmb fun τ : K →+* ℂ => Real.log (X.normK τ (X.sec x i))
  residue : ∀ P : Ideal (𝓞 K), P.IsPrime → P ≠ ⊥ → l ≤ Ideal.absNorm P

end ChowData

end

end GlobalTheory.CompanionTheory.Ar.HS
