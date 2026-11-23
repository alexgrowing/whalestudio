import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.DimPosOfHasType

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CM

def DegSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [NeZero H.d] (χ : DirichletCharacter ℂ H.d),
    IsKroneckerChar χ → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (T : PAT H (Sp (𝓞 K))),
    Splits E K → ρ ^ 2 = -(H.d : 𝓞 K) → HasType H T.t.act ρ 1 0 →
    ∀ (F : GenFib T.pol) (h : HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ →
      ((2 * deg h (F.eigLat T.t.act τ) : ℝ) : ℂ) = logOm E χ

def LenSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K)
    (σ₁ : K →+* ℂ) (p q : ℕ) (X : CMObj H K ρ σ₁ p q) (FA : ∀ b, GenFib (X.A b).pol) (FB : GenFib X.B.pol)
    (hA : ∀ b, HermFam K (Fin (FA b).P₀.g → K)) (hB : HermFam K (Fin FB.P₀.g → K)),
    (∀ b, (FA b).IsHerm (hA b)) → FB.IsHerm hB →
    ∀ (j : Fin p ⊕ Fin q) (M : (Fin (FA j.isLeft).P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K)),
      (FA j.isLeft).IsDiffOf FB (X.φ j) M → ∀ (s : K →+* ℂ) (τ : 𝓞 E →+* 𝓞 K),
      ∀ c ∈ (FA j.isLeft).eigLat (X.A j.isLeft).t.act τ,
        hB.nrm s (M c) ^ 2 = (s (τ (X.hh j) : K)).re * (hA j.isLeft).nrm s c ^ 2

def IndSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K)
    (σ₁ : K →+* ℂ) (p q : ℕ) (X : CMObj H K ρ σ₁ p q) (FA : ∀ b, GenFib (X.A b).pol) (FB : GenFib X.B.pol)
    (M : ∀ j : Fin p ⊕ Fin q, (Fin (FA j.isLeft).P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K)),
    (∀ j, (FA j.isLeft).IsDiffOf FB (X.φ j) (M j)) →
    let N : (Fin p ⊕ Fin q) × (𝓞 E →+* 𝓞 K) → Submodule (𝓞 K) (Fin FB.P₀.g → K) := fun x =>
      ((FA x.1.isLeft).eigLat (X.A x.1.isLeft).t.act x.2).map ((M x.1).restrictScalars (𝓞 K))
    (∀ x, N x ≤ FB.eigLat X.B.t.act x.2) ∧
    (∀ x, latRank K (N x) = open Classical in if x.2 H.rt = (if x.1.isLeft then ρ else -ρ) then 1 else 0) ∧
    (∀ j, Function.Injective (M j)) ∧
    iSupIndep (fun x => Submodule.span K (N x : Set (Fin FB.P₀.g → K))) ∧
    ⨆ x, Submodule.span K (N x : Set (Fin FB.P₀.g → K)) = ⊤

def KeyAtSt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (hg rig hr th hth)
    (h : HermFam K (Fin F.P₀.g → K)) (δ : ℝ), F.IsHerm h → IsThetaDeg (F.key hg rig hr th hth) δ →
    δ = -(1 / 2) * deg h F.lieLat + (P.g : ℝ) / 4 * Real.log (2 * Real.pi)

def DegBoundSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [NeZero H.d] (χ : DirichletCharacter ℂ H.d),
    IsKroneckerChar χ → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ)
    (X : CMObj H K ρ σ₁ p q) (FB : GenFib X.B.pol) (hB : HermFam K (Fin FB.P₀.g → K)) (Λ : ℝ), FB.IsHerm hB → 0 < Λ →
    (∀ j (τ : E →+* ℂ), ‖τ (X.hh j : E)‖ ≤ Λ ^ 2) →
    ((Module.finrank ℚ E / 2 * (p + q) : ℕ) : ℝ) * ((logOm E χ).re / 2 - Real.log Λ) ≤ deg hB FB.lieLat ∧
    ∀ (hg rig hr th hth) (δ : ℝ), IsThetaDeg (FB.key hg rig hr th hth) δ →
      δ ≤ ((Module.finrank ℚ E / 2 * (p + q) : ℕ) : ℝ) *
        (-(1 / 2) * ((logOm E χ).re / 2 - Real.log Λ) + Real.log (2 * Real.pi) / 4)

namespace NumInh

variable {K : Type} [Field K] [NumberField K] {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem deg_conjugate_type (hD : DegSt) [NeZero H.d] {χ : DirichletCharacter ℂ H.d} (hχ : IsKroneckerChar χ) {ρ : 𝓞 K}
    {σ₁ : K →+* ℂ} {p q : ℕ} (X : CMObj H K ρ σ₁ p q) (F : GenFib (X.A false).pol) {h : HermFam K (Fin F.P₀.g → K)}
    (hh : F.IsHerm h) {τ : 𝓞 E →+* 𝓞 K} (hτ : τ H.rt = -ρ) :
    2 * deg h (F.eigLat (X.A false).t.act τ) = (logOm E χ).re := by
  have hD' := hD E H χ hχ K (-ρ) (X.A false) X.split (by rw [neg_sq]; exact X.ρ_sq)
    (Test.hasType_neg X.ρ_sq X.typeM) F h hh τ hτ
  have hre := congrArg Complex.re hD'
  rwa [Complex.ofReal_re] at hre

end NumInh

end GlobalTheory.CM
end
