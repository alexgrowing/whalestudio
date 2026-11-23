import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsSmoothPts

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def IsSmoothOnPts {J : Type} [Fintype J] (P : Ideal (MvPolynomial J ℤ)) (D : ℕ)
    (u : (J → ℂ) → ℝ) : Prop :=
  IsDegZero u ∧ ∀ (U : Set (Fin D → ℂ)) (γ : (Fin D → ℂ) → J → ℂ), IsParam P U γ →
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ∘ γ) U

def ExtStatement : Prop :=
  ∀ (J : Type) [Fintype J] (P : Ideal (MvPolynomial J ℤ)) (D : ℕ) (u : (J → ℂ) → ℝ),
    P.IsPrime → IsHomogIdeal ℤ P → P.comap (C : ℤ →+* MvPolynomial J ℤ) = ⊥ →
    IsSmoothPts P D → IsSmoothOnPts P D u →
    ∃ ũ : (J → ℂ) → ℝ, IsDegZero ũ ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ũ {z | z ≠ 0} ∧ (∀ z ∈ pts P, ũ z = u z) ∧
      ((∀ z ∈ pts P, u (conjPt z) = u z) → ∀ z, ũ (conjPt z) = ũ z)

def PtsLocalStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (φ φ' : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g g' : ((Σ k, ι k) → ℂ) → ℝ),
    (∀ j, ∀ z ∈ mcPts P, φ j z = φ' j z) → (∀ z ∈ mcPts P, g z = g' z) →
    ptsIntegralAt P Ψ φ g = ptsIntegralAt P Ψ φ' g' ∧ ptsIntegral P φ g = ptsIntegral P φ' g'

end ReciprocityTheory.ChartRestriction.G.Geo
