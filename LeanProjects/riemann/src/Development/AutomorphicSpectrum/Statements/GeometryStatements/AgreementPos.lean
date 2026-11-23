import Mathlib
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Filter Topology
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

def AgreementPos : Prop :=
  Inputs → ∀ (D : ℕ) (σ : Type) [Fintype σ] (S : AnSys D σ) (abelian₂ : ℝ), 0 < S.t₀ → ∃ C₃ s₀ : ℝ, 0 < s₀ ∧
    ∀ (II : IntersectionSystem), IsFullIntersectionSystem II →
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (Re : Realis S P),
      (∀ w, Tendsto (fun t => Re.num II t w) (𝓝[>] 0) (𝓝 (Re.limNum II w))) ∧
      ∀ s, 0 < s → s ≤ s₀ → Real.exp (-(s ^ 2)⁻¹) ≤ S.t₀ ∧ ∀ c : σ → ℝ, ∑ a, |c a| ≤ abelian₂ →
        |eval c (Re.FT II (Real.exp (-(s ^ 2)⁻¹))) - eval c (Re.PB II)| ≤ C₃ * s

end GlobalTheory.CompanionTheory.Ar.PB
