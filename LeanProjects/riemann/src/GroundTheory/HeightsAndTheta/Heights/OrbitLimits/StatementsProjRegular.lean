import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivPushA
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

def projRegular {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
    {n : ℕ} (R : AnLogRes P J (n + 1)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    {V : Set R.X} (BV : FinHolAtlas n V) : Set V :=
  {x | Ψ (segre (R.lift x.1 x.1)) 0 ≠ 0 ∧ ∀ j, x ∈ (BV.chart j).source →
    LinearMap.det (fderiv ℂ ((projCoord R Ψ ∘ Subtype.val) ∘ (BV.chart j).symm) (BV.chart j x) :
      (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≠ 0}

def ProjRegular.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (V : Set R.X) (BV : FinHolAtlas n V),
    HoloMap BV R.A Subtype.val →
    IsOpen (projRegular R Ψ BV) ∧
    (∀ x : V, Ψ (segre (R.lift x.1 x.1)) 0 ≠ 0 → ∀ j, x ∈ (BV.chart j).source →
      AnalyticAt ℂ ((projCoord R Ψ ∘ Subtype.val) ∘ (BV.chart j).symm) (BV.chart j x)) ∧
    (∀ x : V, Ψ (segre (R.lift x.1 x.1)) 0 ≠ 0 →
      LinearMap.det (fderiv ℂ ((projCoord R Ψ ∘ Subtype.val) ∘ (BV.chart (chartIdx BV x)).symm)
        (BV.chart (chartIdx BV x) x) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≠ 0 →
      x ∈ projRegular R Ψ BV)

end GroundTheory.Heights₂.Heights.Targets
