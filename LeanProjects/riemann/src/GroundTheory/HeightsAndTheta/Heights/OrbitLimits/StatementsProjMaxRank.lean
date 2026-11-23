import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjFullRankDense
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

def projMaxRank {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
    {n : ℕ} (R : AnLogRes P J (n + 1)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    {V : Set R.X} (BV : FinHolAtlas n V) : Set V :=
  {x | ∃ i : Fin (n + 1), Ψ (segre (R.lift x.1 x.1)) i ≠ 0 ∧ ∃ j, x ∈ (BV.chart j).source ∧
    Module.finrank ℂ (LinearMap.range (fderiv ℂ
      (fun u l => Ψ (segre (R.lift x.1 ((BV.chart j).symm u).1)) l /
        Ψ (segre (R.lift x.1 ((BV.chart j).symm u).1)) i) (BV.chart j x) :
        (Fin n → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))) = n}

end GroundTheory.Heights₂.Heights.Targets
