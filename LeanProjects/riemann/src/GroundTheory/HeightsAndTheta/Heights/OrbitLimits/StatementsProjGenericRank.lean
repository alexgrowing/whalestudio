import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjRegular
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

def ProjGenericRank.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (V : Set R.X) (BV : FinHolAtlas n V),
    HoloMap BV R.A Subtype.val → IsClosed V → (∀ x ∈ V, Ψ (segre (R.lift x x)) ≠ 0) →
    ∀ j, ∀ᵐ u, u ∈ (BV.chart j).target → (BV.chart j).symm u ∉ projRegular R Ψ BV →
      ∃ p : (k : K) → ι k,
        (∀ k, R.lift ((BV.chart j).symm u).1 ((BV.chart j).symm u).1 ⟨k, p k⟩ ≠ 0) ∧
        Module.finrank ℂ (LinearMap.range (fderiv ℂ
          (fun y => ReciprocityTheory.ChartRestriction.G.Geo.affCoord p
            (R.lift ((BV.chart j).symm u).1 ((BV.chart j).symm y).1)) u :
            (Fin n → ℂ) →ₗ[ℂ] ((Σ k, ι k) → ℂ))) < n

end GroundTheory.Heights₂.Heights.Targets
