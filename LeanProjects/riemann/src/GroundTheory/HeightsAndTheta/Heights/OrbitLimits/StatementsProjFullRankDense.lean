import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjRegular
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.DivPushResSideInhabitants
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

def projFullRank {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
    {n : ℕ} (R : AnLogRes P J (n + 1)) {V : Set R.X} (BV : FinHolAtlas n V) : Set V :=
  {x | ∃ p : (k : K) → ι k, (∀ k, R.lift x.1 x.1 ⟨k, p k⟩ ≠ 0) ∧ ∃ j, x ∈ (BV.chart j).source ∧
    Module.finrank ℂ (LinearMap.range (fderiv ℂ
      (fun y => ReciprocityTheory.ChartRestriction.G.Geo.affCoord p (R.lift x.1 ((BV.chart j).symm y).1)) (BV.chart j x) :
        (Fin n → ℂ) →ₗ[ℂ] ((Σ k, ι k) → ℂ))) = n}

def ProjFullRankDense.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (V : Set R.X) (BV : FinHolAtlas n V),
    HoloMap BV R.A Subtype.val → IsClosed V → (∀ x ∈ V, Ψ (segre (R.lift x x)) ≠ 0) →
    ∀ x ∈ projFullRank R BV, x ∈ interior (closure (projRegular R Ψ BV))

end GroundTheory.Heights₂.Heights.Targets
