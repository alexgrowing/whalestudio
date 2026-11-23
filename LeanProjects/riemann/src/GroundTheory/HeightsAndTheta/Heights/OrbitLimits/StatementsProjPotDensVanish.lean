import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjPotMassEq
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

def ProjPotDensVanish.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (V : Set R.X) (BV : FinHolAtlas n V),
    HoloMap BV R.A Subtype.val → (∀ x ∈ V, Ψ (segre (R.lift x x)) ≠ 0) →
    ∀ j, ∀ u ∈ (BV.chart j).target, (BV.chart j).symm u ∉ projMaxRank R Ψ BV →
      locDens BV (fun _ => projPot R Ψ V) j u = 0

end GroundTheory.Heights₂.Heights.Targets
