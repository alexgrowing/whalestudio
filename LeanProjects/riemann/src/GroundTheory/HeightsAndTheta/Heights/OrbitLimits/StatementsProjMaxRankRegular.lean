import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjMaxRank
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

def ProjMaxRankRegular.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (V : Set R.X) (BV : FinHolAtlas n V),
    HoloMap BV R.A Subtype.val →
    ∀ y ∈ projMaxRank R Ψ BV, Ψ (segre (R.lift y.1 y.1)) 0 ≠ 0 → y ∈ projRegular R Ψ BV

end GroundTheory.Heights₂.Heights.Targets
