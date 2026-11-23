import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjRegular
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.DivPushResSideInhabitants
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

def ProjRegularClosureOpen.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (V : Set R.X) (BV : FinHolAtlas n V),
    HoloMap BV R.A Subtype.val → IsOpen (closure (projRegular R Ψ BV))

end GroundTheory.Heights₂.Heights.Targets
