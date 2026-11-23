import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjPotMassEq
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjFullRankDense
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

def ProjPotDens.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (V : Set R.X) (BV : FinHolAtlas n V),
    HoloMap BV R.A Subtype.val → ∀ j, ∀ y ∈ (BV.chart j).target,
      0 ≤ locDens BV (fun _ => multiprojPot R V) j y ∧
        ((BV.chart j).symm y ∈ projFullRank R BV →
          0 < locDens BV (fun _ => multiprojPot R V) j y)

end GroundTheory.Heights₂.Heights.Targets
