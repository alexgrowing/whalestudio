import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.UIObjects
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLinePartitionContinuousCoe
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.EnergySum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot mInt MIntegrable locDens)

def TailShift.Statement : Prop :=
  ∀ (D : ℕ) (B CE : ℝ), ∃ CE' : ℝ, ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas D X) (Yo : Set X) (r r' : X → ℝ) (T : Fin D → LocPot X),
    IsOpen Yo → ContinuousOn r Yo → ContinuousOn r' Yo →
    (∀ x ∈ Yo, Real.exp 1 ≤ r x) → (∀ x ∈ Yo, Real.exp 1 ≤ r' x) →
    (∀ x ∈ Yo, |r x - r' x| ≤ B) →
    (∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ Yo → 0 ≤ locDens A T j y) →
    TailLogBound A Yo r' T CE → TailLogBound A Yo r T CE'

section Inhabitants

open ReciprocityTheory.AnForm (fsDens fsDens_pos)
open ReciprocityTheory.AnForm.M (p1 fsPot projectiveLine_locDens_first_chart projectiveLine_locDens_second_chart projectiveLine_fubiniStudy_mass_one)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
