import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaETailLog
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLemmaETailLog
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.EnergyStep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPsh)

def LemmaETrunc.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas D X) (Om : KaehlerForm A)
    (Yo : Set X) (r : X → ℝ) (C₁ : ℝ) (u : X → ℝ), IsOpen Yo → Dense Yo →
    (∀ x ∈ Yo, Real.exp 1 ≤ r x) → 0 ≤ C₁ → A.SmoothOn Yo u → FormNonneg A Yo (potForm Om.pot u) →
    (∀ x ∈ Yo, u x ≤ 0) → (∀ x ∈ Yo, -(C₁ * Real.log (r x)) ≤ u x) →
    (A.Smooth u ∨ ∀ y, y ∉ Yo → Tendsto u (𝓝[Yo] y) atBot) →
    ∀ R : ℝ, Real.exp 1 ≤ R → ∃ v : X → ℝ, A.Smooth v ∧ IsPsh A (potForm Om.pot v) ∧
      (∀ x, -(C₁ * Real.log R + 2) ≤ v x ∧ v x ≤ 0) ∧
      ∃ c : ℝ, ∀ x ∈ Yo, r x < R → v x = u x + c

section Inhabitants

open ReciprocityTheory.AnForm.M (p1 fsPot projectiveLinePairSection projLine_isSmoothPotential projLine_isHolomorphicSection)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
