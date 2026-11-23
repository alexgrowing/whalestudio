import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaETrunc
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPsh mInt MIntegrable)

def LemmaETruncMass.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (Om : KaehlerForm A) (Yo : Set X) (r : X → ℝ) (u : Fin D → X → ℝ) (v : ℝ → Fin D → X → ℝ),
    IsOpen Yo → ContinuousOn r Yo → (∀ i, A.SmoothOn Yo (u i)) →
    (∀ i, FormNonneg A Yo (potForm Om.pot (u i))) →
    (∀ R : ℝ, Real.exp 1 ≤ R → ∀ i, A.Smooth (v R i) ∧ IsPsh A (potForm Om.pot (v R i)) ∧
      ∃ c : ℝ, ∀ x ∈ Yo, r x < R → v R i x = u i x + c) →
    ∀ R₀ : ℝ, Real.exp 1 ≤ R₀ →
      MIntegrable A (fun i => potForm Om.pot (u i)) ((tail Yo r R₀).indicator 1) ∧
      mInt A (fun i => potForm Om.pot (u i)) ((tail Yo r R₀).indicator 1) ≤
        mInt A (fun i => potForm Om.pot (v R₀ i)) ({x | x ∉ Yo ∨ R₀ ≤ r x}.indicator 1)

section Inhabitants

open ReciprocityTheory.AnForm.M (p1 fsPot projectiveLinePairSection projLine_isSmoothPotential projLine_isHolomorphicSection)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
