import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaETrunc
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPsh mInt)

def LemmaEScale.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas D X)
    (Om : KaehlerForm A) (M : ℝ) (v : Fin D → X → ℝ), 1 ≤ M → (∀ i, A.Smooth (v i)) →
    (∀ i, IsPsh A (potForm Om.pot (v i))) →
    (∀ i, IsPsh A (potForm Om.pot fun x => v i x / M)) ∧
    ∀ g : X → ℝ, Continuous g → (∀ x, 0 ≤ g x) →
      mInt A (fun i => potForm Om.pot (v i)) g ≤
        M ^ D * mInt A (fun i => potForm Om.pot fun x => v i x / M) g

section Inhabitants

open ReciprocityTheory.AnForm.M (p1)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
