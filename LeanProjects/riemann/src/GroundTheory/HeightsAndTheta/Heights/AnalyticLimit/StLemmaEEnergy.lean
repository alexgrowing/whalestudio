import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaETrunc
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPsh mInt)

def LemmaEEnergy.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas D X)
    (Om : KaehlerForm A) (v : Fin D → X → ℝ) (w : X → ℝ), (∀ i, A.Smooth (v i)) →
    (∀ i, IsPsh A (potForm Om.pot (v i))) → (∀ i x, -1 ≤ v i x ∧ v i x ≤ 0) → A.Smooth w →
    IsPsh A (potForm Om.pot w) →
    mInt A (fun i => potForm Om.pot (v i)) (fun x => -w x) ≤
      mInt A (fun _ => Om.pot) (fun x => -w x) + D * Om.vol

section Inhabitants

open ReciprocityTheory.AnForm.M (p1)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
