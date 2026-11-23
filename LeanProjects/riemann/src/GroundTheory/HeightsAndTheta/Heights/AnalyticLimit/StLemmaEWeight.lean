import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaETrunc
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection IsPsh)

def LemmaEWeight.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (Om : KaehlerForm A) (L : LocPot X) (s : X → X → ℂ), IsPotential A L → IsSection A L s →
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ l : ℝ, 1 ≤ l → ∃ w : X → ℝ, A.Smooth w ∧ IsPsh A (potForm Om.pot w) ∧
      (∀ x ∈ secOpen s, min (c₀ * rSec L s x) l ≤ -w x ∧ -w x ≤ c₀ * rSec L s x + 1) ∧
      (∀ x, x ∉ secOpen s → l ≤ -w x)

section Inhabitants

open ReciprocityTheory.AnForm.M (p1 fsPot projectiveLinePairSection projLine_isSmoothPotential projLine_isHolomorphicSection)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
