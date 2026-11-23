import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaETrunc
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection IsPsh mInt)

def LemmaETruncTail.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (Om : KaehlerForm A) (L : LocPot X) (s : X → X → ℂ), IsPotential A L → IsSection A L s →
    Dense (secOpen s) → (∀ y, ‖s y y‖ * Real.exp (-L.φ y y) ≤ 1) →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ℝ, 1 ≤ M → ∀ v : Fin D → X → ℝ, (∀ i, A.Smooth (v i)) →
      (∀ i, IsPsh A (potForm Om.pot (v i))) → (∀ i x, -M ≤ v i x ∧ v i x ≤ 0) →
      ∀ ρ : ℝ, Real.exp 1 ≤ ρ →
        mInt A (fun i => potForm Om.pot (v i))
            ({x | x ∉ secOpen s ∨ ρ ≤ rSec L s x}.indicator 1) ≤ M ^ D * K / ρ

section Inhabitants

open ReciprocityTheory.AnForm.M (p1 fsPot projectiveLinePairSection projLine_isSmoothPotential projLine_isHolomorphicSection)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
