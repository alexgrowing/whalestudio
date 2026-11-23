import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.UIObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (mInt)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell errE)

noncomputable section

def GreenMassZero.Statement : Prop :=
  ∀ {D : ℕ} {W : Type} [TopologicalSpace W] [CompactSpace W] [T2Space W] (S : UIData D W),
    ∀ η, 0 < η → ∃ ε₀, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ t, S.J 0 ε t ≤ η

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
