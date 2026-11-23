import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.UIObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (mInt)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell errE)

noncomputable section

def GreenMassError.Statement : Prop :=
  ∀ {D : ℕ} {W : Type} [TopologicalSpace W] [CompactSpace W] [T2Space W] (S : UIData D W)
    (a : ℕ) (ha : a < D + 1), ∀ δ, 0 < δ → ∃ τ, 0 < τ ∧ ∀ t₀ t, 0 < t → t ≤ t₀ → t₀ ≤ τ →
      S.ell₀ ≤ ell t₀ → S.errW a ha t₀ t ≤ δ ∧ S.errDiv a ha t₀ t ≤ δ

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
