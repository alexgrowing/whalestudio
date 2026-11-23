import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.UIObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (mInt)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell errE)

noncomputable section

def GreenMassReplace.Statement : Prop :=
  ∀ {D : ℕ} {W : Type} [TopologicalSpace W] [CompactSpace W] [T2Space W] (S : UIData D W),
    ∃ Cκ, 0 ≤ Cκ ∧ ∀ (a : ℕ) (ha : a < D + 1) (t₀ : ℝ), 0 < t₀ → S.ell₀ ≤ ell t₀ →
      ∃ K, 0 ≤ K ∧ ∀ ε t, 0 < ε → ε ≤ 1 → 0 < t → t ≤ t₀ →
        S.plTerm a ha ε t ≤ K * S.J a ε t + Cκ * S.errW a ha t₀ t + 2 * S.errDiv a ha t₀ t

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
