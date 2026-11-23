import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.ResidueChartModel
import GroundTheory.HeightsAndTheta.Heights.ThetaKeyFormula.RigSymFormTauIIsBasisOf
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.KeyFormula

open Complex Matrix

noncomputable section

open RigSymForm

def ResidueFiniteModel.Statement : Prop :=
  ∀ (P : RigSymForm ℂ) (a : ℕ), 3 ≤ a → ∀ (r : ℕ) (x : Fin (r + 1) → P.Fn), P.IsBasisOf a x →
    ∀ b : ℕ, b < a → Nonempty (ResidueChartModel P a b x)

theorem residueFiniteModel_hyps :
    rigSymFormTauI.g = 1 ∧ 3 ≤ 3 ∧ rigSymFormTauI.IsBasisOf 3 (r := 2) thetaThreeFam ∧ 1 < 3 :=
  ⟨rfl, le_rfl, rigSymFormTauI_isBasisOf, by norm_num⟩

theorem residueFiniteModel_point :
    3 ≤ 3 ∧ pointForm.IsBasisOf 3 pointX ∧ 0 < 3 ∧ Nonempty (ResidueChartModel pointForm 3 0 pointX) :=
  ⟨le_rfl, pointX_isBasisOf, by norm_num, ⟨pointChartModel⟩⟩

end

end GroundTheory.Heights₂.Heights.KeyFormula
