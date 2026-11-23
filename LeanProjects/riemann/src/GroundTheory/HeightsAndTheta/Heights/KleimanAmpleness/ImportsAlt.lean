import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsStepDataDimZero
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsLastTail
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldChartRingOverPnPtZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

theorem ClaimVanishDimZero.proof (h₁ : PointChartField.Statement) (h₂ : CechPointVanish.Statement) :
    ClaimVanishDimZero.Statement := by
  intro F _ K _ _ ι _ _ Ω _ _ y k₀ μ r a m c₁ σ hd
  exact ⟨0, fun b c _ => h₂ F K ι Ω y (h₁ F K ι Ω y hd.2.1) _⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
