import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPtZeroNeZero
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraLast
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

theorem ModelNumEq.proof (hN : NumModel.Statement) : ModelNumEq.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e hmod d βs Qs hsecs hsub
  exact hN F K ι Ω y k₀ N e _ rfl hmod d Qs βs (fun j c => hsecs j c) hsub

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
