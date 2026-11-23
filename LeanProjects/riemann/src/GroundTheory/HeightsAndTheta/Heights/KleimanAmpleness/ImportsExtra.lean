import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherTer
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockComp
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

theorem ModelChangeVeryAmple.proof (hGen : ModelChangeGen.Statement) : ModelChangeVeryAmple.Statement := by
  intro F _ Ω _ _ N K _ _ ι _ y k₀ e K' _ _ ι' _ y' k₀' e' hy hy' hx β β' hs
  exact veryAmple_change hGen F Ω N K ι y k₀ e K' ι' y' k₀' e' hy hy' hx β β' hs

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
