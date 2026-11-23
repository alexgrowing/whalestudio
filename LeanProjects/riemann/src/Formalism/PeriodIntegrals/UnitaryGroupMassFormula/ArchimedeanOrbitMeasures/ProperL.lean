import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ConstY

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem pushLFin_of_proper (h : ProperOrb) : PushLFin := by
  intro D X u' ψ hT μinf νinf fibInf hH K hK hKI
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have : X.measG.μGinf.IsHaarMeasure := X.measG_norm.2.1
  obtain ⟨N, hN, C, hC, hNC⟩ := h X u' ψ hT μinf νinf fibInf hH K hK hKI
  rw [Measure.map_apply (measurable_orbM X u') hK.isClosed.measurableSet]
  refine lt_of_le_of_lt (measure_mono fun g hg => hNC 1 (mem_of_mem_nhds hN) g ?_) hC.measure_lt_top
  rw [rmulT_one]; exact hg

end PI.AprimeInfW
