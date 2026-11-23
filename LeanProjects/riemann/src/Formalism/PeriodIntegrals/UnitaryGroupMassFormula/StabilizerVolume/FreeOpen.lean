import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.FibTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensAll

noncomputable section

namespace PI.VolStabS

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW TensAllW

theorem freeOpen_holds : FreeOpen := by
  intro F E _ _ _ _ _ σ hCM M J hJ _ _ a _ _ X0 hT hdet
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  refine ⟨isOpen_linIndep (Module.finBasis F E) (Ainf F) (isOpen_units_Ainf F) (lip_ainf F),
    fun v => ?_⟩
  exact isOpen_linIndep (Module.finBasis F E) (Fv F v) (isOpen_units_Fv F v) (lip_field _)

end PI.VolStabS
