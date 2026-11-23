import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.FibDis
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExOmTOfSteps
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensFibV

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Topology
open scoped TensorProduct

def FreeOpen : Prop := InCtx fun F E _ _ _ _ _ _σ M _J a _X0 _hT =>
  IsOpen {X : Fin a → Fin M → Ainf F ⊗[F] E | LinearIndependent (Ainf F ⊗[F] E) X} ∧
  ∀ v : HeightOneSpectrum (𝓞 F),
    IsOpen {X : Fin a → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X}

end PI.VolStabS
