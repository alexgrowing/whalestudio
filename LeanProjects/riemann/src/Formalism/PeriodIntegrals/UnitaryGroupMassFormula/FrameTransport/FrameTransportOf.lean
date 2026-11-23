import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameTransport.StepTransl

noncomputable section

namespace PI.FT

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Topology
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}

instance instBorelHA {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : BorelSpace (HA (AF F) σ J) :=
  ⟨rfl⟩

end PI.FT
