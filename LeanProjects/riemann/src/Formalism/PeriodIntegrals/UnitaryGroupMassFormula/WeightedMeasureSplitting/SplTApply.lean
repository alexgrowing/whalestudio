import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures

noncomputable section

namespace PI.UnitaryGroupMassFormula.MeasWCore

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Measures NumberField
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def splT : AF F ⊗[F] E →+* (Ainf F ⊗[F] E) × (Af F ⊗[F] E) :=
  RingHom.prod (tensMap (E := E) (fstA F)) (tensMap (E := E) (sndA F))

theorem splT_apply (x : AF F ⊗[F] E) :
    splT x = (tensMap (E := E) (fstA F) x, tensMap (E := E) (sndA F) x) := rfl

end PI.UnitaryGroupMassFormula.MeasWCore
