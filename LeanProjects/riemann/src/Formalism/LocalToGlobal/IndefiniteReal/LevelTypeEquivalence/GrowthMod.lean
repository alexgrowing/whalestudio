import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContinuousPsiT

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField
open scoped TensorProduct

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def finOnly (V : HSp D) (x : GA D V) : GA D V := (infOnly D V x)⁻¹ * x

end Formalism.IndefR.Eqv

end
