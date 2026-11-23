import Formalism.LocalRingCardinality.DataTheta

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH

namespace Formalism.IndefR

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsFDiag (V : HSp D) : Prop :=
  ∃ d : Fin V.rank → D.host.F, V.gram = Matrix.diagonal (fun i => algebraMap D.host.F D.host.E (d i))

end Formalism.IndefR
