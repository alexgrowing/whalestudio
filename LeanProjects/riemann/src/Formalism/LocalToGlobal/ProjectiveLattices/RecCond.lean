import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition

namespace Formalism.L2.Pj

open Formalism.BasicNotions

def OKPsi (D : D7) : Prop := ∀ Q : Par D, Q.Pins → ∀ j, InR D j → KPsiIn (Dw := Q.Dw j) Q.c

end Formalism.L2.Pj
