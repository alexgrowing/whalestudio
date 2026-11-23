import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal

noncomputable section

open NumberField

namespace Formalism.L2.Host

open Formalism.BasicNotions Formalism.FrobeniusOrbits

def SameFrameN {D : D7} (T : HostTied D) (jE : D.host.E →+* Qb) : Prop := ∀ x, jE x = T.fr.j x

end Formalism.L2.Host
