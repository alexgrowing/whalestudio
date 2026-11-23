import Formalism.LocalToGlobal.GaloisLevelStructure.TiedGal
import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal

namespace Formalism.L2

def OmFrame.Extends {D : Formalism.BasicNotions.D7} (fr : OmFrame D) (T : Host.Frame D.host) : Prop := ∀ x, fr.jE x = T.j x

end Formalism.L2
