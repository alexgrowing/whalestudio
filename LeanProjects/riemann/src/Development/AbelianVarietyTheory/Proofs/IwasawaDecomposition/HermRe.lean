import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RedivisionStructureEq
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Formalism.LocalToGlobal.NumberFieldFamilies.OwnStruct
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports

noncomputable section

namespace GlobalTheory.Mem.SRe.ColRe

open Formalism.BasicNotions Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.SRe NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (Z : New D)

set_option maxHeartbeats 4000000 in

def hermRe (H : Formalism.L2.Herm.ColsHermS D) : Formalism.L2.Herm.ColsHermS (reD D Z) := by kcopy H

end GlobalTheory.Mem.SRe.ColRe

end
