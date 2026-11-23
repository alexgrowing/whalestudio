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

def formsRe {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (T : FormsTiedSym D u Ch chOf) :
    FormsTiedSym (reD D Z) u Ch chOf := by kcopy T

end GlobalTheory.Mem.SRe.ColRe

end
