import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameDegreeZeroFormsSelf

noncomputable section

namespace GlobalTheory.Mem.SRe

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.SG.RowDict Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl K Yd cX}

def SRest.toSTiesR (Rc : Formalism.L2.RecT ex) {P : SPack D fun u => (Rc.T.cols.forms u).to0} (S : SRest P) :
    Formalism.L2.SG.SpectralTiesReal.STiesR Rc where
  toSTies := S.toSTies
  tr := P.tr
  into := P.into
  bij := P.bij
  lev := P.lev
  colPin := fun _ => S.colPin
  inst := P.inst
  G := P.G
  rowTie := fun _ => S.rowTie
  locTied := S.locTied

section
variable (Rc : Formalism.L2.RecT ex) {P : SPack D fun u => (Rc.T.cols.forms u).to0} (S : SRest P)

theorem SRest.toSTiesR_X : (S.toSTiesR Rc).X = P.X := rfl

end

end GlobalTheory.Mem.SRe

end
