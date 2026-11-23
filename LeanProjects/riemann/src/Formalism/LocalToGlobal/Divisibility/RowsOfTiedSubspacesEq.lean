import Formalism.LocalToGlobal.Divisibility.RecBridge
import Formalism.LocalToGlobal.HilbertRowConditions.ColumnsFunctionAtSubspaces

open NumberField

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Rows Formalism.L2.Indef

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}

def DivisionRowsFace.ofCompatibleData (T : TiedDataSK ex) (P : RowSideFamily ex) (h : RowSideDetermined T P) (hr : RowsHold0_3 P)
    (Zsc : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) : DivisionRowsFace L where
  Bs := P.A3.fam3.base3
  Am := P.A3.fam3.amb3
  fc := Formalism.IndefR.Cx.faceOf3 P.A3 P.P0 P.ψ0 P.Ps P.ψs (Classical.choose h.faces)
    (Classical.choose (Classical.choose_spec h.faces)) Zsc
  Zs := P.Zs
  stable := hr.zsSt
  inBlock := hr.zsBl
  wf0 := P.A3.side_well_formed (Classical.choose_spec hr.famOk) P.P0 P.ψ0 P.Zs hr.zsSt hr.zsBl hr.famSep
  wf1 := P.A3.side_well_formed (Classical.choose_spec hr.famOk) P.Ps P.ψs P.Zs hr.zsSt hr.zsBl hr.famSep
  what₂ := Classical.choose hr.rows0

end Formalism.L2.DIV

end
