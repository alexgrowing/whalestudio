import Formalism.LocalToGlobal.KernelLattices.KerPins
import Formalism.LocalToGlobal.KernelLattices.KerMemPin

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions

namespace Formalism.L2.Ker

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}

structure KerPinsU (R : Formalism.L2.RecT ex) : Prop where

  pins : KerPins R

  mem : R.T.ker.MemSideU

end Formalism.L2.Ker
