import Formalism.LocalToGlobal.ClassRec
import Formalism.LocalToGlobal.KernelLattices.KerChTie
import Formalism.LocalToGlobal.KernelLattices.AdaptedEnt
import Formalism.LocalToGlobal.KernelLattices.TopPin

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions

namespace Formalism.L2.Ker

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}

structure KerPins (R : Formalism.L2.RecT ex) : Prop where

  ch : R.T.ker.ChTie

  adapted : R.T.ker.Adapted

  top : R.T.ker.TopPinned

end Formalism.L2.Ker
