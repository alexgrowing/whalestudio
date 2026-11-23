import Mathlib
import Formalism.LocalToGlobal.Divisibility.DivisibilityConstruction.RBDGam
import Formalism.LocalToGlobal.HilbertRowConditions.ColumnsFunctionAtSubspaces

open Formalism.BasicNotions Formalism.MainNotions

noncomputable section

namespace Formalism.L2.DIV.Cons

open Formalism.L2.DIV Formalism.L2.Rows

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}

theorem gamma_size_of_sizeData {Tk : TiedDataSK ex} {P : RowSideFamily ex} (hR : RowSideDetermined Tk P) (hTf : Finite P.T) (hSG : SizeG L)
    (hSC : SizeCond L) (Del h0 : ℕ) (Nc : ℝ) (hNc : 0 ≤ Nc) (C : ℝ) (hC : 0 ≤ C) (hF : FactDGam D C) :
    DGamSize P.A3.A P.P0 P.ψ0 (ofRecord D L Del h0) Nc hTf 1 (2 + 9 * C) :=
  dGamSize_record_one P.A3.A P.P0 P.ψ0 hTf L hSG hSC Del h0 Nc hNc P.tied.div.grp.card D.u₀ hR.gamDvd.2 C hC hF

end Formalism.L2.DIV.Cons
