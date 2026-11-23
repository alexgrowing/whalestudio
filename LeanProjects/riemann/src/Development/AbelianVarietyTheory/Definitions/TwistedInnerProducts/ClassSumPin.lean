import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BigTop

namespace GlobalTheory.ExportPin

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

set_option synthInstance.maxHeartbeats 400000 in

def ClassSumPin (p : PtAt ex Csz) : Prop :=
  ∀ (w : D.what₂.places.Pl) (i : Fin D.R.m) (h1 : 1 ≤ (i : ℕ) + 1) (h2 : (i : ℕ) + 1 ≤ D.R.m) (t : p.P.T)
    (ht : p.P.I.tup t = D.what₂.muTw w), D.what₂.muAt w ≠ D.what₂.mu0 →
    ∀ (c : Fin (lDim D p.P.A3.A p.P.P0 p.P.ψ0 i t) → D.what₂.LL) (x : D.what₂.MtL (D.what₂.muTw w) ((i : ℕ) + 1)),
      x = ht ▸ p.P.I.eMt i t c → x ∈ Idx.TjV D (D.what₂.muTw w) ((i : ℕ) + 1) →
    ∀ (y : Fin (Module.finrank D.what₂.LL (p.R.toRealDat.WL p.F.lv2 false i)) → D.what₂.LL),
      HEq (((p.P.A3.indefDown p.P.S0).θ i t).mulVec
        ((lPrj D p.P.A3.A p.P.P0 p.P.ψ0 (p.P.A3.fam3.toSub2 p.P.Zs) i t).mulVec c)) y →
    ∀ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK p.Sx ((i : ℕ) + 1)),
      (p.nexp.fi i).e (∑ k, a k • (show ↥(p.Sx.A ((i : ℕ) + 1)).WK from f k).1) = jDL p.R p.F.lv2 i y →
      NChoice.thPe D ex.nch w ((i : ℕ) + 1) (ex.nch.eMt w ((i : ℕ) + 1) x) =
        ∑ k, ex.nch.embW w (a k) ⊗ₜ[D.ntw.O (ex.nch.twI w)]
          (p.nexp.eF (ex.nch.twI w) ((i : ℕ) + 1) (ex.nch.sd w) h1 h2).symm
            ((1 : KB p.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[p.Sx.Ks] f k)

end GlobalTheory.ExportPin
