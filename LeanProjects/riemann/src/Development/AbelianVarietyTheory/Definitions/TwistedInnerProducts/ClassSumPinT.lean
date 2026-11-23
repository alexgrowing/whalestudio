import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.RealTB
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.Rows

namespace GlobalTheory.ExportPin

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
  {Rc : Formalism.L2.RecT ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

set_option synthInstance.maxHeartbeats 400000 in

def ClassSumPinT (Q : RealT Rc P Dcf Spf Zscf S Ks) : Prop :=
  ∀ (w : D.what₂.places.Pl) (i : Fin D.R.m) (h1 : 1 ≤ (i : ℕ) + 1) (h2 : (i : ℕ) + 1 ≤ D.R.m) (t : P.T)
    (ht : P.I.tup t = D.what₂.muTw w), D.what₂.muAt w ≠ D.what₂.mu0 →
    ∀ (c : Fin (lDim D P.A3.A P.P0 P.ψ0 i t) → D.what₂.LL) (x : D.what₂.MtL (D.what₂.muTw w) ((i : ℕ) + 1)),
      x = ht ▸ P.I.eMt i t c → x ∈ Idx.TjV D (D.what₂.muTw w) ((i : ℕ) + 1) →
    ∀ (y : Fin (Module.finrank D.what₂.LL (Q.Rl.toRealDat.WL Q.F.lv2 false i)) → D.what₂.LL),
      HEq (((P.A3.indefDown P.S0).θ i t).mulVec
        ((lPrj D P.A3.A P.P0 P.ψ0 (P.A3.fam3.toSub2 P.Zs) i t).mulVec c)) y →
    ∀ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK Q.Sx ((i : ℕ) + 1)),
      (Q.nexp.fi i).e (∑ k, a k • (show ↥(Q.Sx.A ((i : ℕ) + 1)).WK from f k).1) = jDL Q.Rl Q.F.lv2 i y →
      NChoice.thPe D ex.nch w ((i : ℕ) + 1) (ex.nch.eMt w ((i : ℕ) + 1) x) =
        ∑ k, ex.nch.embW w (a k) ⊗ₜ[D.ntw.O (ex.nch.twI w)]
          (Q.nexp.eF (ex.nch.twI w) ((i : ℕ) + 1) (ex.nch.sd w) h1 h2).symm
            ((1 : KB Q.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[Q.Sx.Ks] f k)

end GlobalTheory.ExportPin
