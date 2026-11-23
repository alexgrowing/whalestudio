import Formalism.LocalToGlobal.Divisibility.RecBridge
import Formalism.LocalToGlobal.Divisibility.DivisibilityConstruction.ShiftOfColTie
import Formalism.LocalToGlobal.Divisibility.DivisibilityConstruction.RBNum
import Formalism.LocalToGlobal.Divisibility.RecBridgeNum
import Formalism.LocalToGlobal.Divisibility.SmallTies

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.L2.Indef

def DivisionPackageFace.ofOpen {D : D7} {L : SizeData₂ D} (Rw : DivisionRowsFace L) (C Cabs : ℝ)
    (Cp CHp : ℝ) (cf : ConvFace Rw.Bs) (Pk : IndefPkgR Rw.Am Rw.fc cf Cp CHp) (hZs : Pk.Zs = Rw.Zs)
    (hRows : HEq Pk.core.base.toIndefRows Rw.what₂)
    (wU : D.what₂.Word → (Rw.fc Pk.Zs).Dc.Mem)
    (eNu : ∀ u, (Fin ((Rw.fc Pk.Zs).Dc.a (wU u)) → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V)
    (eRR : (Fin Pk.core.cols.D → D.what₂.LL) ≃ₗ[D.what₂.LL] D.div.RR.V)
    (NuC : ∀ w, Submodule (𝓞 D.what₂.LL) (Fin ((Rw.fc Pk.Zs).Dc.a w) → D.what₂.LL))
    (hNu : ∀ u, HLatTie (D.div.Nu u) (NuC (wU u)) ((Rw.fc Pk.Zs).Dc.Xc (wU u)) (eNu u))
    (hRR : HLatTie D.div.RR Pk.core.cols.RR Pk.core.cols.XE eRR)
    (hBk : ∀ u x y, D.div.Bk u (eNu u x) (eRR y) = Pk.core.cols.col.B (wU u) x y)
    (tup : Rw.Bs.Tup → D.what₂.Tup) (eV : ∀ t, (Fin ((Rw.fc Pk.Zs).Df1.nV t) → D.what₂.LL) → D.what₂.Amb (tup t))
    (brTied : (Formalism.L2.G.ServJointF.ColBrF.mk Rw.Bs (Rw.fc Pk.Zs).Df1 (Rw.fc Pk.Zs).Dc wU (fun u x => eNu u x) tup eV
      Pk.core.cols.μ).Tied)
    (Del h0 : ℕ) (lam0 C0 ce Ch Sw C1 : ℝ) (eJ : Rw.Bs.J ≃ Fin D.R.m)
    (H : ∀ u, (ofRecord D L Del h0).NumFacts (letterOf D L Del h0 u) L.Nc lam0 C0 ce Ch Sw C1)
    (inp : ∀ u, DivInputs0R Pk.core
      (RecNums.ofNum (ofRecord D L Del h0) eJ (letterOf D L Del h0 u) ((D.mem u).A.T) L.Nc lam0 C0 ce Ch Sw C1 (H u))
      (wU u) (Cons.nuOf L u (eNu u)) (sgRec L u))
    (hN : NprimeDef D L) (Z : DivX D) (hk : ∀ σ, Z.kapR σ = Pk.core.cols.κ (InfinitePlace.mk σ))
    (tH : ∀ u, NumRecTieH (ofRecord D L Del h0) L u (letterOf D L Del h0 u) ((D.mem u).A.T) Del h0)
    (hh : ∀ u, D.div.h u = hExpl6 D L Z Ch u)
    (hF : FTie L ((Rw.fc Pk.Zs).Z.num Cp CHp) eJ)
    (hC0 : 0 ≤ C) (hC1 : 50 * C0 + 10 ≤ C) (hC2 : 60 * ce ≤ C) (hCabs : 1 ≤ Cabs) (hLa : 0 ≤ L.La) :
    DivisionPackageFace Rw C Cabs where
  Cp := Cp
  CHp := CHp
  cf := cf
  Pk := Pk
  hZs := hZs
  hRows := hRows
  wU := wU
  eNu := eNu
  eRR := eRR
  NuC := NuC
  hNu := hNu
  hRR := hRR
  hBk := hBk
  tup := tup
  eV := eV
  brTied := brTied
  Pl := RPl (ofRecord D L Del h0).R
  R u := RecNums.ofNum (ofRecord D L Del h0) eJ (letterOf D L Del h0 u) ((D.mem u).A.T) L.Nc lam0 C0 ce Ch Sw C1 (H u)
  Nu u := Cons.nuOf L u (eNu u)
  inp := inp
  shift u := Cons.shift_nuOf L hN u (eNu u) (NuC (wU u)) (hNu u).lat
  hTie u := hTie_of L Z Ch u Pk.core.cols.κ _ hk
    (hnum_of_numRecTieH (ofRecord D L Del h0) eJ (letterOf D L Del h0 u) ((D.mem u).A.T) L.Nc lam0 C0 ce Ch Sw C1 (H u) L u Del h0
      (tH u)) (hh u)
  foTie := two_FoOfR_eq_Fo L Pk.core eJ hF
  rhs u := rhs_le_record (ofRecord D L Del h0) eJ (letterOf D L Del h0 u) ((D.mem u).A.T) L.Nc lam0 C0 ce Ch Sw C1 (H u) L u
    (Cons.numRecTie_record L Del h0 u) C Cabs hC0 hC1 hC2 hCabs hLa

end Formalism.L2.DIV

end
