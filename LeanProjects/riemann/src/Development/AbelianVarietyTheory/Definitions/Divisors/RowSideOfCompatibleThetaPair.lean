import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseRankDimension

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT

open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.BigTop

namespace GlobalTheory.Fc.Ind

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}

@[reducible] def rowSideOfCompatibleThetaPair (P : RowSideFamily ex) : IndefiniteRowSideFullHecke ex where
  Gp := P.Gp
  Pl0 := P.Pl0
  I0 := P.I0
  T := P.T
  A3 := P.A3
  P0 := P.P0
  ψ0 := P.ψ0
  Ps := P.Ps
  ψs := P.ψs
  Zs := P.Zs
  S0 := P.S0
  S1 := P.S1
  Dc := P.Dc
  Sp := P.Sp
  C := P.C
  NuC := P.NuC
  I := P.I
  JA := P.JA
  JM := P.JM
  div := P.tied.div
  amb0 := P.tied.amb0
  mjH := P.tied.mjH
  cen0 := P.tied.cen0

abbrev zscOf (P : RowSideFamily ex) (Del h0 : ℕ) (c : ℝ) : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3 :=
  (rowSideOfCompatibleThetaPair P).zsc Del h0 c

variable {Rc : Formalism.L2.RecT ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc}

def ptOf (pin : RowSideDetermined Rc.T P) {Del h0 : ℕ} (hDel : D.s.Del = (Del : ℚ)) (hh0 : L.etaSz = (D.R.m : ℝ) * (h0 : ℝ)) {c : ℝ}
    (B : RealTB Rc P Dcf Spf (zscOf P Del h0 c) S) (Qp : RealPins B.Q) (Qr : RealRec B.Q) : PtAt ex c where
  P := rowSideOfCompatibleThetaPair P
  Del := Del
  h0 := h0
  hDel := hDel
  hh0 := hh0
  Dcf := Dcf
  Spf := Spf
  gamDvd := pin.gamDvd
  T := B.T
  alg := B.alg
  R := B.Q.Rl
  charW := B.Q.charW
  zs := B.Q.zs
  s0 := B.Q.s0
  s1 := B.Q.s1
  dc := B.Q.dc
  stdChar := B.Q.stdChar
  signs := B.Q.signs
  cG := B.Q.cG
  Sx := B.Q.Sx
  nexp := B.Q.nexp
  stdV := B.Q.stdV
  stdX := B.Q.stdX
  host := B.Q.host
  err_eq := B.Q.err_eq
  vpos := B.Q.vpos
  κ := B.κ
  v₀ := B.v₀
  fw := B.fw
  bar := B.bar
  O := B.O
  pins := B.pins
  rhoGeo := B.rhoGeo
  equivAll := B.equivAll
  cTie := B.cTie
  phase := B.phase
  qGuard := Qp.qGuard
  hF := Qp.hF
  phsOne := Qp.phsOne
  prXunit := Qp.prXunit
  grpRecPin := Qp.grpRecPin
  fdiag := Qp.fdiag
  eGtie := Qp.eGtie
  betaStd := Qp.betaStd
  tupT := Qr.tupT
  hm := Qr.hm
  Tp := Qr.Tp
  tupXi := Qr.recR.tupXi
  tupAt := Qr.recR.tupAt
  tupTie := Qr.tupTie
  tupT_tup := Qr.tupT_tup
  muEq := Qr.muEq

def Part.pt {D : D7} {O : Obj D} {c : ℝ} (b : Part D O c) : PtAt O.ex c :=
  ptOf b.pin b.DH.2.1 b.DH.2.2 b.B b.pins b.Rr

abbrev PtP : Type 1 := ∀ (D : D7) (O : Obj D) (c : ℝ), PtAt O.ex c → Prop

def onPt (G : PtP) : BdP Part := fun D O c b => G D O c b.pt

def PRows : BdP Part := fun _ _ _ b => b.pt.Rows

example {D : D7} {O : Obj D} {c : ℝ} (b : Part D O c) (C CH : ℝ) : L3 C CH D O c b ↔ (b.pt.S false).L3 (b.pt.N C CH) := Iff.rfl

example {D : D7} {O : Obj D} {c : ℝ} (b : Part D O c) : PNmj D O c b ↔ b.pt.ExportRow := Iff.rfl

end GlobalTheory.Fc.Ind

end
