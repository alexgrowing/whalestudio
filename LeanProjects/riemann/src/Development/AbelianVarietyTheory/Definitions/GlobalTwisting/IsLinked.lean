import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ColumnCompatibleSelection
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToSTiesRPin
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
import Formalism.LocalToGlobal.CarriedPlMap
import Formalism.LocalToGlobal.SelSideN
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DivRows3GIff
import Formalism.LocalToGlobal.Divisibility.ColPins

noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Pack

open Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure RPk {D : D7} {O : Obj D} (R : Formalism.L2.RecT O.ex) (S : Formalism.L2.SG.SpectralTiesReal.STiesR R) : Type 1 where
  P : RowSideFamily O.ex
  Dc : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)
  Sp : ∀ Zs, SPer (Dc Zs)
  Zsc : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3
  B : RealTB R P Dc Sp Zsc S

def rpkB {D : D7} {O : Obj D} {c : ℝ} (b : GlobalTheory.Fc.Bundle D O c) : RPk b.R b.S :=
  ⟨b.P, b.C.c.face, b.C.Sp, GlobalTheory.Fc.zsc b.P b.DH.1.1 b.DH.1.2 c, b.B⟩

def rpkX {D : D7} {O : Obj D} {R : Formalism.L2.RecT O.ex} {S : Formalism.L2.SG.SpectralTiesReal.STiesR R} {x : R3.TwIn O.ex} (y : R3.RealIn x R S) :
    RPk R S := ⟨R3.divisionPairOfAdelicFormsFaceColumnsData x, x.F.Dc, x.F.Sp, x.F.Zsc, R3.realTBOf y⟩

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure BTw {D : D7} {O : Obj D} {c : ℝ} (b : GlobalTheory.Fc.Bundle D O c) (x : R3.TwIn O.ex) : Type 1 where
  intersectionNumber_baseChange : R3.Holds x.R x.F
  y : R3.RealIn x b.R b.S
  r : R3.RecIn y
  eq : rpkB b = rpkX y
  HD : Formalism.L2.HostDatumC b.R.T.toTiedDataS

end Pack

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Prm hL} {K : Ctx}

def WPt.sat (q : WPt p.s K) :
    SAt (D := (q.w.st q.Z).toD7) q.x.what₂.r.z.R.toRealDat q.x.what₂.r.z.F.lv2 q.x.what₂.r.Y.eE fun u => (q.x.col.C.forms u).to0 := q.x.sx.1

set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 1000000 in

structure BWit (q : WPt p.s K) {c : ℝ} (b : GlobalTheory.Fc.Bundle (q.w.D q.Z) q.O c) : Type 1 where
  x : R3.TwIn q.O.ex
  a : R3.TwArgs q.O.ex q.x.what₂
  ax : HEq a.x x
  y : BTw b x
  recPin : RecPinE q b.R
  s : ∃ (sP : GlobalTheory.Mem.SRe.SPack (q.w.D q.Z) fun u => (b.R.T.cols.forms u).to0) (sS : GlobalTheory.Mem.SRe.SRest sP),
    HEq sP q.sat.P ∧ HEq sS q.sat.S ∧ b.S = sS.toSTiesR b.R
  pt : HEq y.y.tS q.sat.t ∧ y.y.cS = q.sat.c
  sx : HEq y.y.Sx (Formalism.IndefR.NX.ratDatR (D := (q.w.st q.Z).toD7) q.x.what₂.r.z.R q.x.what₂.r.z.cG q.core.row.kKs q.core.row.hk)
  eF : HEq y.y.nexp.eF q.core.row.nexp.eF
  fi : HEq y.y.nexp.fi q.core.row.nexp.fi
  uS : y.y.uS = 1
  parts : (R3.realRecOf y.r).PartsRow
  cW : HEq b.C.c.W q.B.wts ∧ HEq b.C.c.Xg q.x.what₂.r.z.Xg
  d3b : HEq y.HD.d3b q.x.pin.d3b
  side : Formalism.L2.SelSideRT b.R (R3.divisionPairOfAdelicFormsFaceColumnsData x) (R3.realTOf y.y) (R3.realRecOf y.r) y.HD q.core.a.Pq
  colPins : Formalism.L2.DIV.ColPins b.C.toS

def IsLinked (p : Prm hL) : GlobalTheory.Fc.LkT GlobalTheory.Fc.Bundle :=
  linkOf (𝒮 := p.s) (Bd := GlobalTheory.Fc.Bundle) fun _ q _ b => Nonempty (BWit (p := p) q b)

def BunU (p : Prm hL) : Prop :=
  GlobalTheory.Fc.EvP fun _ K => ∀ (q : WPt p.s K) (R : Formalism.L2.RecT q.O.ex), RecPinE q R → ∀ (c : ℝ)
    (_ : {n : ℕ × ℕ // (q.w.D q.Z).s.Del = (n.1 : ℚ) ∧ q.O.L.etaSz = ((q.w.D q.Z).R.m : ℝ) * (n.2 : ℝ)}),
    q.O.L.sc = K.s → Val K.C K.cD K.ch q.O.L → ∃ b : GlobalTheory.Fc.Bundle (q.w.D q.Z) q.O c, b.R = R ∧ Nonempty (BWit q b)

end GlobalTheory.Mem.Top.Bl

end
