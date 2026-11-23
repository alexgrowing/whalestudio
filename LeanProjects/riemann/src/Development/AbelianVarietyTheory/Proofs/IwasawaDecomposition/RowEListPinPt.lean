import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.GoodPairSystems
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowRatW
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyGrid
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LiteralAutomorphy.PinPt

open Formalism.L2.Host Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev

theorem listPin_twArgs {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
    {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}
    {t : RowsT K w Z Wt ex.p0} (a : GlobalTheory.Mem.R3.TwArgs ex t) {CF bb : ℝ}
    (h : GlobalTheory.HeightCounting.Up.ListPin (w.st Z).toD7 t.r.z.R.toRealDat.toLevCh CF bb) :
    GlobalTheory.HeightCounting.Up.ListPin (w.st Z).toD7 a.x.R.toRealDat.toLevCh CF bb := by
  have e := congrArg (fun s : Σ' (G : Type) (_ : Group G) (_ : Fintype G) (Pl0 I0 T0 : Type)
        (A3 : FamIn3 (w.st Z).toD7.what₂.LL G Pl0 I0 (List ℕ) T0 (w.st Z).toD7.R.m) (C : Formalism.L2.Pj.CoreJ (w.st Z).toD7)
        (_ : Algebra C.Q.c.F (w.st Z).toD7.what₂.LL) (R : RealDat3 (w.st Z).toD7 A3 C.Q.c.F) (_ : Face3 (w.st Z).toD7 A3),
        G0 R.Pg (w.st Z).toD7.R.r ≃* G0g (w.st Z).toD7.nd =>
      match s with
      | ⟨_, _, _, _, _, _, _, _, _, R, _, _⟩ => GlobalTheory.HeightCounting.Up.ListPin (w.st Z).toD7 R.toRealDat.toLevCh CF bb) a.pack
  exact cast e.symm h

theorem listPin_rpk {D : D7} {O : Obj D} {R : Formalism.L2.RecT O.ex} {S : Formalism.L2.SG.SpectralTiesReal.STiesR R} {x : GlobalTheory.Mem.R3.TwIn O.ex}
    (y : GlobalTheory.Mem.R3.RealIn x R S) (r : RPk R S) (hr : r = rpkX y) {CF bb : ℝ}
    (h : GlobalTheory.HeightCounting.Up.ListPin D x.R.toRealDat.toLevCh CF bb) : GlobalTheory.HeightCounting.Up.ListPin D r.B.Q.Rl.toRealDat.toLevCh CF bb := by
  subst hr
  exact h

end GlobalTheory.Mem.LiteralAutomorphy.PinPt
