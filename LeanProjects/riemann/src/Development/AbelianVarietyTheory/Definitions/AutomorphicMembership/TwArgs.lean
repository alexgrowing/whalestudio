import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
  {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} (ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX)

abbrev famT {p0 : BaseLevelRowSide (w.D Z)} (t : RowsT K w Z Wt p0) := famR (w.st Z) w.I t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr

set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 4000000 in

structure TwArgs (t : RowsT K w Z Wt ex.p0) : Type 1 where
  Dc : ∀ Zs : DefSub (famT t).fam3.amb3, DefCols ((famT t).side3 t.r.z.F.P1 t.r.z.F.ψ1 Zs)
  Sp : ∀ Zs, SPer (Dc Zs)
  Zsc : DefSub (famT t).fam3.amb3 → IndefScale (famT t).fam3.base3
  lam : type_of% t.r.z.R.lam3
  err : type_of% t.r.z.R.err0
  lam_eq : ∀ i s p v, t.r.z.R.EEp3 p ≠ ⊥ → lam i s p v = t.r.z.R.lam3 i s p v
  x : TwIn ex
  pack : (⟨x.G, x.grp, x.fin, x.Pl0, x.I0, x.T, x.A3, x.core, x.alg, x.R, x.F, x.cG⟩ :
      Σ' (G : Type) (_ : Group G) (_ : Fintype G) (Pl0 I0 T0 : Type)
        (A3 : FamIn3 (w.st Z).toD7.what₂.LL G Pl0 I0 (List ℕ) T0 (w.st Z).toD7.R.m) (C : Formalism.L2.Pj.CoreJ (w.st Z).toD7)
        (_ : Algebra C.Q.c.F (w.st Z).toD7.what₂.LL) (R : RealDat3 (w.st Z).toD7 A3 C.Q.c.F) (_ : Face3 (w.st Z).toD7 A3),
        G0 R.Pg (w.st Z).toD7.R.r ≃* G0g (w.st Z).toD7.nd) =
    ⟨_, _, _, _, _, _, famT t, t.r.z.core, t.r.z.alg, (t.r.z.R.updS t.r.z.R.kap lam).withErr err, reFace t.r.z.F Dc Sp Zsc,
      (t.r.z.cG)⟩
  intersectionNumber_baseChange : Holds x.R x.F
  κ : HEq x.geo.κ t.r.z.geo.κ
  v₀ : HEq x.geo.v₀ t.r.z.geo.v₀
  fw : HEq x.geo.fw.e t.r.z.geo.fw.e
  tup : HEq x.Y.tup t.r.Y.tup
  tupT : HEq x.Y.tupT t.r.Y.tupT
  jA : HEq x.Y.jA t.r.Y.jA
  jA0 : HEq x.Y.jA0 t.r.Y.jA0
  eMt : HEq x.Y.eMt t.r.Y.eMt
  PY : HEq x.Y.PY t.r.Y.PY
  PW : HEq x.Y.PW t.r.Y.PW
  eFT : HEq x.Y.eFT t.r.Y.eFT
  IL : HEq x.Y.IL t.r.Y.IL
  eE : HEq x.Y.eE t.r.Y.eE
  eW : HEq x.Y.mj.eW t.r.Y.mj.eW
  jW : HEq x.Z.jW t.r.Z.jW
  eRR : HEq x.Z.eRR t.r.Z.eRR

end GlobalTheory.Mem.R3

end
