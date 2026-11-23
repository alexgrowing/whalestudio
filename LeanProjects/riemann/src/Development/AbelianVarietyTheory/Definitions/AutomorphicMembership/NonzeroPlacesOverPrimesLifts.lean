import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReadPk
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
import BuildAid.D3

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI

variable {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z₀ : w.Lt} {hX : B.fields.Ok} {Wt : Set B.places.Pl}
  {z₀ : Dat (w.st Z₀) w.I hX T Wt} {q : RowPk w z₀} {o : q.Over}

structure Moved.Copy (m : Moved o) : Prop where
  core : HEq m.z.core (coreJ (a := ⟨Z₀.W, Z₀.V, Z₀.S, Z₀.N, Z₀.G⟩) ⟨q.W o.η o.hη, o.V, o.S, o.N, o.G⟩ z₀.core)
  R : HEq m.z.R (real3 (a := ⟨Z₀.W, Z₀.V, Z₀.S, Z₀.N, Z₀.G⟩) ⟨q.W o.η o.hη, o.V, o.S, o.N, o.G⟩ (iK := z₀.alg) z₀.R)

structure Moved.Coh (m : Moved o) : Prop where
  tupT : HEq m.y.tupT q.y.tupT
  PY : HEq m.y.PY.ψ q.y.PY.ψ
  PW : HEq (fun i => (m.y.PW i).ψ) fun i => (q.y.PW i).ψ
  rep : HEq m.t.rep q.t.rep
  jE : ∀ b, HEq (m.t.ch b).jE (q.t.ch b).jE
  jM : ∀ b, HEq (m.t.ch b).jM (q.t.ch b).jM
  jX : ∀ b, HEq (m.t.ch b).jX (q.t.ch b).jX
  eW : HEq m.t.lf.eW q.t.lf.eW
  jMt : HEq m.t.lf.jMt q.t.lf.jMt

structure ReadPk.Pin {m : Moved o} {s : Side0 o} (r : ReadPk m s) : Prop where
  rep : ∀ π, (principalLevelFrame.rowRepR m.z.R.θ (r.Y.eFT π)).Iso (m.t.rep π)
  jE : ∀ x, HEq (r.Y.Ish.jE x).1 ((m.t.ch true).jE x)
  heq_eigen_embedding_zero : ∀ x, HEq (r.Y.Iz.jE x).1 ((m.t.ch false).jE x)
  eW : ∀ i x, HEq (r.Y.mj.eW i x) (m.t.lf.eW i x)
  jMt : ∀ μ h i x, HEq (r.Y.IL.jMt μ h i x).1 (m.t.lf.jMt μ i x)

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure Pre2 (K : Ctx) (w : ColW B f T) : Type 1 where
  Z₀ : w.Lt
  hX : B.fields.Ok
  Wt : Set B.places.Pl
  z : Dat (w.st Z₀) w.I hX T Wt
  q : RowPk w z
  g : GIs2 K w Z₀.G
  coh : Coh B T
  grp : GrpTrue Z₀.N f
  grpAt : GrpAt (w.st Z₀) w.I
  kap : DV.KapDef (w.D Z₀)
  intersectionNumber_baseChange : Holds z.R z.F
  exAt : z.R.toRealDat.ExAt
  inGeo : GlobalTheory.RealGeo.InGeo z.geo
  core : CoreP z
  exact : Wt = z.W1 (F0K K.s (w.D Z₀))
  sub : ∀ v ∈ Wt, B.places.resChar v ∈ T.pl
  supp : ∀ v, v ∉ Wt → T.psi v = 1
  std : z.Std

def HasPk : WP := fun K _ _ _ w => Nonempty (Pre2 K w)

structure HoldsL {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) : Prop where
  heckeR : ∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint
  heckeL : ∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint
  hecke : R.PHecke F
  gUnit : R.PGUnit F
  gEquiv : R.PGEquiv F
  block : (R.toCx3 F).zs.InBlock
  liftTest : Formalism.IndefR.Rat.LiftTest (R.toCx3 F)
  liftTestB : Formalism.IndefR.Rat.LiftTestB (R.toCx3 F) false
  liftOnto : ∀ hW, HeckeIntertwiningLifts A3 (R.toCx3 F) hW → U2.OntoC A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 hW
  unif : R.toRealDat.LUnif
  mLat : (R.toCx3 F).MLat false
  levW : R.PLevW F
  thmA : R.PThmA
  sumW : (R.toCx3 F).PartsW false
  aux : UnusedChoiceStatements R F
  ok : A3.fam3.Ok3 1
  sep : A3.fam3.TypesSep3

theorem HoldsL.of_holds {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} (h : Holds R F) :
    HoldsL R F :=
  ⟨h.prim.heckeR, h.prim.heckeL, h.prim.hecke, h.prim.gUnit, h.prim.gEquiv, h.prim.block, h.prim.liftTest, h.prim.liftTestB,
    h.prim.liftOnto, h.prim.unif, h.prim.mLat, h.prim.levW, h.prim.thmA, h.prim.sumW, h.aux, h.ok, h.sep⟩

def LowerUnitaryCaseCondition : Prop := GroupRetwisting.Step KPx (fun _ _ _ _ => True) fun K B f T => ∀ w : ColW B f T, Pinned K B f T w →
  ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I →
    z.R.toRealDat.ExAt → GlobalTheory.RealGeo.InGeo z.geo → HoldsL z.R z.F

def NonzeroPlacesOverPrimesLifts : Prop := StepW Pinned fun K B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
  (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → DV.KapDef (w.D Z) →
    HoldsL z.R z.F → ∀ v ∈ z.W1 (F0K K.s (w.D Z)), B.places.resChar v ∈ T.pl

def WeightCaseCondition : Prop := StepW Start fun K B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
  (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → DV.KapDef (w.D Z) → z.R.toRealDat.ExAt →
    GlobalTheory.RealGeo.InGeo z.geo → CoreP z → GIs2 K w Z.G → Wt = z.W1 (F0K K.s (w.D Z)) → (∀ v ∈ Wt, B.places.resChar v ∈ T.pl) →
    Holds z.R z.F

def BkLaw (D : D7) : Prop := WeightDegreeSizes.RationalMapValues D → D.BuRational

structure St {K : Ctx} (P : Pre2 K w) : Type 1 where
  o : P.q.Over
  fits : o.Fits
  G_eq : o.G = P.Z₀.G
  etaF : o.V.div.etaF = 6 * K.s.x ^ (-K.C.P.CF)
  bk : BkLaw (w.D o.Z)
  m : Moved o
  copy : m.Copy
  coh : m.Coh
  s : Side0 o
  r : ReadPk m s
  pin : r.Pin

def HasBare : WP := fun K _ _ _ w => ∃ (P : Pre2 K w) (x : St P), IsEmpty x.o.N.nd.Loc ∧ ∀ j v, x.o.η j v = 0

structure RowsSame {K : Ctx} {Z Z' : w.Lt} {p0 : BaseLevelRowSide (w.D Z)} {p0' : BaseLevelRowSide (w.D Z')} (t : RowsT K w Z Wt p0)
    (t' : RowsT K w Z' Wt p0') : Prop where
  Xg : t'.r.z.Xg = t.r.z.Xg
  tr : t'.r.z.tr = t.r.z.tr
  core : HEq t'.r.z.core (coreJ (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) ⟨Z'.W, Z'.V, Z'.S, Z'.N, Z'.G⟩ t.r.z.core)
  R : HEq t'.r.z.R (real3 (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) ⟨Z'.W, Z'.V, Z'.S, Z'.N, Z'.G⟩ (iK := t.r.z.alg) t.r.z.R)
  cG : HEq t'.r.z.cG t.r.z.cG
  tup : HEq t'.r.Y.tup t.r.Y.tup
  tupT : HEq t'.r.Y.tupT t.r.Y.tupT
  PY : HEq t'.r.Y.PY.ψ t.r.Y.PY.ψ
  PW : HEq (fun i => (t'.r.Y.PW i).ψ) fun i => (t.r.Y.PW i).ψ
  rep : HEq (fun π => principalLevelFrame.rowRepR t'.r.z.R.θ (t'.r.Y.eFT π)) fun π => principalLevelFrame.rowRepR t.r.z.R.θ (t.r.Y.eFT π)
  jE : HEq (fun x => (t'.r.Y.Ish.jE x).1) fun x => (t.r.Y.Ish.jE x).1
  heq_eigen_embedding_zero : HEq (fun x => (t'.r.Y.Iz.jE x).1) fun x => (t.r.Y.Iz.jE x).1
  eE : HEq t'.r.Y.eE t.r.Y.eE
  jA : HEq t'.r.Y.jA t.r.Y.jA
  jA0 : HEq t'.r.Y.jA0 t.r.Y.jA0
  eMt : HEq t'.r.Y.eMt t.r.Y.eMt
  eW : HEq t'.r.Y.mj.eW t.r.Y.mj.eW
  jW : HEq t'.r.Z.jW t.r.Z.jW
  eRR : HEq t'.r.Z.eRR t.r.Z.eRR
  eRR0 : HEq t'.r.Z.eRR0 t.r.Z.eRR0

def p0To {Z : w.Lt} (p0 : BaseLevelRowSide (w.D Z)) (S : SStage B w.C Z.W) (G : GJStage B w.C) : BaseLevelRowSide (w.D ⟨Z.W, Z.V, S, Z.N, G⟩) :=
  ⟨{ Amb := p0.s.Amb
     instAmb := p0.s.instAmb
     instAmbi := p0.s.instAmbi
     instAmbf := p0.s.instAmbf
     Mult := p0.s.Mult
     instMult := p0.s.instMult
     instMulti := p0.s.instMulti
     instMultf := p0.s.instMultf
     multZero := (by with_unfolding_all exact (p0.s.multZero :))
     multTop := (by with_unfolding_all exact (p0.s.multTop :))
     io := (by with_unfolding_all exact (p0.s.io :))
     Mtilde := (by with_unfolding_all exact (p0.s.Mtilde :))
     cen := (by with_unfolding_all exact (p0.s.cen :))
     eOp := (by with_unfolding_all exact (p0.s.eOp :))
     eOp_idem := (by with_unfolding_all exact (p0.s.eOp_idem :))
     eOp_sa := (by with_unfolding_all exact (p0.s.eOp_sa :))
     eOp_tie := (by with_unfolding_all exact (p0.s.eOp_tie :))
     RR := p0.s.RR
     RR_frames := (by with_unfolding_all exact (p0.s.RR_frames :))
     jEE := (by with_unfolding_all exact (p0.s.jEE :))
     jEE_basis := (by with_unfolding_all exact (p0.s.jEE_basis :))
     jEE_norm := (by with_unfolding_all exact (p0.s.jEE_norm :)) }⟩

end GlobalTheory.Mem.R3.Rw

end
