import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RealIoX
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MovedReadingSameMapsBaseReadingAgrees

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI

section Tr

variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C) {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
  {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] {A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m}

abbrev HdB (R : RealDat a.D A Ks) : Type := @Hd b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R)

structure Same {R : RealDat a.D A Ks} (y : Hd R) (y' : HdB b R) : Prop where
  tup : letI := alg b iK; HEq y'.tup y.tup
  tupT : letI := alg b iK; HEq y'.tupT y.tupT
  PY : letI := alg b iK; HEq y'.PY.ψ y.PY.ψ
  PW : letI := alg b iK; HEq (fun i => (y'.PW i).ψ) fun i => (y.PW i).ψ

end Tr

section Univ

variable (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px)

def mAU (b : Bool) (a : I.ι) : Mat1 X.toD7.what₂.LL (Gc X.B px) :=
  rMat (D := X.toD7) (famR X I hX Set.univ Xg tr).A (levP (face0 X I hX Set.univ Xg tr).lv2 b).1
    (levP (face0 X I hX Set.univ Xg tr).lv2 b).2 (tAll I a)

def mLU (a : I.ι) (j : ℕ) : Mat1 X.toD7.what₂.LL (Gc X.B px) :=
  if h : 1 ≤ j ∧ j ≤ X.toD7.R.m then
    lMat (D := X.toD7) (famR X I hX Set.univ Xg tr).A (face0 X I hX Set.univ Xg tr).lv2.P0 (face0 X I hX Set.univ Xg tr).lv2.ψ0
      ⟨j - 1, by omega⟩ (tAll I a)
  else Mat1.zero _ _

end Univ

variable {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T)

structure PerT (Z : w.Lt) (hX : B.fields.Ok) (Xg : Finset (Gc B w.px → B.LL)) (tr : TrI B w.px) (p : PkB B w.C (Gc B w.px))
    (j : ∀ a : w.I.ι, (Fin (mAU (w.st Z) w.I hX Xg tr true a).n → B.LL) → (p.sA true a).A.T) (d : PerD p) : Type where
  e : ∀ a : w.C.Tup, Df.MtCx w.I a ≃ₗ[ℂ] (p.sA true a).A.T
  ref : ∀ u F, Df.SameForm w.I w.l u w.I.mu0 F ((d.e0 u).symm (e w.C.mu0 F))
  tw : ∀ u (a : w.C.Tup) F, Df.SameForm w.I w.l u a F ((d.eT u a).symm (e a F))
  crd : ∀ (a : w.C.Tup) y, IsCrd w.I hX a (e a)
    (rowForm (D := (w.st Z).toD7) (famR (w.st Z) w.I hX Set.univ Xg tr).A (lev1 w.I) (chr1 w.I) (tAll w.I a) y) (j a y)

variable {w} in

def CoreP {Z : w.Lt} {hX : B.fields.Ok} {Wt : Set B.places.Pl} (z : Dat (w.st Z) w.I hX T Wt) : Prop :=
  Formalism.L2.Pj.LawsCore z.core.toCore ∧ z.core.Q.Canon ∧ (∀ j, 1 ≤ (z.core.Q.Dw j).p + (z.core.Q.Dw j).q) ∧ z.core.pb = f.P.pb

open Classical in

structure MuW (Wt : Set B.places.Pl) (W : RowsRest B w.C) : Prop where
  tw : ∀ v, w.I.xi (W.muTw v) = T.xiTw f v
  on : ∀ v, v ∈ Wt → W.muAt v = W.muTw v
  off : ∀ v, v ∉ Wt → W.muAt v = w.C.mu0

set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 2000000 in

structure RowPk {Z₀ : w.Lt} {hX : B.fields.Ok} {Wt : Set B.places.Pl} (z : Dat (w.st Z₀) w.I hX T Wt) : Type 1 where
  y : Hd z.R.toRealDat
  tup : ∀ t, y.tup t = ixOf w.I (usedOf w.I T Wt) t
  p : PkB B w.C (Gc B w.px)
  t : PkT z.F y (mAU (w.st Z₀) w.I hX z.Xg z.tr) p
  mL : ∀ a j, p.mL a j = mLU (w.st Z₀) w.I hX z.Xg z.tr a j
  e : PerD p
  per : PerT w Z₀ hX z.Xg z.tr p (fun a x => (t.tA true a).j x) e
  W₀ : RowsRest B w.C
  mu : MuW w Wt W₀
  sha : GlobalTheory.MemN.ShaOK B.toPre W₀.shaLen
  n : Nums p W₀
  kap : ∀ η hη V S N G, DV.KapDef (assemble B w.C (p.what₂ e W₀ n η hη) V S N G)
  num : ∀ η hη V S N G, NumOK (assemble B w.C (p.what₂ e W₀ n η hη) V S N G)

variable {w} {Z₀ : w.Lt} {hX : B.fields.Ok} {Wt : Set B.places.Pl} {z₀ : Dat (w.st Z₀) w.I hX T Wt} (q : RowPk w z₀)

abbrev RowPk.W (η : ℕ → B.places.Pl → ℚ) (hη : ∀ j v, 0 ≤ η j v) : RowsRest B w.C := q.p.what₂ q.e q.W₀ q.n η hη

def RowPk.eta (_q : RowPk w z₀) : ℕ → B.places.Pl → ℚ := etaOf z₀.R z₀.F

structure RowPk.Over : Type 1 where
  η : ℕ → B.places.Pl → ℚ
  hη : ∀ j v, 0 ≤ η j v
  V : DivStage B w.C (q.W η hη)
  S : SStage B w.C (q.W η hη)
  N : NStage B w.C (q.W η hη)
  G : GJStage B w.C

variable {q}

abbrev RowPk.Over.Z (o : q.Over) : w.Lt := ⟨q.W o.η o.hη, o.V, o.S, o.N, o.G⟩

def StdIso (X : Stages) (px : PreX X.B.toPre) (eR : Gc X.B px ≃* G0g X.toD7.nd) : Prop :=
  ∃ (plg : (Σ k : Fin 2, X.toD7.nd.PlG k) ≃ (X.B.primes px).vGs)
    (iso : ∀ kv : (Σ k : Fin 2, X.toD7.nd.PlG k), ZMod (X.toD7.host.g kv.1) ≃+* kP (plg kv).1),
    (∀ kv, ((plg kv).1 : Pl X.toD7.host.E) = X.toD7.naut.plGw kv.1 kv.2) ∧
    ∀ g kv, g (plg kv) = Formalism.UG.bc (iso kv : ZMod (X.toD7.host.g kv.1) →+* kP (plg kv).1) (eR g kv)

structure RowPk.Over.Fits (o : q.Over) : Prop where
  div : DivIs q.p o.V
  grp : GrpTrue o.N f
  grpAt : GrpAt (w.st o.Z) w.I
  cen : ∀ eR, StdIso (w.st o.Z) w.px eR → CenIs q.p o.N eR

structure Side0 (o : q.Over) : Type 1 where
  cen : ∀ μ, Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (w.D o.Z).nd)) →ₐ[ℂ] Module.End ℂ (q.p.sA false μ).A.T
  tie : ∀ μ, (q.p.sA false μ).e = (open Classical in
    if h : (w.D o.Z).ntypes.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (w.D o.Z).nd)) then cen μ ⟨(w.D o.Z).ntypes.e0, h⟩ else 0)
  is : ∀ eR, StdIso (w.st o.Z) w.px eR → ∀ μ (c : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (w.D o.Z).nd)))
    (c' : Subalgebra.center ℂ (MonoidAlgebra ℂ (Gc B w.px))),
    (∀ g, (c' : MonoidAlgebra ℂ (Gc B w.px)).coeff g = (c : MonoidAlgebra ℂ (G0g (w.D o.Z).nd)).coeff (eR g)) →
      ∀ x, cen μ c x = (q.p.sA false μ).act c' x
  RR : HLat B.LL
  frames : ∀ v, IsUnit (RR.X v).det
  jEE : RR.V →ₛₗ[B.embLL] (q.p.ch false).EE.T
  basis : LinearIndependent ℂ (fun i => jEE (RR.b i)) ∧ Submodule.span ℂ (Set.range (fun i => jEE (RR.b i))) = ⊤
  norm : ∀ x : RR.V, Formalism.HermitianLatticesTheory.normAt RR.b RR.X (InfinitePlace.mk B.embLL) x = ‖jEE x‖

@[reducible] def Side0.p0 {o : q.Over} (s : Side0 o) : BaseLevelRowSide (w.D o.Z) :=
  ⟨{ Amb := fun μ => (q.p.sA false μ).A.T
     instAmb := fun μ => (q.p.sA false μ).A.nacg
     instAmbi := fun μ => (q.p.sA false μ).A.ips
     instAmbf := fun μ => (q.p.sA false μ).A.fd
     Mult := fun μ j => ((q.p.ch false).Mult μ j).T
     instMult := fun μ j => ((q.p.ch false).Mult μ j).nacg
     instMulti := fun μ j => ((q.p.ch false).Mult μ j).ips
     instMultf := fun μ j => ((q.p.ch false).Mult μ j).fd
     multZero := (q.p.ch false).multZero
     multTop := (q.p.ch false).multTop
     io := (q.p.ch false).io
     Mtilde := fun μ => (q.p.sA false μ).lat
     cen := s.cen
     eOp := fun μ => (q.p.sA false μ).e
     eOp_idem := fun μ => (q.p.sA false μ).idem
     eOp_sa := fun μ => (q.p.sA false μ).sa
     eOp_tie := s.tie
     RR := s.RR
     RR_frames := s.frames
     jEE := s.jEE
     jEE_basis := s.basis
     jEE_norm := s.norm }⟩

set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 4000000 in

structure Moved (o : q.Over) : Type 1 where
  z : Dat (w.st o.Z) w.I hX T Wt
  intersectionNumber_baseChange : Holds z.R z.F
  exAt : z.R.toRealDat.ExAt
  inGeo : GlobalTheory.RealGeo.InGeo z.geo
  Xg : z.Xg = z₀.Xg
  tr : z.tr = z₀.tr
  core : CoreP z₀ → CoreP z
  eta : ∀ j v, etaOf z.R z.F j v = q.eta j v
  W1 : ∀ F0, z.W1 F0 = z₀.W1 F0
  y : Hd z.R.toRealDat
  tup : ∀ t, y.tup t = ixOf w.I (usedOf w.I T Wt) t
  t : PkT z.F y (mAU (w.st o.Z) w.I hX z.Xg z.tr) q.p
  tA : ∀ b a, HEq (t.tA b a).j (q.t.tA b a).j

set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 4000000 in

structure ReadPk {o : q.Over} (m : Moved o) (s : Side0 o) : Type 1 where
  Y : Read m.z.R.toRealDat m.z.F.lv2 s.p0
  Z : RationalReadingWithoutCongruence m.z.R m.z.F s.p0 Y
  tup : Y.tup = m.y.tup
  tupT : Y.tupT = m.y.tupT
  PY : Y.PY = m.y.PY
  PW : Y.PW = m.y.PW
  jA : ∀ t, HEq (Y.jA t) ((m.t.tA true (m.y.tup t)).cast (m.t.hA true t)).j
  jA0 : ∀ t, HEq (Y.jA0 t) ((m.t.tA false (m.y.tup t)).cast (m.t.hA false t)).j
  eMt : ∀ (i : Fin (w.D o.Z).R.m) t x, HEq (Y.eMt i t x) x

end GlobalTheory.Mem.R3.Rw

end
