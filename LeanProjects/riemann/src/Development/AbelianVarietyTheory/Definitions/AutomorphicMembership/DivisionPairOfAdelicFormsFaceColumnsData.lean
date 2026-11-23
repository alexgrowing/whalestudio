import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Formalism.LocalToGlobal.IndefiniteReal.RealTB
import Formalism.LocalToGlobal.IndefiniteReal.RealRec
import Formalism.LocalToGlobal.IndefiniteReal.RealPins
import Formalism.LocalToGlobal.IndefiniteReal.RealRecPins
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev

namespace GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts} {Yd : DivX D}
  {cX : ExtraC}

set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 2000000 in

structure TwIn (ex : Extra D L hT Gi Gl K Yd cX) : Type 1 where
  G : Type
  [grp : Group G]
  [fin : Fintype G]
  Pl0 : Type
  I0 : Type
  T : Type
  A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m
  core : Formalism.L2.Pj.CoreJ D
  [alg : Algebra core.Q.c.F D.what₂.LL]
  R : RealDat3 D A3 core.Q.c.F
  F : Face3 D A3
  cG : G0 R.Pg D.R.r ≃* G0g D.nd
  geo : GlobalTheory.RealGeo.GeoHalf core R.toRealDat fun _ => 1
  pins : Pins R F cG
  err : ErrEq R F
  Y : Read (A3 := A3) R.toRealDat F.lv2 ex.p0
  Z : ReadL R F ex.p0 Y
  C : ReadC R F ex.p0 Y
  sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH
  div : DivDef3 D A3 F.P0 F.ψ0 F.P1 F.ψ1 (zsOf R F) (s0Of R F) (s1Of R F) ex.p0 (colOf R F sEE) C.NuC (idsOf cG Z C)
  JA : AmbIds D A3.A ex.p0.s ex.amb0 F.P0 F.ψ0 Y.tup
  amb0 : AmbTie D A3.A ex.p0.s ex.amb0 F.P0 F.ψ0 Y.tup Y.jA0 JA
  JM : MjHIds D A3.A Yd (A3.indefDown (s0Of R F))
  mjH : MjHTie D A3.A Yd (A3.indefDown (s0Of R F)) Z.jW JM

attribute [instance] TwIn.grp TwIn.fin TwIn.alg

variable {ex : Extra D L hT Gi Gl K Yd cX}

set_option maxHeartbeats 2000000 in

@[reducible] def divisionPairOfAdelicFormsFaceColumnsData (x : TwIn ex) : RowSideFamily ex where
  Gp := x.G
  Pl0 := x.Pl0
  I0 := x.I0
  T := x.T
  A3 := x.A3
  P0 := x.F.P0
  ψ0 := x.F.ψ0
  Ps := x.F.P1
  ψs := x.F.ψ1
  Zs := zsOf x.R x.F
  S0 := s0Of x.R x.F
  S1 := s1Of x.R x.F
  Dc := x.F.Dc (zsOf x.R x.F)
  Sp := x.F.Sp (zsOf x.R x.F)
  C := colOf x.R x.F x.sEE
  NuC := x.C.NuC
  I := idsOf x.cG x.Z x.C
  JA := x.JA
  JM := x.JM
  tied := ⟨x.div, x.amb0, x.mjH, x.Y.cen0 x.cG x.pins.keep⟩

def TwIn.wd (x : TwIn ex) : (x.F.Dc (zsOf x.R x.F)).Mem → D.what₂.Word := (Equiv.ofBijective _ x.C.bij).symm

theorem TwIn.wd_wU (x : TwIn ex) (u : D.what₂.Word) : x.wd (x.C.wU u) = u := (Equiv.ofBijective _ x.C.bij).symm_apply_apply u

theorem TwIn.wU_wd (x : TwIn ex) (m : (x.F.Dc (zsOf x.R x.F)).Mem) : x.C.wU (x.wd m) = m :=
  (Equiv.ofBijective _ x.C.bij).apply_symm_apply m

def TwIn.bR (x : TwIn ex) (m : (x.F.Dc (zsOf x.R x.F)).Mem) (i : Fin ((x.F.Dc (zsOf x.R x.F)).a m)) : (D.mem (x.wd m)).A.Mram :=
  D.eMu (x.wd m) (D.jN (x.wd m) (x.C.eNu (x.wd m)
    (Pi.single (Fin.cast (congrArg (x.F.Dc (zsOf x.R x.F)).a (x.wU_wd m)).symm i) 1)))

set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 4000000 in

structure RealIn (x : TwIn ex) (Rc : Formalism.L2.RecT ex) (S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc) : Type 1 where
  psiPin : x.R.ψ = Rc.T.theta.W.ψ
  hin : ∀ u, Formalism.L2.SG.PoincareInHH.PoincareSetting.InHH S.X u S.Y.hK
  spPin : HEq (x.F.Sp (zsOf x.R x.F)) (Formalism.IndefR.Cx.spOf (X := S.X) (twAt D.what₂.embLL x.A3.A.v0) (x.F.Dc (zsOf x.R x.F)) S.Y.hK S.G
    x.wd (fun m => pwOf S hin (x.wd m)) x.bR)
  Sx : Formalism.IndefR.NX.RatDat D.ntw
  nexp : Formalism.IndefR.NX.NExpRealS x.R x.cG Sx
  stdV : ∀ i, (∀ a b, (Vc D i).hT ((Vc D i).frame a) ((Vc D i).frame b) = if a = b then 1 else 0) ∧
    (Vc D i).L0 = Submodule.span (𝓞 D.host.E) (Set.range (Vc D i).frame)
  stdX : (∀ a b, D.sp.X'.hT (D.sp.X'.frame a) (D.sp.X'.frame b) = if a = b then 1 else 0) ∧
    D.sp.X'.L0 = Submodule.span (𝓞 D.host.E) (Set.range D.sp.X'.frame)
  tS : Formalism.L2.Theta.GA D (Yc D 0)
  cS : ℝ
  κS : ℝ
  ιS : Formalism.L2.Theta.GA D (Yc D 0) ≃* S.X.B.I.GA
  instEq : S.X.B.I = Formalism.IndefR.RationalEmbedding.inst D
  ιS_eq : HEq ιS (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv
  sEEc : Tw (twAt D.what₂.embLL x.A3.A.v0) x.R.HE.H →ₗ⋆[ℂ] Tw (twAt D.what₂.embLL x.A3.A.v0) (Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX S.X)
  sEEj : HEq x.sEE sEEc
  seeLev : (∃ t' : Formalism.L2.Theta.GA D (Yc D 0), Formalism.IndefR.AutomorphicEvaluation.ConjLevel t'⁻¹ (levS _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 true))) (Formalism.IndefR.Lev.levChi _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 true))) (ιS ⁻¹' seeKS S.X) (fun k => seeChiS S.X (ιS k))) →
    Formalism.IndefR.AutomorphicEvaluation.ConjLevel tS⁻¹ (levS _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 true))) (Formalism.IndefR.Lev.levChi _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 true))) (ιS ⁻¹' seeKS S.X) (fun k => seeChiS S.X (ιS k))
  seeEval : (∃ c' : ℝ, Formalism.IndefR.AutomorphicEvaluation.EvalTieT (x.R.MY 0) x.R.ν0 x.R.fd0 (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true)) S.X S.G ιS tS c') →
    Formalism.IndefR.AutomorphicEvaluation.EvalTieT (x.R.MY 0) x.R.ν0 x.R.fd0 (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true)) S.X S.G ιS tS cS
  uS : ℂ
  uS_norm : ‖uS‖ = 1
  seeDef : ∀ (v : Tw (twAt D.what₂.embLL x.A3.A.v0) x.R.HE.H) (hx : x.R.HE.e (Tw.out v) ∈ (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true))),
    sEEc v = Tw.mk (twAt D.what₂.embLL x.A3.A.v0) ((uS * (κS : ℂ)) • (Formalism.IndefR.AutomorphicEvaluation.sEEofTT (x.R.MY 0) x.R.ν0 x.R.fd0 (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true)) S.X S.G ιS tS cS) ⟨x.R.HE.e (Tw.out v), hx⟩)
  seeK : 0 < κS ∧ ((∃ κ' : ℝ, 0 < κ' ∧ ∀ (v : Tw (twAt D.what₂.embLL x.A3.A.v0) x.R.HE.H) (hx : x.R.HE.e (Tw.out v) ∈ (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true))),
      ‖(κ' : ℂ) • (Formalism.IndefR.AutomorphicEvaluation.sEEofTT (x.R.MY 0) x.R.ν0 x.R.fd0 (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true)) S.X S.G ιS tS cS) ⟨x.R.HE.e (Tw.out v), hx⟩‖ = ‖v‖) →
    ∀ (v : Tw (twAt D.what₂.embLL x.A3.A.v0) x.R.HE.H), x.R.HE.e (Tw.out v) ∈ (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true)) →
      RealDat.nP x.F.lv2 true * ‖sEEc v‖ ^ 2 = ‖v‖ ^ 2)
  host : HostHyp D
  vpos : ∀ i, (Vc D i).IsPosDef

variable {x : TwIn ex} {Rc : Formalism.L2.RecT ex} {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc}

set_option maxHeartbeats 4000000 in

def realTOf (y : RealIn x Rc S) : RealT Rc (divisionPairOfAdelicFormsFaceColumnsData x) x.F.Dc x.F.Sp x.F.Zsc S x.core.Q.c.F where
  Rl := x.R
  sEE := x.sEE
  charW := (x.pins.char)
  zs := rfl
  s0 := (HEq.refl (s0Of x.R x.F))
  s1 := (HEq.refl (s1Of x.R x.F))
  dc := rfl
  sp := HEq.rfl
  col := (HEq.refl (colOf x.R x.F x.sEE))
  allPlaces := x.pins.char.allPl
  trSem := (x.pins.trSem)
  stdChar := x.pins.keep.std
  psiPin := y.psiPin
  signs := (x.pins.keep.signs)
  wdD := x.wd
  wdD_wU := x.wd_wU
  wU_wdD := x.wU_wd
  hin := y.hin
  bR := x.bR
  spPin := (y.spPin)
  frames := fun h => (Formalism.IndefR.Seed.Frm.framesOKg2_iff x.R).2 (x.pins.keep.frames h)
  cG := x.cG
  Sx := y.Sx
  nexp := y.nexp
  stdV := y.stdV
  stdX := y.stdX
  tS := y.tS
  cS := y.cS
  κS := y.κS
  ιS := y.ιS
  instEq := y.instEq
  ιS_eq := y.ιS_eq
  sEEc := y.sEEc
  sEEj := y.sEEj
  seeLev := (y.seeLev)
  seeEval := (y.seeEval)
  uS := y.uS
  uS_norm := y.uS_norm
  seeDef := (y.seeDef)
  seeK := (y.seeK)
  host := y.host
  err_eq := (x.err)
  vpos := y.vpos

theorem phEff_one (x : TwIn ex) : phEff x.R = fun _ => 1 := by
  funext i
  unfold phEff
  rw [x.pins.phs i]
  simp

set_option maxHeartbeats 4000000 in

def realTBOf (y : RealIn x Rc S) : RealTB Rc (divisionPairOfAdelicFormsFaceColumnsData x) x.F.Dc x.F.Sp x.F.Zsc S where
  T := x.core
  Q := realTOf y
  κ := x.geo.κ
  v₀ := (x.geo.v₀)
  fw := (x.geo.fw)
  bar := (x.geo.bar)
  O := (x.geo.O)
  pins := (x.geo.pins)
  rhoGeo := (x.geo.rhoGeo)
  equivAll := (x.geo.equivAll)
  cTie := (x.geo.cTie)
  phase := by
    have h : ∀ i, x.R.toRealDat.LUnif →
        Formalism.IndefR.FWT.PhaseTie x.core x.R.toRealDat x.geo.κ x.geo.v₀ x.geo.O (phEff x.R) i := by
      rw [phEff_one x]
      exact x.geo.phase
    exact (h)

set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 4000000 in

structure RecIn (y : RealIn x Rc S) : Type 1 where
  E : EigIdx D Yd
  labPi : E.Pi → x.A3.A.fam.base.Ix
  piOf : E.Pi → HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ
  Tp : Formalism.L2.Host.TupTied D x.R.C ex.nch
  tpEq : HEq Tp Rc.T.n.tp
  tupXi : ∀ μ, Formalism.IndefR.RecTie.Used0 D μ → x.R.toLevCh.xiH (x.Y.tupT μ) = Tp.xi μ
  mtRead : Formalism.IndefR.RecTie.MtRead x.R.toRealDat x.F.lv2 x.Y.tupT x.Y.hm x.Y.hTop x.Y.hinj x.Y.IL
    (twPOf (divisionPairOfAdelicFormsFaceColumnsData x) x.Y.tupT x.Y.tupTie)
  mjRead : Formalism.IndefR.RecTie.MjRead x.R.toRealDat x.F.lv2 x.Y.tupT x.Y.hm x.Y.hTop x.Y.hinj x.Y.IL
    (fun i => (x.A3.indefDown (s0Of x.R x.F)).dW i) (fun i v => x.Z.jW i v) ((jDT (realTOf y)))

set_option maxHeartbeats 4000000 in

def realRecOf {y : RealIn x Rc S} (r : RecIn y) : RealRec (realTOf y) where
  tupT := x.Y.tupT
  hm := x.Y.hm
  hTop := x.Y.hTop
  hinj := x.Y.hinj
  Ish := (x.Y.Ish)
  I0 := (x.Y.Iz)
  IL := (x.Y.IL)
  Kc := x.Y.Kc
  E := r.E
  labPi := r.labPi
  PY := x.Y.PY
  PW := x.Y.PW
  eFT := (x.Y.eFT)
  piOf := r.piOf
  ιW := x.Y.ιW
  Tp := (r.Tp)
  recR := by
    have h : Formalism.IndefR.RecTie.RecReal x.R.toRealDat x.F.lv2 x.Y.tupT x.Y.hm x.Y.hTop x.Y.hinj ex.p0 x.Y.Ish x.Y.Iz x.Y.IL x.Y.Kc r.E
        r.labPi x.Y.PY x.Y.PW x.Y.eFT r.piOf x.Y.ιW ex.nch r.Tp :=
      ⟨x.pins.char.base, x.Y.tied, x.Y.prtE, x.Y.prtE0, x.Y.prtWE, x.Y.xi, r.tupXi,
        fun w => by rw [x.Y.muAt w, x.Y.tupT_tup], x.Y.isomFin, x.Y.frameMatch⟩
    exact (h)
  tpEq := (r.tpEq)
  tupTie := x.Y.tupTie
  tupT_tup := x.Y.tupT_tup
  muEq := (Eq.refl x.R.mu)
  mtRead := (r.mtRead)
  mjRead := (r.mjRead)

end GlobalTheory.Mem.R3

end
