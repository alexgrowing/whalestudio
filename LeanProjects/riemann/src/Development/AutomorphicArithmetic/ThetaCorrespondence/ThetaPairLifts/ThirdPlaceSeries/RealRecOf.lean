import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealRec
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEqAlt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
namespace GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts} {Yd : DivX D}
  {cX : ExtraC}
variable {ex : Extra D L hT Gi Gl K Yd cX}
set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 4000000 in
structure RealInAlt (x : TwIn ex) (Rc : _root_.Formalism.L2.RecTAlt ex) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) : Type 1 where
  psiPin : x.R.ψ = Rc.T.theta.W.ψ
  hin : ∀ u, Formalism.L2.SG.PoincareInHH.PoincareSetting.InHH S.X u S.Y.hK
  spPin : HEq (x.F.Sp (zsOf x.R x.F)) (Formalism.IndefR.Cx.spOf (X := S.X) (twAt D.what₂.embLL x.A3.A.v0) (x.F.Dc (zsOf x.R x.F)) S.Y.hK S.G
    x.wd (fun m => _root_.Formalism.IndefR.pwOf_alt S hin (x.wd m)) x.bR)
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
variable {x : TwIn ex} {Rc : _root_.Formalism.L2.RecTAlt ex} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc}
set_option maxHeartbeats 4000000 in
def realisationOfInput (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc S) : _root_.Formalism.IndefR.IndefiniteRealisation Rc (divisionPairOfAdelicFormsFaceColumnsData x) x.F.Dc x.F.Sp x.F.Zsc S x.core.Q.c.F where
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
set_option maxHeartbeats 4000000 in
def boundedRealisationOfInput (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc S) : _root_.Formalism.IndefR.RealTBAlt Rc (divisionPairOfAdelicFormsFaceColumnsData x) x.F.Dc x.F.Sp x.F.Zsc S where
  T := x.core
  Q := _root_.GlobalTheory.Mem.R3.realisationOfInput y
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
structure RecursiveInput (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc S) : Type 1 where
  E : EigIdx D Yd
  labPi : E.Pi → x.A3.A.fam.base.Ix
  piOf : E.Pi → HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ
  Tp : Formalism.L2.Host.TupTied D x.R.C ex.nch
  tpEq : HEq Tp Rc.T.n.tp
  tupXi : ∀ μ, Formalism.IndefR.RecTie.Used0 D μ → x.R.toLevCh.xiH (x.Y.tupT μ) = Tp.xi μ
  mtRead : Formalism.IndefR.RecTie.MtRead x.R.toRealDat x.F.lv2 x.Y.tupT x.Y.hm x.Y.hTop x.Y.hinj x.Y.IL
    (twPOf (divisionPairOfAdelicFormsFaceColumnsData x) x.Y.tupT x.Y.tupTie)
  mjRead : Formalism.IndefR.RecTie.MjRead x.R.toRealDat x.F.lv2 x.Y.tupT x.Y.hm x.Y.hTop x.Y.hinj x.Y.IL
    (fun i => (x.A3.indefDown (s0Of x.R x.F)).dW i) (fun i v => x.Z.jW i v) ((indefiniteDownJoin (realisationOfInput y)))
set_option maxHeartbeats 4000000 in
def realisationRecursionOfInput {y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc S} (r : _root_.GlobalTheory.Mem.R3.RecursiveInput y) : _root_.Formalism.IndefR.IndefiniteRealisationRecursion (_root_.GlobalTheory.Mem.R3.realisationOfInput y) where
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
end
