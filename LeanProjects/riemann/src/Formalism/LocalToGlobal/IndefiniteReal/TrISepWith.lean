import Mathlib
import Formalism.LocalToGlobal.ClassSK
import Formalism.LocalToGlobal.HilbertRowConditions.ColumnsFunctionAtSubspaces
import Formalism.LocalToGlobal.IndefiniteReal.PrimitivePackageFullHecke
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Formalism.LocalToGlobal.IndefiniteReal.SpOfRwRange
import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.SignsG
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR
import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.FramesOK
import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.NormalFrameClauses
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.RatDatOfReal
import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.SEEPinC
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR.Links Formalism.IndefR.Cx

namespace Formalism.IndefR

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}

def faceT (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs))
    (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) :
    Face3 D P.A3 :=
  ⟨P.P0, P.ψ0, P.Ps, P.ψs, Dcf, Spf, Zscf⟩

def TrISepWith {G Pl0 I0 T : Type} [Group G] [Fintype G] (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m)
    (tr : Fin D.R.m → (I0 × List ℕ → D.what₂.LL) → I0 × List ℕ → D.what₂.LL) : Prop :=
  ∀ (j : Fin D.R.m), ∀ p ∈ (A3.fam3.RI A3.fam3.F.μ0).ixFin3 A3.fam3.F.X,
    ∀ p' ∈ (A3.fam3.RI A3.fam3.F.μ0).ixFin3 A3.fam3.F.X,
    (∃ k : A3.okI A3.A.μ0 × List ℕ, p.2 (k.1.1, k.2) ≠ p'.2 (k.1.1, k.2)) →
      ∃ k : A3.okI A3.A.μ0 × List ℕ, tr j p.2 (k.1.1, k.2) ≠ tr j p'.2 (k.1.1, k.2)

open Classical in

def hkCan {G Pl0 I0 T : Type} [Group G] [Fintype G] (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) : HkDat3 A3 where
  Hk := A3.fam3.base3.Ix
  ev p q := if p = q then 1 else 0
  ev_inj p p' h := by
    have h2 := congrFun h p
    dsimp only at h2
    rw [if_pos rfl] at h2
    by_contra hne
    rw [if_neg (fun h' => hne h'.symm)] at h2
    exact one_ne_zero h2

def errCan {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs} (S : IndefData Df)
    (F0 : HeightOneSpectrum (𝓞 K) → Bs.J → ℝ) (w : HeightOneSpectrum (𝓞 K)) : ℝ :=
  max 0 ((∑ j', ((S.Iw j' (S.μ w) w : ℝ) + (S.Iw j' (S.μ w) (Formalism.DivisionValues.conjPl w) : ℝ))) / (S.D : ℝ) -
      ∑ j', 2 * ((Formalism.EigenvalueLevelCeiling.ramw w : ℝ) * F0 w j') - (Formalism.EigenvalueLevelCeiling.ramw w : ℝ) * (2 / (Formalism.EigenvalueLevelCeiling.plc w : ℝ) ^ 2)) /
    ((Formalism.EigenvalueLevelCeiling.ramw w : ℝ) * (Fintype.card Bs.J : ℝ))

def pwOf {Rc : Formalism.L2.RecT ex} (S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc)
    (hin : ∀ u, Formalism.L2.SG.PoincareInHH.PoincareSetting.InHH S.X u S.Y.hK) (u : D.what₂.Word) : Formalism.IndefR.Cx.PerW S.X S.Y.hK u where
  Dt := S.Y.Dt u
  hD := S.Y.reps u
  hin := hin u
  hlin := Formalism.L2.SG.Closed.PuLinearC_holds D S.X S.Y u
  F := (Rc.T.cols.forms u).to0
  Tr := S.tr u
  hI := S.into u
  hB := S.bij u

def seeKS (X : Formalism.L2.SG.HidaSetting.HidaSetting D) : Set X.B.I.GA := {x | x.1 = 1 ∧ x.2 ∈ X.K2}

def seeChiS (X : Formalism.L2.SG.HidaSetting.HidaSetting D) : X.B.I.GA → ℂ := fun x => star (X.chi2 x.2)

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure RealT (Rc : Formalism.L2.RecT ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs))
    (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3)
    (S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] : Type 1 where

  Rl : RealDat3 D P.A3 Ks

  sEE : (Rl.toCx3 (faceT P Dcf Spf Zscf)).EE →ₗ⋆[ℂ] ((faceT P Dcf Spf Zscf).fc (Rl.toCx3 (faceT P Dcf Spf Zscf)).zs).Sp.HH

  charW : Rl.WeakCharacterisation (faceT P Dcf Spf Zscf)

  zs : (Rl.toCx3 (faceT P Dcf Spf Zscf)).zs = P.Zs

  s0 : HEq ((Rl.toCx3 (faceT P Dcf Spf Zscf)).data (faceT P Dcf Spf Zscf).cr false) P.S0

  s1 : HEq ((Rl.toCx3 (faceT P Dcf Spf Zscf)).data (faceT P Dcf Spf Zscf).cr true) P.S1

  dc : Dcf P.Zs = P.Dc

  sp : HEq (Spf P.Zs) P.Sp

  col : HEq ((Rl.toCx3 (faceT P Dcf Spf Zscf)).colOf (faceT P Dcf Spf Zscf).cr
      ((Rl.toCx3 (faceT P Dcf Spf Zscf)).colDef
        (fun u t => (zetaEps (Rl.toCx3 (faceT P Dcf Spf Zscf)) (faceT P Dcf Spf Zscf).cr sEE u t)⁻¹) sEE)) P.C

  allPlaces : Rl.AllPlaces

  trSem : (∃ tr, Rl.TrISem (faceT P Dcf Spf Zscf) tr ∧ TrISepWith P.A3 tr) →
    Rl.TrISem (faceT P Dcf Spf Zscf) P.A3.trI ∧ P.A3.fam3.TrISep

  stdChar : Formalism.L2.Theta.IsStdChar D Rl.ψ (-1)

  psiPin : Rl.ψ = Rc.T.theta.W.ψ

  signs : Formalism.IndefR.Mi.SignsAtG Rl.toRealDat (faceT P Dcf Spf Zscf).lv2

  wdD : P.Dc.Mem → D.what₂.Word

  wdD_wU : ∀ u, wdD (P.I.wU u) = u

  wU_wdD : ∀ x, P.I.wU (wdD x) = x

  hin : ∀ u, Formalism.L2.SG.PoincareInHH.PoincareSetting.InHH S.X u S.Y.hK

  bR : ∀ x, Fin (P.Dc.a x) → (D.mem (wdD x)).A.Mram

  spPin : HEq P.Sp (Formalism.IndefR.Cx.spOf (X := S.X) (twAt D.what₂.embLL P.A3.A.v0) P.Dc S.Y.hK S.G wdD (fun x => pwOf S hin (wdD x)) bR)

  frames : Formalism.IndefR.Seed.Frm.FramesExistDiagonal D Rl.Pg → Formalism.IndefR.Mi.FramesOKg2 Rl

  cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd

  Sx : Formalism.IndefR.NX.RatDat D.ntw

  nexp : Formalism.IndefR.NX.NExpRealS Rl cG Sx

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

  sEEc : Tw (twAt D.what₂.embLL P.A3.A.v0) Rl.HE.H →ₗ⋆[ℂ] Tw (twAt D.what₂.embLL P.A3.A.v0) (Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX S.X)

  sEEj : HEq sEE sEEc

  seeLev : (∃ t' : Formalism.L2.Theta.GA D (Yc D 0), Formalism.IndefR.AutomorphicEvaluation.ConjLevel t'⁻¹ (levS _ (Rl.βY 0) (Rl.dat0 (Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))) (Formalism.IndefR.Lev.levChi _ (Rl.βY 0) (Rl.dat0 (Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))) (ιS ⁻¹' seeKS S.X) (fun k => seeChiS S.X (ιS k))) →
    Formalism.IndefR.AutomorphicEvaluation.ConjLevel tS⁻¹ (levS _ (Rl.βY 0) (Rl.dat0 (Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))) (Formalism.IndefR.Lev.levChi _ (Rl.βY 0) (Rl.dat0 (Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))) (ιS ⁻¹' seeKS S.X) (fun k => seeChiS S.X (ιS k))

  seeEval : (∃ c' : ℝ, Formalism.IndefR.AutomorphicEvaluation.EvalTieT (Rl.MY 0) Rl.ν0 Rl.fd0 (Rl.toRealDat.EEat (Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true)) S.X S.G ιS tS c') →
    Formalism.IndefR.AutomorphicEvaluation.EvalTieT (Rl.MY 0) Rl.ν0 Rl.fd0 (Rl.toRealDat.EEat (Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true)) S.X S.G ιS tS cS

  uS : ℂ

  uS_norm : ‖uS‖ = 1

  seeDef : ∀ (x : Tw (twAt D.what₂.embLL P.A3.A.v0) Rl.HE.H) (hx : Rl.HE.e (Tw.out x) ∈ (Rl.toRealDat.EEat (Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))),
    sEEc x = Tw.mk (twAt D.what₂.embLL P.A3.A.v0) ((uS * (κS : ℂ)) • (Formalism.IndefR.AutomorphicEvaluation.sEEofTT (Rl.MY 0) Rl.ν0 Rl.fd0 (Rl.toRealDat.EEat (Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true)) S.X S.G ιS tS cS) ⟨Rl.HE.e (Tw.out x), hx⟩)

  seeK : 0 < κS ∧ ((∃ κ' : ℝ, 0 < κ' ∧ ∀ (x : Tw (twAt D.what₂.embLL P.A3.A.v0) Rl.HE.H) (hx : Rl.HE.e (Tw.out x) ∈ (Rl.toRealDat.EEat (Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))),
      ‖(κ' : ℂ) • (Formalism.IndefR.AutomorphicEvaluation.sEEofTT (Rl.MY 0) Rl.ν0 Rl.fd0 (Rl.toRealDat.EEat (Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true)) S.X S.G ιS tS cS) ⟨Rl.HE.e (Tw.out x), hx⟩‖ = ‖x‖) →
    ∀ (x : Tw (twAt D.what₂.embLL P.A3.A.v0) Rl.HE.H), Rl.HE.e (Tw.out x) ∈ (Rl.toRealDat.EEat (Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true)) →
      RealDat.nP (faceT P Dcf Spf Zscf).lv2 true * ‖sEEc x‖ ^ 2 = ‖x‖ ^ 2)

  host : HostHyp D

  err_eq : ∀ w j, ((Rl.toCx3 (faceT P Dcf Spf Zscf)).data (faceT P Dcf Spf Zscf).cr false).err0 w j =
    errCan ((Rl.toCx3 (faceT P Dcf Spf Zscf)).data (faceT P Dcf Spf Zscf).cr false)
      ((faceT P Dcf Spf Zscf).fc (Rl.toCx3 (faceT P Dcf Spf Zscf)).zs).Z.F0 w

  vpos : ∀ i, (Vc D i).IsPosDef

namespace RealT

variable {Rc : Formalism.L2.RecT ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  (R : RealT Rc P Dcf Spf Zscf S Ks)

abbrev F (_R : RealT Rc P Dcf Spf Zscf S Ks) : Face3 D P.A3 := faceT P Dcf Spf Zscf

def FramesEx : Prop := Formalism.IndefR.Seed.Frm.FramesExistDiagonal D R.Rl.Pg

end RealT

end Formalism.IndefR
