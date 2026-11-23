import Formalism.LocalToGlobal.IndefiniteReal.TrISepWith
import Formalism.LocalToGlobal.IndefiniteReal.IsMultMapUnivZero
import Formalism.LocalToGlobal.IndefiniteReal.PartsRow
import Formalism.LocalToGlobal.IndefiniteReal.ThetaFireRow
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.RatDatOfReal

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR.Links Formalism.IndefR.Cx

namespace Formalism.IndefR

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}

variable {Rc : Formalism.L2.RecT ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

open Classical in

def twPOf (P : RowSideFamily ex) (tupT : D.what₂.Tup → P.T) (tupTie : ∀ μ, Formalism.IndefR.RecTie.Used0 D μ → P.I.tup (tupT μ) = μ)
    (μ : D.what₂.Tup) (i : Fin D.R.m) (x : D.what₂.MtL μ ((i : ℕ) + 1)) :
    P.A3.A.fam.amb.FL i (tupT μ) :=
  if h : Formalism.IndefR.RecTie.Used0 D μ then
    (P.A3.A.fam.L i (tupT μ)).S.basis.equivFun.symm
      (((P.A3.A.fam.L i (tupT μ)).S.lvlE (P.A3.A.fam.L i (tupT μ)).r (P.A3.A.fam.lvlA P.P0 P.ψ0).P
          (P.A3.A.fam.lvlA P.P0 P.ψ0).ψ).mulVec
        ((P.I.eMt i (tupT μ)).symm ((tupTie μ h).symm ▸ x)))
  else 0

theorem dW_of_heq {Bs : DefBase D.what₂.LL} {Df Df' : DefSide Bs} (h : Df = Df') {S0 : IndefData Df} {S1 : IndefData Df'}
    (hS : HEq S0 S1) : S0.dW = S1.dW := by
  subst h
  cases hS
  rfl

theorem dWL_eq (Q : RealT Rc P Dcf Spf Zscf S Ks) (i : Fin D.R.m) :
    Module.finrank D.what₂.LL (Q.Rl.toRealDat.WL Q.F.lv2 false i) = (P.A3.indefDown P.S0).dW i := by
  refine (congrFun (dW_of_heq ?_ Q.s0) i).trans ?_
  · rw [Q.zs]
    rfl
  · rfl

def jDT (Q : RealT Rc P Dcf Spf Zscf S Ks) (i : Fin D.R.m) (y : Fin ((P.A3.indefDown P.S0).dW i) → D.what₂.LL) :
    Fin (Q.Rl.nW i) → D.what₂.LL :=
  Formalism.IndefR.NX.jDL Q.Rl Q.F.lv2 i (y ∘ Fin.cast (dWL_eq Q i))

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure RealRec (Q : RealT Rc P Dcf Spf Zscf S Ks) : Type 1 where

  tupT : D.what₂.Tup → P.T

  hm : 0 < D.R.m

  hTop : Formalism.IndefR.RecTie.TopMultH Q.Rl.toRealDat

  hinj : ∀ i t, Function.Injective (Q.Rl.toRealDat.extV i t)

  Ish : Formalism.IndefR.RecTie.RowIds (Formalism.BasicNotions.RowSide.sharp D) (Formalism.IndefR.RecTie.toChainReal Q.Rl.toRealDat (faceT P Dcf Spf Zscf).lv2 tupT hm hTop) true

  I0 : Formalism.IndefR.RecTie.RowIds ex.p0.s (Formalism.IndefR.RecTie.toChainReal Q.Rl.toRealDat (faceT P Dcf Spf Zscf).lv2 tupT hm hTop) false

  IL : Formalism.IndefR.RecTie.LiftIds (Formalism.IndefR.RecTie.toLiftReal Q.Rl.toRealDat (faceT P Dcf Spf Zscf).lv2 tupT hm hTop hinj)

  Kc : Formalism.IndefR.RecTie.ColReal D

  E : EigIdx D Y

  labPi : E.Pi → P.A3.A.fam.base.Ix

  PY : Formalism.IndefR.principalLevelFrame.RowPsi (Yc D 0) D.R.r

  PW : ∀ i, Formalism.IndefR.principalLevelFrame.RowPsi (Wc D i) D.R.r

  eFT : D.what₂.FT ≃ Formalism.IndefR.principalLevelFrame.FTR Q.Rl.θ PY (Q.Rl.MY 0)
    (fun b => levS _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.levR (faceT P Dcf Spf Zscf).lv2 b)))
    (fun b => Formalism.IndefR.Lev.levChi _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.levR (faceT P Dcf Spf Zscf).lv2 b))) (fun _ => Q.Rl.e0)

  piOf : E.Pi → HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ

  ιW : ∀ i, ↥(Formalism.L2.Theta.GfC (Yc D 0)) →* ↥(Formalism.L2.Theta.GfC (Wc D i))

  Tp : Formalism.L2.Host.TupTied D Q.Rl.C ex.nch

  recR : Formalism.IndefR.RecTie.RecReal Q.Rl.toRealDat (faceT P Dcf Spf Zscf).lv2 tupT hm hTop hinj ex.p0 Ish I0 IL Kc E labPi PY PW eFT piOf ιW ex.nch Tp

  tpEq : HEq Tp Rc.T.n.tp

  tupTie : ∀ μ, Formalism.IndefR.RecTie.Used0 D μ → P.I.tup (tupT μ) = μ

  tupT_tup : ∀ t, tupT (P.I.tup t) = t

  muEq : Q.Rl.mu = P.S0.μ

  mtRead : Formalism.IndefR.RecTie.MtRead Q.Rl.toRealDat Q.F.lv2 tupT hm hTop hinj IL (twPOf P tupT tupTie)

  mjRead : Formalism.IndefR.RecTie.MjRead Q.Rl.toRealDat Q.F.lv2 tupT hm hTop hinj IL (fun i => (P.A3.indefDown P.S0).dW i)
    (fun i y => P.I.jW i y) (jDT Q)

namespace RealRec

variable {Q : RealT Rc P Dcf Spf Zscf S Ks} (Qr : RealRec Q)

theorem tupT_inj_used {μ μ' : D.what₂.Tup} (hμ : Formalism.IndefR.RecTie.Used0 D μ) (hμ' : Formalism.IndefR.RecTie.Used0 D μ')
    (h : Qr.tupT μ = Qr.tupT μ') : μ = μ' := by
  calc μ = P.I.tup (Qr.tupT μ) := (Qr.tupTie μ hμ).symm
    _ = P.I.tup (Qr.tupT μ') := by rw [h]
    _ = μ' := Qr.tupTie μ' hμ'

theorem tupleRead_baseTuple_eq_family : Qr.tupT D.what₂.mu0 = P.A3.A.μ0 := by
  have h : P.I.tup P.A3.A.μ0 = D.what₂.mu0 := by
    first
    | exact P.tied.div.tup.mu0
    | exact P.tied.div.1.tup.mu0
    | exact P.tied.div.tied.tup.mu0
  rw [← h]
  exact Qr.tupT_tup _

theorem tw_iff (Qr : RealRec Q) (w : D.what₂.places.Pl) : D.plEq w ∈ Q.Rl.twPl ↔ D.what₂.muAt w ≠ D.what₂.mu0 := by
  have h0 := Qr.tupleRead_baseTuple_eq_family
  constructor
  · intro hw he
    apply Q.charW.tup.mu_ne (D.plEq w) hw
    rw [← Qr.recR.tupAt w, he, h0]
  · intro hne
    by_contra hw
    apply hne
    apply Qr.tupT_inj_used (Or.inr ⟨w, rfl⟩) (Or.inl rfl)
    rw [Qr.recR.tupAt w, Q.charW.tup.mu_off (D.plEq w) hw, h0]

end RealRec

namespace RealRec

variable {Q : RealT Rc P Dcf Spf Zscf S Ks}

def ThetaFireAll (Qr : RealRec Q) : Prop :=
  Formalism.IndefR.RecTie.ThetaFireRow (Formalism.IndefR.RecTie.toLiftReal Q.Rl.toRealDat Q.F.lv2 Qr.tupT Qr.hm Qr.hTop Qr.hinj) Qr.IL

def PartsRow (Qr : RealRec Q) : Prop :=
  Formalism.IndefR.RecTie.PartsRec Q.Rl.toRealDat Q.F.lv2 Qr.tupT Qr.hm Qr.PY Qr.PW Qr.eFT Qr.E Qr.labPi Qr.piOf Qr.Ish.prt Qr.IL.prtW

end RealRec

end Formalism.IndefR
