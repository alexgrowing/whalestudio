import Formalism.LocalToGlobal.IndefiniteReal.RealRec
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEqAlt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR.Links Formalism.IndefR.Cx
namespace Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
variable {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
theorem finrank_WL_eq_dW (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (i : Fin D.R.m) :
    Module.finrank D.what₂.LL (Q.Rl.toRealDat.WL Q.F.lv2 false i) = (P.A3.indefDown P.S0).dW i :=
  congrFun (dW_of_heq (congrArg (fun Z => P.A3.side3 P.P0 P.ψ0 Z) Q.zs) Q.s0) i
def indefiniteDownJoin (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (i : Fin D.R.m) (y : Fin ((P.A3.indefDown P.S0).dW i) → D.what₂.LL) :
    Fin (Q.Rl.nW i) → D.what₂.LL :=
  Formalism.IndefR.NX.jDL Q.Rl Q.F.lv2 i (y ∘ Fin.cast (_root_.Formalism.IndefR.finrank_WL_eq_dW Q i))
set_option genInjectivity false in
set_option genSizeOfSpec false in
structure IndefiniteRealisationRecursion (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) : Type 1 where
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
    (fun i y => P.I.jW i y) (_root_.Formalism.IndefR.indefiniteDownJoin Q)
namespace RealRec
variable {Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks} (Qr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion Q)
theorem _root_.Formalism.IndefR.IndefiniteRealisationRecursion.tupT_inj_used {μ μ' : D.what₂.Tup} (hμ : Formalism.IndefR.RecTie.Used0 D μ) (hμ' : Formalism.IndefR.RecTie.Used0 D μ')
    (h : Qr.tupT μ = Qr.tupT μ') : μ = μ' := by
  apply Qr.Tp.xi_inj
  rw [← Qr.recR.tupXi μ hμ, ← Qr.recR.tupXi μ' hμ', h]
theorem _root_.Formalism.IndefR.IndefiniteRealisationRecursion.tupleRead_baseTuple_eq_family : Qr.tupT D.what₂.mu0 = P.A3.A.μ0 :=
  Q.charW.base.lev.xi_inj (by rw [Qr.recR.tupXi D.what₂.mu0 (Or.inl rfl), Qr.Tp.trueColumnChoices_heckeChar_reference_eq_one, Q.charW.base.lev.xi_base])
theorem _root_.Formalism.IndefR.IndefiniteRealisationRecursion.tw_iff (Qr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion Q) (w : D.what₂.places.Pl) : D.plEq w ∈ Q.Rl.twPl ↔ D.what₂.muAt w ≠ D.what₂.mu0 := by
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
variable {Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks}
def _root_.Formalism.IndefR.IndefiniteRealisationRecursion.PartsRow (Qr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion Q) : Prop :=
  Formalism.IndefR.RecTie.PartsRec Q.Rl.toRealDat Q.F.lv2 Qr.tupT Qr.hm Qr.PY Qr.PW Qr.eFT Qr.E Qr.labPi Qr.piOf Qr.Ish.prt Qr.IL.prtW
end RealRec
end Formalism.IndefR
end
end
