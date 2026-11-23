import Formalism.LocalToGlobal.IndefiniteReal.TrISepWith
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
import Formalism.LocalToGlobal.IndefiniteReal.RhoGeo

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT

namespace Formalism.IndefR

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}

def phEff {G Pl0 I0 T0 : Type} [Group G] [Fintype G] {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) : Fin D.R.m → ℂ :=
  fun i => cj (twAt D.what₂.embLL A3.A.v0) (Rl.phs i)

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure RealTB (Rc : Formalism.L2.RecT ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs))
    (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3)
    (S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc) : Type 1 where

  T : CoreJ D

  [alg : Algebra T.Q.c.F D.what₂.LL]

  Q : RealT Rc P Dcf Spf Zscf S T.Q.c.F

  κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)

  v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Q.Rl.toRealDat.MW i σ).Vec

  fw : FWTie T Q.Rl.toRealDat κ v₀

  bar : BarTie fw

  O : ∀ i, OMDat T.toCore Q.Rl.toRealDat i Unit (fun _ => P.A3.A.μ0)

  pins : ∀ i, OMPins T Q.Rl.toRealDat κ v₀ O i

  rhoGeo : RhoGeo fw O

  equivAll : EquivAll T Q.Rl.toRealDat κ O

  cTie : ∀ i, CTie T Q.Rl.toRealDat κ v₀ O i

  phase : ∀ i, Q.Rl.toRealDat.LUnif → PhaseTie T Q.Rl.toRealDat κ v₀ O (phEff Q.Rl) i

attribute [instance] RealTB.alg

variable {Rc : Formalism.L2.RecT ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc}

structure RowsB (B : RealTB Rc P Dcf Spf Zscf S) : Prop where

  ioExt : IoExt B.Q.Rl.toRealDat

  oneMap : ∀ i, OneMapRowR B.T B.Q.Rl.toRealDat B.κ B.v₀ B.O (phEff B.Q.Rl) i

structure InB (B : RealTB Rc P Dcf Spf Zscf S) : Prop where

  jEvExists : JEvExists B.T B.Q.Rl.toRealDat B.κ B.v₀

  jEvBar : JEvBar B.T B.Q.Rl.toRealDat B.κ

  evInj : EvInj B.T B.Q.Rl.toRealDat B.v₀

  jUnif : JUnif B.T B.Q.Rl.toRealDat B.κ B.v₀

  geoAct : GeoAct B.T B.Q.Rl.toRealDat B.κ B.v₀

  latFull : LatFull B.T B.κ

  dimMatch : DimMatch B.T B.Q.Rl.toRealDat B.κ

end Formalism.IndefR
