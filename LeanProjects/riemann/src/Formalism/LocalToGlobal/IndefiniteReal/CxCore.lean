import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LiftCoordinatesInGoodPart
import Formalism.LocalToGlobal.IndefiniteReal.LiftCoordinatesInGoodPartOfDefinite
import Formalism.LocalToGlobal.IndefiniteReal.EigSumLeComapSemi
import Formalism.LocalToGlobal.IndefiniteReal.LiftGoodPartComplexEqRange

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

structure CxCore (A : FamIn K G Pl0 T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
    (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
    (Zsc : DefSub A.fam.amb → IndefScale A.fam.base) (X : CxData A.fam.amb) (s : ℕ)
    (C0 C1 : ∀ j : Fin m, ((A.fam.L j A.fam.μ0).Pl × ℕ → K) → Prop)
    (ζ : (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Dc.Mem → A.fam.base.Tup → K)
    (sEE : X.EE →ₗ⋆[ℂ] (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Sp.HH)
    (C CH : ℝ)
    (hE : ∀ t, (A.fam.R t).Pl × ℕ → Module.End ℂ X.EE)
    (hW : ∀ j t, (A.fam.L j t).Pl × ℕ → Module.End ℂ (X.W j)) (gE : Representation ℂ G X.EE)
    (gW : ∀ j, Representation ℂ G (X.W j)) : Prop where

  kFormR : X.KFormR

  kFormL : X.KFormL

  jIsoR : X.JIsoR (cvOf A P0 ψ0 P1 ψ1)

  jIsoL : X.JIsoL (cvOf A P0 ψ0 P1 ψ1)

  npTie : NPTie X P0 P1

  ok : A.fam.Ok s

  sep : A.fam.TypesSep

  heckeR : HeckeRatAllR A

  heckeL : HeckeRatAllL A

  thetaR : HeckeThetaR A X hE

  thetaL : HeckeThetaL A X hW

  gUnit : Formalism.IndefR.CxPass.GUnit A X gE

  gEquiv : Formalism.IndefR.CxPass.GEquiv A X gE

  lev0 : Formalism.IndefR.CxPass.LevType A X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gE false P0 ψ0

  lev1 : Formalism.IndefR.CxPass.LevType A X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gE true P1 ψ1

  h2P : Formalism.IndefR.CxPass.PrincipalInjectiveCommonRange A X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc)

  gUnitL : Formalism.IndefR.CxPass.GUnitL A X gW

  gEquivL : Formalism.IndefR.CxPass.GEquivL A X gW

  lower_level_lift_type : Formalism.IndefR.CxPass.LevTypeL A X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gW false P0 ψ0

  upper_level_lift_type : Formalism.IndefR.CxPass.LevTypeL A X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gW true P1 ψ1

  inBlock : X.zs.InBlock

  ratZ : X.RatZ

  eig0 : LiftsEig A X P0 ψ0 C0

  eig1 : LiftsEig A X P1 ψ1 C1

  typ0 : LiftsTyp A C0

  typ1 : LiftsTyp A C1

  pos : ∀ b, (lv (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs) b).Pos

  h0 : X.H0

  w1 : ∀ w, X.W1 (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH) w → w ∈ X.Tw

  h4pos : X.H4pos

  thmBop : ∀ b, X.ThmBop b

  partsE : ∀ b, X.PartsE b

  ratMu : ∀ b, X.RATmu (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b

  kForm : ∀ b, X.KForm b

  mLat : ∀ b, X.MLat b

  ewNorm : ∀ b, X.EWnorm b

  thmAop : ∀ b, X.ThmAop b

  partsW : ∀ b, X.PartsW b

  ratTh : ∀ b, X.RATth (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b

  galD : ∀ b, X.GalD (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b

  dimParts : ∀ b, X.DimParts b

  l3 : (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) false).L3 ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)

  on : (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) false).ON ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)

  l6 : (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) true).L6 ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)

  btVanish : X.BtVanish (fc := faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc)

  mi0 : X.MatrixIdentityOffBase (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) ζ

  zetaOK : X.ZetaOK ζ

  l1e : (X.colOf (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) (X.colDef (fun u t => (ζ u t)⁻¹) sEE)).L1e

  fun0 : (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) false).FUN ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)

section Core

variable {A : FamIn K G Pl0 T m} {P0 : Subgroup G} {ψ0 : P0 →* Kˣ} {P1 : Subgroup G} {ψ1 : P1 →* Kˣ}
  {Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)} {Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs)}
  {Zsc : DefSub A.fam.amb → IndefScale A.fam.base} {X : CxData A.fam.amb} {s : ℕ}
  {C0 C1 : ∀ j : Fin m, ((A.fam.L j A.fam.μ0).Pl × ℕ → K) → Prop}
  {ζ : (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Dc.Mem → A.fam.base.Tup → K}
  {sEE : X.EE →ₗ⋆[ℂ] (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Sp.HH}
  {C CH : ℝ}
  {hE : ∀ t, (A.fam.R t).Pl × ℕ → Module.End ℂ X.EE} {hW : ∀ j t, (A.fam.L j t).Pl × ℕ → Module.End ℂ (X.W j)}
  {gE : Representation ℂ G X.EE} {gW : ∀ j, Representation ℂ G (X.W j)}

theorem CxCore.stable (hC : CxCore A P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 C1 ζ sEE C CH hE hW gE gW) : X.zs.Stable :=
  CxData.cutStable X hC.kFormR hC.kFormL
    (Formalism.IndefR.CxPass.kerStabR_of hC.kFormR hC.gEquiv (kerStabR_hecke hC.thetaR))
    (Formalism.IndefR.CxPass.kerStabL_of hC.kFormL hC.gEquivL (kerStabL_hecke hC.thetaL))
    (adjClosedR_of hC.ok hC.heckeR hC.kFormR hC.jIsoR) (adjClosedL_of hC.ok hC.heckeL hC.kFormL hC.jIsoL)

theorem CxCore.wf (hC : CxCore A P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 C1 ζ sEE C CH hE hW gE gW) :
    ∀ b, (lv (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs) b).WF := fun b => match b with
  | false => A.side_WF hC.ok P0 ψ0 X.zs hC.stable hC.inBlock hC.sep
  | true => A.side_WF hC.ok P1 ψ1 X.zs hC.stable hC.inBlock hC.sep

theorem CxCore.h2 (hC : CxCore A P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 C1 ζ sEE C CH hE hW gE gW) (b : Bool) :
    X.H2 (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b :=
  (cutRows (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) (cvOf A P0 ψ0 P1 ψ1) b (hC.wf b) hC.h4pos
    (isoR_of hC.ok hC.jIsoR hC.npTie b) (crdZ_of X b) (coordinates_in_good_part_of_definite X b)
    (Formalism.IndefR.CxPass.ratLev_of hC.ok hC.kFormR hC.jIsoR hC.ratZ hC.gUnit hC.gEquiv b)
    (Formalism.IndefR.CxPass.dnLev_of hC.ok hC.kFormR hC.jIsoR hC.ratZ hC.gUnit hC.gEquiv hC.h2P hC.lev0 hC.lev1 b)
    (Formalism.IndefR.CxPass.upLev_of hC.ok hC.kFormR hC.jIsoR hC.gUnit hC.gEquiv hC.lev0 hC.lev1 b)
    (hC.thmBop b) (hC.partsE b)).1

theorem prims_of_core (hC : CxCore A P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 C1 ζ sEE C CH hE hW gE gW)
    (hPass : Passage ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)
      (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) false) (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) true)) :
    CxPrims A P0 ψ0 P1 ψ1 Dc Sp Zsc X (cvOf A P0 ψ0 P1 ψ1) s C0 C1 ζ sEE C CH := by
  have kR : X.KerStabR := Formalism.IndefR.CxPass.kerStabR_of hC.kFormR hC.gEquiv (kerStabR_hecke hC.thetaR)
  have kL : X.KerStabL := Formalism.IndefR.CxPass.kerStabL_of hC.kFormL hC.gEquivL (kerStabL_hecke hC.thetaL)
  have aR : X.AdjClosedR := adjClosedR_of hC.ok hC.heckeR hC.kFormR hC.jIsoR
  have aL : X.AdjClosedL := adjClosedL_of hC.ok hC.heckeL hC.kFormL hC.jIsoL
  have hst : X.zs.Stable := CxData.cutStable X hC.kFormR hC.kFormL kR kL aR aL
  exact
    { kFormR := hC.kFormR, kFormL := hC.kFormL, kerStabR := kR, kerStabL := kL, adjClosedR := aR, adjClosedL := aL
      inBlock := hC.inBlock, ratZ := hC.ratZ, jIsoR := hC.jIsoR, jIsoL := hC.jIsoL, ok := hC.ok, sep := hC.sep
      heckeR := hC.heckeR A.fam.μ0, heckeL := fun j => hC.heckeL j A.fam.μ0
      eig0 := hC.eig0, eig1 := hC.eig1, typ0 := hC.typ0, typ1 := hC.typ1, pos := hC.pos, h0 := hC.h0, w1 := hC.w1
      h4pos := hC.h4pos, isoR := isoR_of hC.ok hC.jIsoR hC.npTie, crdZ := crdZ_of X, coordinates_in_good_part := coordinates_in_good_part_of_definite X
      ratLev := Formalism.IndefR.CxPass.ratLev_of hC.ok hC.kFormR hC.jIsoR hC.ratZ hC.gUnit hC.gEquiv
      dnLev := Formalism.IndefR.CxPass.dnLev_of hC.ok hC.kFormR hC.jIsoR hC.ratZ hC.gUnit hC.gEquiv hC.h2P hC.lev0 hC.lev1
      upLev := Formalism.IndefR.CxPass.upLev_of hC.ok hC.kFormR hC.jIsoR hC.gUnit hC.gEquiv hC.lev0 hC.lev1
      thmBop := hC.thmBop, partsE := hC.partsE
      ratMu := hC.ratMu, h3 := equivRows_of P0 ψ0 P1 ψ1 Dc Sp Zsc hC.kFormR hst hC.ok hC.thetaR
      kForm := hC.kForm, mLat := hC.mLat, ewNorm := hC.ewNorm, isoL := isoL_of hC.ok hC.jIsoL hC.npTie
      crdZL := crdZL_of X, lift_coordinates_in_good_part := lift_coordinates_in_good_part_of_definite X
      ratLevL := Formalism.IndefR.CxPass.ratLevL_of hC.ok hC.kFormL hC.jIsoL hC.ratZ hC.gUnitL hC.gEquivL
      dnLevL := Formalism.IndefR.CxPass.dnLevL_of hC.ok hC.kFormL hC.jIsoL hC.ratZ hC.gUnitL hC.gEquivL hC.lower_level_lift_type hC.upper_level_lift_type
      upLevL := Formalism.IndefR.CxPass.upLevL_of hC.ok hC.kFormL hC.jIsoL hC.gUnitL hC.gEquivL hC.lower_level_lift_type hC.upper_level_lift_type
      thmAop := hC.thmAop, partsW := hC.partsW, ratTh := hC.ratTh
      h3W := equivLifts_of P0 ψ0 P1 ψ1 Dc Sp Zsc hC.kFormL hst hC.ok hC.thetaL
      galD := hC.galD, dimParts := hC.dimParts, l3 := hC.l3, on := hC.on, l6 := hC.l6, btVanish := hC.btVanish
      mi0 := hC.mi0, zetaOK := hC.zetaOK, l1e := hC.l1e, passage := hPass, fun0 := hC.fun0 }

theorem links_of_core (hC : CxCore A P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 C1 ζ sEE C CH hE hW gE gW)
    (hPass : Passage ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)
      (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) false) (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) true)) :
    X.CxLinks (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) (X.colDef (fun u t => (ζ u t)⁻¹) sEE) C CH :=
  links_of_prims (prims_of_core hC hPass)

end Core

end Formalism.IndefR.Cx
