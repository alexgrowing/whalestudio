import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.CxToPkgFamIn
import Formalism.LocalToGlobal.IndefiniteReal.MemRangeAdjointOfKerStable
import Formalism.LocalToGlobal.IndefiniteReal.EqZeroOfMemRangeAdjoint
import Formalism.LocalToGlobal.IndefiniteReal.EqZeroOfRangeAdjoint
import Formalism.LocalToGlobal.IndefiniteReal.FinrankISupLeSum
import Formalism.LocalToGlobal.IndefiniteReal.CutPassage
import Formalism.LocalToGlobal.IndefiniteReal.CxCutEP
import Formalism.LocalToGlobal.IndefiniteReal.CxCutPO

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

structure CxPrims (A : FamIn K G Pl0 T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
    (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
    (Zsc : DefSub A.fam.amb → IndefScale A.fam.base) (X : CxData A.fam.amb) (cv : CrdV A.fam.amb) (s : ℕ)
    (C0 C1 : ∀ j : Fin m, ((A.fam.L j A.fam.μ0).Pl × ℕ → K) → Prop)
    (ζ : (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Dc.Mem → A.fam.base.Tup → K)
    (sEE : X.EE →ₗ⋆[ℂ] (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Sp.HH)
    (C CH : ℝ) : Prop where

  kFormR : X.KFormR

  kFormL : X.KFormL

  kerStabR : X.KerStabR

  kerStabL : X.KerStabL

  adjClosedR : X.AdjClosedR

  adjClosedL : X.AdjClosedL

  inBlock : X.zs.InBlock

  ratZ : X.RatZ

  jIsoR : X.JIsoR cv

  jIsoL : X.JIsoL cv

  ok : A.fam.Ok s

  sep : A.fam.TypesSep

  heckeR : HeckeRatR A

  heckeL : HeckeRatL A

  eig0 : LiftsEig A X P0 ψ0 C0

  eig1 : LiftsEig A X P1 ψ1 C1

  typ0 : LiftsTyp A C0

  typ1 : LiftsTyp A C1

  pos : ∀ b, (lv (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs) b).Pos

  h0 : X.H0

  w1 : ∀ w, X.W1 (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH) w → w ∈ X.Tw

  h4pos : X.H4pos

  isoR : ∀ b, X.IsoR (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b

  crdZ : ∀ b, X.CrdZ (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b

  coordinates_in_good_part : ∀ b, X.CoordinatesInGoodPart (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) cv b

  ratLev : ∀ b, X.RatLev (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) cv b

  dnLev : ∀ b, X.DnLev cv b

  upLev : ∀ b, X.UpLev cv b

  thmBop : ∀ b, X.ThmBop b

  partsE : ∀ b, X.PartsE b

  ratMu : ∀ b, X.RATmu (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b

  h3 : ∀ b, X.H3 (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b

  kForm : ∀ b, X.KForm b

  mLat : ∀ b, X.MLat b

  ewNorm : ∀ b, X.EWnorm b

  isoL : ∀ b, X.IsoL (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b

  crdZL : ∀ b, X.CrdZL (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b

  lift_coordinates_in_good_part : ∀ b, X.LiftCoordinatesInGoodPart (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) cv b

  ratLevL : ∀ b, X.RatLevL (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) cv b

  dnLevL : ∀ b, X.DnLevL cv b

  upLevL : ∀ b, X.UpLevL cv b

  thmAop : ∀ b, X.ThmAop b

  partsW : ∀ b, X.PartsW b

  ratTh : ∀ b, X.RATth (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b

  h3W : ∀ b, X.H3W (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b

  galD : ∀ b, X.GalD (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b

  dimParts : ∀ b, X.DimParts b

  l3 : (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) false).L3 ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)

  on : (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) false).ON ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)

  l6 : (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) true).L6 ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)

  btVanish : X.BtVanish (fc := faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc)

  mi0 : X.MatrixIdentityOffBase (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) ζ

  zetaOK : X.ZetaOK ζ

  l1e : (X.colOf (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) (X.colDef (fun u t => (ζ u t)⁻¹) sEE)).L1e

  passage : Passage ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)
    (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) false) (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) true)

  fun0 : (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) false).FUN ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)

section All

variable {A : FamIn K G Pl0 T m} {P0 : Subgroup G} {ψ0 : P0 →* Kˣ} {P1 : Subgroup G} {ψ1 : P1 →* Kˣ}
  {Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)} {Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs)}
  {Zsc : DefSub A.fam.amb → IndefScale A.fam.base} {X : CxData A.fam.amb} {cv : CrdV A.fam.amb} {s : ℕ}
  {C0 C1 : ∀ j : Fin m, ((A.fam.L j A.fam.μ0).Pl × ℕ → K) → Prop}
  {ζ : (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Dc.Mem → A.fam.base.Tup → K}
  {sEE : X.EE →ₗ⋆[ℂ] (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Sp.HH}
  {C CH : ℝ}

theorem CxPrims.stable (hP : CxPrims A P0 ψ0 P1 ψ1 Dc Sp Zsc X cv s C0 C1 ζ sEE C CH) : X.zs.Stable :=
  CxData.cutStable X hP.kFormR hP.kFormL hP.kerStabR hP.kerStabL hP.adjClosedR hP.adjClosedL

theorem CxPrims.wf (hP : CxPrims A P0 ψ0 P1 ψ1 Dc Sp Zsc X cv s C0 C1 ζ sEE C CH) :
    ∀ b, (lv (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs) b).WF := fun b => match b with
  | false => A.side_WF hP.ok P0 ψ0 X.zs hP.stable hP.inBlock hP.sep
  | true => A.side_WF hP.ok P1 ψ1 X.zs hP.stable hP.inBlock hP.sep

theorem links_of_prims (hP : CxPrims A P0 ψ0 P1 ψ1 Dc Sp Zsc X cv s C0 C1 ζ sEE C CH) :
    X.CxLinks (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) (X.colDef (fun u t => (ζ u t)⁻¹) sEE) C CH := by
  have hW := hP.wf
  have hst := hP.stable
  have what₂ := fun b => cutRows (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) cv b (hW b) hP.h4pos (hP.isoR b) (hP.crdZ b)
    (hP.coordinates_in_good_part b) (hP.ratLev b) (hP.dnLev b) (hP.upLev b) (hP.thmBop b) (hP.partsE b)
  have lifts := fun b => CxData.cutLifts X (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) cv b (hW b) hP.h4pos (hP.kForm b)
    (hP.isoL b) (hP.crdZL b) (hP.lift_coordinates_in_good_part b) (hP.ratLevL b) (hP.dnLevL b) (hP.upLevL b) (hP.thmAop b) (hP.partsW b)
  have types := cutTypes A X P0 ψ0 P1 ψ1 Dc Sp Zsc s C0 C1 hP.ok hP.sep hst hP.eig0 hP.eig1 hP.typ0 hP.typ1
  exact
    { stable := hst
      inBlock := hP.inBlock
      ratZ := hP.ratZ
      pos := hP.pos
      proviso := cutProviso A X P0 ψ0 P1 ψ1 Dc Sp Zsc s C0 C1 hP.ok hP.heckeL hP.eig0 hP.eig1
      types := types
      partsOrth := cutPartsOrth A X P0 ψ0 P1 ψ1 Dc Sp Zsc s hP.ok hP.heckeR hst
      h0 := hP.h0
      h2 := fun b => (what₂ b).1
      ratMu := hP.ratMu
      h3 := hP.h3
      h4pos := hP.h4pos
      h4 := fun b => (what₂ b).2
      kForm := hP.kForm
      mLat := hP.mLat
      ewNorm := hP.ewNorm
      h5 := fun b => (lifts b).1
      ratTh := hP.ratTh
      h3W := hP.h3W
      thmA := fun b => (lifts b).2
      galD := hP.galD
      l1d := fun b => CxData.cutDims X (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b (hW b) hP.h4pos (hP.kForm b) (hP.ewNorm b)
        (types b) (what₂ b).1 (hP.ratMu b) (hP.h3 b) (lifts b).1 (hP.ratTh b) (hP.h3W b) (hP.partsE b) (hP.partsW b)
        (hP.dimParts b)
      l3 := hP.l3
      on := hP.on
      l6 := hP.l6
      l1b := CxData.cutPairing X (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) ζ sEE (hW true) (what₂ true).1 hP.btVanish hP.mi0 hP.zetaOK
      l1e := hP.l1e
      untw := CxData.cutTuples2 X (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) C CH hP.h0 hP.w1
      passage := hP.passage
      fun0 := hP.fun0 }

def cxPkgPrims (hP : CxPrims A P0 ψ0 P1 ψ1 Dc Sp Zsc X cv s C0 C1 ζ sEE C CH) :
    IndefPkg A.fam.amb (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) C CH :=
  cxPkgF A hP.ok hP.sep P0 ψ0 P1 ψ1 Dc Sp Zsc X _ C CH (links_of_prims hP)

end All

end Formalism.IndefR.Cx
