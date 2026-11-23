import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FaceOf3
import Formalism.LocalToGlobal.IndefiniteReal.CxCoreRG
import Formalism.LocalToGlobal.IndefiniteReal.LiftCoordinatesInGoodPartOfDefinite
import Formalism.LocalToGlobal.IndefiniteReal.EigSumLeComapSemi
import Formalism.LocalToGlobal.IndefiniteReal.CxHecke
import Formalism.LocalToGlobal.IndefiniteReal.IsometricPeriodsOfHypotheses
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RatZOfTests
import Formalism.LocalToGlobal.IndefiniteReal.IsometricPeriodsOfUnitHypotheses

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Col

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}

section Prims3

variable (A3 : FamIn3 K G Pl0 I0 Ty T m)

def cvOf3 (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ) : CrdV A3.fam3.amb3 where
  v0R _ b t := match b with
    | false => BlockGood.goodR (A3.A.fam.R t) (A3.A.fam.lvl P0 ψ0)
    | true => BlockGood.goodR (A3.A.fam.R t) (A3.A.fam.lvl P1 ψ1)
  v0L _ b j t := match b with
    | false => BlockGood.goodR (A3.A.fam.L j t) (A3.A.fam.lvlA P0 ψ0)
    | true => BlockGood.goodR (A3.A.fam.L j t) (A3.A.fam.lvlA P1 ψ1)
  hR t := CSDForm.csumForm (A3.A.fam.R t).S
  hL j t := CSDForm.csumForm (A3.A.fam.L j t).S

variable (X : CxData A3.fam3.amb3)

structure HeckeIntertwiningDefinite (hE : ∀ t, (A3.rowI t).OpIx → Module.End ℂ X.EE) : Prop where

  intw : ∀ t i (u : X.FC t), X.Θ t (X.opC t (Sum.inl i) u) = hE t i (X.Θ t u)

  comm : PairComm (hE A3.A.fam.μ0)

  parts : ∀ p : A3.fam3.base3.Ix,
    X.EEp p = eigSum (hE A3.A.fam.μ0) (cxSys A3.fam3.base3.v0.embedding ((A3.rowI A3.A.fam.μ0).HasRes3 p.1))

structure HeckeIntertwiningLifts (hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (X.W j)) : Prop where

  intw : ∀ j t i (u : X.FLC j t), X.θ' j t (X.opLC j t (Sum.inl i) u) = hW j t i (X.θ' j t u)

  comm : ∀ j, PairComm (hW j A3.A.fam.μ0)

  parts : ∀ (j : Fin m) (p : A3.fam3.base3.Ix),
    X.Wp j p = eigSum (hW j A3.A.fam.μ0)
      (cxSys A3.fam3.base3.v0.embedding ((A3.liftI j A3.A.fam.μ0).HasRes3 (A3.fam3.tr3 j p.1)))

def GEquiv3 (gE : Representation ℂ G X.EE) : Prop :=
  ∀ t (g : G) (x : A3.fam3.amb3.FR t), X.Θ t (X.jR t (A3.fam3.amb3.opR t (Sum.inr g) x)) = gE g (X.Θ t (X.jR t x))

def LiftGroupEquivariance (gW : ∀ j, Representation ℂ G (X.W j)) : Prop :=
  ∀ j t (g : G) (x : A3.fam3.amb3.FL j t),
    X.θ' j t (X.jL j t (A3.fam3.amb3.opL j t (Sum.inr g) x)) = gW j g (X.θ' j t (X.jL j t x))

def typeSp3 (gE : Representation ℂ G X.EE) (P : Subgroup G) (ψ : P →* Kˣ) : Submodule ℂ X.EE :=
  ⨅ h : P, LinearMap.ker (gE (h : G) - (A3.A.fam.v0.embedding ((ψ h : Kˣ) : K)) • LinearMap.id)

def typeSubspace (j : Fin m) (gW : Representation ℂ G (X.W j)) (P : Subgroup G) (ψ : P →* Kˣ) : Submodule ℂ (X.W j) :=
  ⨅ h : P, LinearMap.ker (gW (h : G) - (A3.A.fam.v0.embedding ((ψ h : Kˣ) : K)) • LinearMap.id)

def LiftsEig3 (P : Subgroup G) (ψ : P →* Kˣ) (C : ∀ j : Fin m, ((A3.liftI j A3.A.fam.μ0).OpIx → K) → Prop) : Prop :=
  ∀ j, (A3.A.fam.L j A3.A.fam.μ0).Z0 (A3.A.fam.lvlA P ψ) (X.Zl j A3.A.fam.μ0) =
    (A3.A.fam.L j A3.A.fam.μ0).inV0 (A3.A.fam.lvlA P ψ) (eigSum (A3.liftI j A3.A.fam.μ0).opAll (C j))

variable {A3} in

def LiftsTyp3 (A3 : FamIn3 K G Pl0 I0 Ty T m) (C : ∀ j : Fin m, ((A3.liftI j A3.A.fam.μ0).OpIx → K) → Prop) : Prop :=
  ∀ j x, C j x → A3.fam3.IsType3 (A3.fam3.LI j A3.A.fam.μ0) (A3.fam3.tr3 j) x

variable {P1 : Subgroup G} {ψ1 : P1 →* Kˣ} {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)}
  {Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)} {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3}

def EEg3 : Submodule ℂ X.EE := LinearMap.range (X.iC (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false A3.A.fam.μ0)

def PrincipalLevelBijectivity : Prop :=
  Function.Injective (X.iC (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false A3.A.fam.μ0) ∧
    ∀ t, Function.Injective (X.iC (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false t) ∧
      LinearMap.range (X.iC (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false t) =
        LinearMap.range (X.iC (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false A3.A.fam.μ0)

def LevType3 (gE : Representation ℂ G X.EE) (b : Bool) (P : Subgroup G) (ψ : P →* Kˣ) : Prop :=
  X.EEl b = EEg3 A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) ⊓ typeSp3 A3 X gE P ψ

def principalFormsSubspace (j : Fin m) : Submodule ℂ (X.W j) :=
  ⨆ t, LinearMap.range (X.tC (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false j t)

def LevelTypeOfLifts (gW : ∀ j, Representation ℂ G (X.W j)) (b : Bool) (P : Subgroup G) (ψ : P →* Kˣ) : Prop :=
  ∀ j, LinearMap.range (X.w0C b j) =
    principalFormsSubspace A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) j ⊓ typeSubspace A3 X j (gW j) P ψ⁻¹

end Prims3

structure ComplexDataConditionsExceptBaseDecomposition (A3 : FamIn3 K G Pl0 I0 Ty T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (X : CxData A3.fam3.amb3) (s : ℕ)
    (hE : ∀ t, (A3.rowI t).OpIx → Module.End ℂ X.EE)
    (hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (X.W j)) (gE : Representation ℂ G X.EE)
    (gW : ∀ j, Representation ℂ G (X.W j)) : Prop where

  kFormR : X.KFormR

  kFormL : X.KFormL

  jIsoR : X.JIsoR (cvOf3 A3 P0 ψ0 P1 ψ1)

  jIsoL : X.JIsoL (cvOf3 A3 P0 ψ0 P1 ψ1)

  npTie : X.nP false = (Nat.card P0 : ℝ) ∧ X.nP true = (Nat.card P1 : ℝ)

  ok : A3.fam3.Ok3 s

  sep : A3.fam3.TypesSep3

  heckeR : ∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint

  heckeL : ∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint

  thetaR : HeckeIntertwiningDefinite A3 X hE

  thetaL : HeckeIntertwiningLifts A3 X hW

  gUnit : ∀ (g : G) (x y : X.EE), ⟪gE g x, gE g y⟫_ℂ = ⟪x, y⟫_ℂ

  gEquiv : GEquiv3 A3 X gE

  lev0 : LevType3 A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gE false P0 ψ0

  lev1 : LevType3 A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gE true P1 ψ1

  h2P : PrincipalLevelBijectivity A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc)

  gUnitL : ∀ j (g : G) (x y : X.W j), ⟪gW j g x, gW j g y⟫_ℂ = ⟪x, y⟫_ℂ

  gEquivL : LiftGroupEquivariance A3 X gW

  lower_level_lift_type : LevelTypeOfLifts A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gW false P0 ψ0

  inBlock : X.zs.InBlock

  rowTest : Formalism.IndefR.Rat.RowTest X

  liftTest : Formalism.IndefR.Rat.LiftTest X

  pos : ∀ b, (lv (faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs) b).Pos

  h0 : X.H0

  h4pos : X.H4pos

  thmBop : ∀ b, X.ThmBop b

  partsE : ∀ b, X.PartsE b

  kForm : X.KForm false

  mLat : X.MLat false

  ewNorm : X.EWnorm false

  thmAop : X.ThmAop false

  partsW : X.PartsW false

  base_lift_test : Formalism.IndefR.Rat.LiftTestB X false

  galD : X.GalD (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false

  dimParts : X.DimParts false

structure ComplexDataConditionsBaseLevel (A3 : FamIn3 K G Pl0 I0 Ty T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (X : CxData A3.fam3.amb3) (s : ℕ)
    (C0 : ∀ j : Fin m, ((A3.liftI j A3.A.fam.μ0).OpIx → K) → Prop)
    (hE : ∀ t, (A3.rowI t).OpIx → Module.End ℂ X.EE)
    (hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (X.W j)) (gE : Representation ℂ G X.EE)
    (gW : ∀ j, Representation ℂ G (X.W j)) : Prop
    extends ComplexDataConditionsExceptBaseDecomposition A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s hE hW gE gW where

  eig0 : LiftsEig3 A3 X P0 ψ0 C0

  typ0 : LiftsTyp3 A3 C0

structure PrimitiveStatementsBaseLiftsOnly (A3 : FamIn3 K G Pl0 I0 Ty T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (X : CxData A3.fam3.amb3) (s : ℕ)
    (C0 : ∀ j : Fin m, ((A3.liftI j A3.A.fam.μ0).OpIx → K) → Prop)
    (eV : ∀ t, (Fin ((faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Df1.nV t) → K) →ₗ[K] A3.fam3.amb3.FR t)
    (sEE : X.EE →ₗ⋆[ℂ] (faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Sp.HH)
    (C CH : ℝ)
    (hE : ∀ t, (A3.rowI t).OpIx → Module.End ℂ X.EE)
    (hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (X.W j)) (gE : Representation ℂ G X.EE)
    (gW : ∀ j, Representation ℂ G (X.W j)) (cf : ConvFace A3.fam3.base3) : Prop
    extends ComplexDataConditionsBaseLevel A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 hE hW gE gW where

  w1 : ∀ w, X.W1 (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) ((faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH) w → w ∈ X.Tw

  l3 : (X.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false).L3 ((faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)

  on : (X.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false).ON ((faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)

  l6 : (X.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) true).L6 ((faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)

  evTie : X.EVTie (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) (cvOf3 A3 P0 ψ0 P1 ψ1) eV

  seeIso : X.SEEIso sEE

  miStar : X.MIstar2 eV sEE

  conv : IndefConv A3.fam3.base3 X.μ cf

  heckeRB : Nonempty (X.HeckeRowsC (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false cf)

  heckeWB : Nonempty (X.HeckeWC false cf)

  heckeRC : Nonempty (X.HeckeRowsC (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) true cf)

  fun0 : (X.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false).FUN ((faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)

structure PrimitiveStatementsWithPassage (A3 : FamIn3 K G Pl0 I0 Ty T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (X : CxData A3.fam3.amb3) (s : ℕ)
    (C0 : ∀ j : Fin m, ((A3.liftI j A3.A.fam.μ0).OpIx → K) → Prop)
    (eV : ∀ t, (Fin ((faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Df1.nV t) → K) →ₗ[K] A3.fam3.amb3.FR t)
    (sEE : X.EE →ₗ⋆[ℂ] (faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Sp.HH)
    (C CH : ℝ)
    (hE : ∀ t, (A3.rowI t).OpIx → Module.End ℂ X.EE)
    (hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (X.W j)) (gE : Representation ℂ G X.EE)
    (gW : ∀ j, Representation ℂ G (X.W j)) (cf : ConvFace A3.fam3.base3) : Prop
    extends PrimitiveStatementsBaseLiftsOnly A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 eV sEE C CH hE hW gE gW cf where

  passage : Passage ((faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)
    (X.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false) (X.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) true)

def PackageFromComplexDataConditions : Prop :=
  ∀ (A3 : FamIn3 K G Pl0 I0 Ty T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (X : CxData A3.fam3.amb3) (s : ℕ)
    (C0 : ∀ j : Fin m, ((A3.liftI j A3.A.fam.μ0).OpIx → K) → Prop)
    (eV : ∀ t, (Fin ((faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Df1.nV t) → K) →ₗ[K] A3.fam3.amb3.FR t)
    (sEE : X.EE →ₗ⋆[ℂ] (faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Sp.HH) (C CH : ℝ)
    (hE : ∀ t, (A3.rowI t).OpIx → Module.End ℂ X.EE) (hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (X.W j))
    (gE : Representation ℂ G X.EE) (gW : ∀ j, Representation ℂ G (X.W j)) (cf : ConvFace A3.fam3.base3),
    PrimitiveStatementsWithPassage A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 eV sEE C CH hE hW gE gW cf →
      Nonempty (IndefPkgR A3.fam3.amb3 (faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) cf C CH)

end Formalism.IndefR.Cx
