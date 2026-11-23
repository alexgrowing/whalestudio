import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsAbsIrrCharCompIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
  (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px)

def face0 : Face3 X.toD7 (famR X I hX U Xg tr) where
  P0 := lev0 I
  ψ0 := chr0 I
  P1 := lev1 I
  ψ1 := chr1 I
  Dc _ := ⟨PEmpty, fun u => u.elim, fun u => u.elim, fun u => u.elim⟩
  Sp _ := ⟨ℂ, inferInstance, inferInstance, fun u => u.elim, ⊥⟩
  Zsc _ := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

open Classical in

def MuOf (T : Top.TwDat X.B) (Wt : Set X.B.places.Pl) {U : Set I.ι} (mu : HeightOneSpectrum (𝓞 X.toD7.what₂.LL) → TupU I U)
    (twPl : Finset (HeightOneSpectrum (𝓞 X.toD7.what₂.LL))) : Prop :=
  ∀ w : X.B.places.Pl, (X.toD7.plEq w ∈ twPl ↔ w ∈ Wt) ∧
    I.xi (ixOf I U (mu (X.toD7.plEq w))) = if w ∈ Wt then T.xiTw I.C w else 1

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure Dat (T : Top.TwDat X.B) (Wt : Set X.B.places.Pl) : Type 1 where
  Xg : Finset (Gc X.B px → X.B.LL)
  tr : TrI X.B px
  core : Formalism.L2.Pj.CoreJ X.toD7
  [alg : Algebra core.Q.c.F X.toD7.what₂.LL]
  alg_eq : ∀ y : core.Q.c.F, X.B.embLL (algebraMap core.Q.c.F X.toD7.what₂.LL y) = (y : ℂ)
  R : RealDat3 X.toD7 (famR X I hX (usedOf I T Wt) Xg tr) core.Q.c.F
  cG : G0 R.Pg X.toD7.R.r ≃* G0g X.toD7.nd
  geo : GlobalTheory.RealGeo.GeoHalf core R.toRealDat fun _ => 1
  pins : Pins R (face0 X I hX (usedOf I T Wt) Xg tr) cG
  lev : LevOf X I (usedOf I T Wt) R.toLevCh
  idG : IsPlacewiseIdentity X (px := px) R.eG
  good : GoodSet X (px := px) (R.eG.trans cG) Xg
  mu : MuOf X I T Wt R.mu R.twPl
  fieldValues_mem_fixedField : ∀ y : core.Q.c.F, algebraMap core.Q.c.F X.toD7.what₂.LL y ∈ X.B.LL0
  Ks_le : ∀ x ∈ X.B.Ks, ∃ y : core.Q.c.F, algebraMap core.Q.c.F X.toD7.what₂.LL y = x

attribute [instance] Dat.alg

variable {X I hX} in

abbrev Dat.F {T : Top.TwDat X.B} {Wt : Set X.B.places.Pl} (z : Dat X I hX T Wt) : Face3 X.toD7 (famR X I hX (usedOf I T Wt) z.Xg z.tr) :=
  face0 X I hX (usedOf I T Wt) z.Xg z.tr

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure RowsAre (T : Top.TwDat X.B) (Wt : Set X.B.places.Pl) (ix : X.C.Tup ≃ I.ι) (p0 : BaseLevelRowSide X.toD7) : Type 1 where
  z : Dat X I hX T Wt
  intersectionNumber_baseChange : Holds z.R z.F
  Y : Read z.R.toRealDat z.F.lv2 p0
  Z : ReadL z.R z.F p0 Y
  tup_ix : ∀ t, ix (Y.tup t) = ixOf I (usedOf I T Wt) t

variable {X I hX} in

def Dat.W1 {T : Top.TwDat X.B} {Wt : Set X.B.places.Pl} (z : Dat X I hX T Wt)
    (F0 : HeightOneSpectrum (𝓞 X.toD7.what₂.LL) → Fin X.toD7.R.m → ℝ) : Set X.B.places.Pl :=
  {w | ∃ j, ∃ w' ∈ ({X.toD7.plEq w, Formalism.DivisionValues.conjPl (X.toD7.plEq w)} : Set (HeightOneSpectrum (𝓞 X.toD7.what₂.LL))),
    (s0Of z.R z.F).Iw j (famR X I hX (usedOf I T Wt) z.Xg z.tr).A.μ0 w' ≠ 0 ∨
    Formalism.DivisionValues.jw (((famR X I hX (usedOf I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).HT j
              (famR X I hX (usedOf I T Wt) z.Xg z.tr).A.μ0) w'
      (((famR X I hX (usedOf I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).Tl j
        (famR X I hX (usedOf I T Wt) z.Xg z.tr).A.μ0) ≠ 0 ∨ F0 w' j ≠ 0}

end GlobalTheory.Mem.R3

end
