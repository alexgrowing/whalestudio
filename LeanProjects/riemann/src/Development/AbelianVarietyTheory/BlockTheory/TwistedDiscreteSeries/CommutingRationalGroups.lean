import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalToGlobal.IndefiniteReal.FWExist

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult NumberField

namespace GlobalTheory.IndefiniteRowSideFullHecke.CommutingRationalGroups

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

abbrev levV (i : Fin D.R.m) (t : T) : Bridge.LevDat D (Vc D i) := levEnv (Vc D i) (R.βV i) (R.datVt i t)

def IsLiftV (i : Fin D.R.m) (t : T) (g : G) (κ : (levV R i t).Q) : Prop :=
  rTup (R.βV i) (R.datVt i t) (Formalism.UG.bc (swapAE D) ((κ : Bridge.Gf (Vc D i)) : GL _ _)) = R.eG g

def IsLiftW (i : Fin D.R.m) (g : G) (κ : GA D (Wc D i)) : Prop :=
  IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) κ

def IsAlgV (i : Fin D.R.m) (t : T) (c : G → ℂ) (κ : G → (levV R i t).Q) (x y : (R.HV i t).H) : Prop :=
  (R.HV i t).e y = ∑ g, c g • Bridge.g0Act (levV R i t).ch (κ g) ((R.HV i t).e x)

def algW (i : Fin D.R.m) (c : G → ℂ) : MMap (R.MW i (sg0 D A)) →ₗ[ℂ] MMap (R.MW i (sg0 D A)) :=
  postOn _ (gaL (Wc D i) (R.βW i) (R.datWp i R.triv) R.eG c)

theorem algW_eC (i : Fin D.R.m) :
    algW R i (RealDat.eC (A := A) (sg0 D A)) = postOn _ (R.eWf i (sg0 D A)) := rfl

structure Commutes (i : Fin D.R.m) (t : T) : Prop where

  liftV : ∀ g, ∃ κ, IsLiftV R i t g κ

  liftW : ∀ g, ∃ κ, IsLiftW R i g κ

  act : ∀ g κ, IsLiftV R i t g κ → ∀ x : (R.HV i t).H,
    ∃ y : (R.HV i t).H, (R.HV i t).e y = Bridge.g0Act (levV R i t).ch κ ((R.HV i t).e x)

  grp : ∀ g κ, IsLiftV R i t g κ → ∀ x y : (R.HV i t).H,
    (R.HV i t).e y = Bridge.g0Act (levV R i t).ch κ ((R.HV i t).e x) →
      R.thF i t y = FWT.actW R i (sg0 D A) g (R.thF i t x)

  grpAt : ∀ g κ κ', IsLiftV R i t g κ → IsLiftW R i g κ' → ∀ x y : (R.HV i t).H,
    (R.HV i t).e y = Bridge.g0Act (levV R i t).ch κ ((R.HV i t).e x) →
      ∀ v h, R.thF i t y v h = R.thF i t x v (h * κ')

  alg : ∀ (c : G → ℂ) (κ : G → (levV R i t).Q), (∀ g, IsLiftV R i t g (κ g)) → ∀ x y : (R.HV i t).H,
    IsAlgV R i t c κ x y → R.thF i t y = algW R i c (R.thF i t x)

  good : ∀ κ : G → (levV R i t).Q, (∀ g, IsLiftV R i t g (κ g)) → ∀ x y : (R.HV i t).H,
    IsAlgV R i t (RealDat.eC (A := A) (sg0 D A)) κ x y → R.thF i t y = postOn _ (R.eWf i (sg0 D A)) (R.thF i t x)

  goodG : ∀ κ : G → (levV R i t).Q, (∀ g, IsLiftV R i t g (κ g)) → ∀ x y : (R.HV i t).H,
    IsAlgV R i t (RealDat.eC (A := A) (sg0 D A)) κ x y → R.thG i t y = R.thG i t x

  ratGrp : ∀ (g : G) (f : (A.MtCSD i t).Forms),
    R.thF i t (R.jV i t (A.leftGroupActionLift i t g f)) = FWT.actW R i (sg0 D A) g (R.thF i t (R.jV i t f))

  ratGood : ∀ f : (A.MtCSD i t).Forms,
    R.thF i t (R.jV i t ((A.MtCSD i t).gaOp (A.leftGroupActionLift i t) (idemOf A.X) f)) =
      postOn _ (R.eWf i (sg0 D A)) (R.thF i t (R.jV i t f))

  ratGoodG : ∀ f : (A.MtCSD i t).Forms,
    R.thG i t (R.jV i t ((A.MtCSD i t).gaOp (A.leftGroupActionLift i t) (idemOf A.X) f)) = R.thG i t (R.jV i t f)

def ThetaCommutes (F : Face D A) : Prop :=
  R.Char F → ∀ (i : Fin D.R.m) (t : T), Commutes R i t

end GlobalTheory.IndefiniteRowSideFullHecke.CommutingRationalGroups

end
